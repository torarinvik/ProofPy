(** Type checker for CertiJSON.
    
    This module implements the typing rules from the specification. *)

open Syntax
open Context

(** {1 Typing Errors} *)

type typing_error =
  | UnboundVariable of name
  | TypeMismatch of { expected : term; actual : term; context : string }
  | NotAFunction of term
  | NotAType of term
  | NotAProp of term
  | InvalidApplication of term * term
  | NonExhaustiveMatch of name list  (* Missing constructors *)
  | InvalidPattern of string
  | TerminationCheckFailed of name
  | PositivityCheckFailed of name * name  (* inductive, problematic param/ctor arg *)
  | RecArgNotInductive of name * int      (* def name, param index *)
  | InvalidRecursiveArg of name * int
  | UnknownConstructor of name
  | UnknownInductive of name
  | RoleMismatch of name * role * role  (* name, expected, actual *)
  | InDeclaration of name * Loc.t option * typing_error
[@@deriving show]

exception TypeError of typing_error

(** {1 Utilities} *)

module StringSet = Set.Make (String)

(** {1 Universe Checking} *)

(** Check if a term is a universe. *)
let is_universe (t : term) : bool =
  match t with
  | Universe _ -> true
  | _ -> false

(** Get the universe level of a type. *)
let rec infer_universe (ctx : context) (t : term) : universe option =
  match t with
  | Universe u -> Some u
  | PrimType _ -> Some Type
  | Pi { arg; result } ->
      let _ = infer_universe ctx arg.ty in
      let ctx' = extend ctx arg.name arg.ty in
      infer_universe ctx' result
  | _ -> None

(** {1 Definitional Equality} *)

(** Weak head normal form reduction. *)
let rec whnf (ctx : context) (t : term) : term =
  match t with
  | App (f, args) -> (
      let f' = whnf ctx f in
      match f' with
      | Lambda { arg; body } when args <> [] ->
          let arg_val = List.hd args in
          let body' = subst arg.name arg_val body in
          let remaining = List.tl args in
          if remaining = [] then whnf ctx body'
          else whnf ctx (App (body', remaining))
      | _ -> App (f', args))
  | Global name -> (
      match lookup ctx name with
      | Some (`Global (GDefinition def)) when def.def_role <> ProofOnly ->
          whnf ctx def.def_body
      | _ -> t)
  | Match { scrutinee; cases; _ } -> (
      let scrut' = whnf ctx scrutinee in
      match scrut' with
      | App (Global ctor_name, ctor_args) -> (
          match
            List.find_opt (fun c -> String.equal c.pattern.ctor ctor_name) cases
          with
          | Some case ->
              let bindings =
                List.combine (List.map (fun a -> a.arg_name) case.pattern.args) ctor_args
              in
              let body =
                List.fold_left
                  (fun acc (x, v) -> subst x v acc)
                  case.body bindings
              in
              whnf ctx body
          | None -> Match { scrutinee = scrut'; motive = t; as_name = None; cases; coverage_hint = Unknown })
      | Global ctor_name -> (
          match
            List.find_opt (fun c -> String.equal c.pattern.ctor ctor_name) cases
          with
          | Some case when case.pattern.args = [] -> whnf ctx case.body
          | _ -> t)
      | _ -> t)
  | Rewrite { body; _ } -> whnf ctx body  (* rewrite is computationally identity *)
  | _ -> t

(** Check definitional equality of two terms. *)
let rec conv (ctx : context) (t1 : term) (t2 : term) : bool =
  let t1' = whnf ctx t1 in
  let t2' = whnf ctx t2 in
  conv_whnf ctx t1' t2'

and conv_whnf (ctx : context) (t1 : term) (t2 : term) : bool =
  match (t1, t2) with
  | Var x, Var y -> String.equal x y
  | Universe u1, Universe u2 -> equal_universe u1 u2
  | PrimType p1, PrimType p2 -> equal_prim_type p1 p2
  | Literal l1, Literal l2 -> equal_literal l1 l2
  | Global n1, Global n2 -> String.equal n1 n2
  | Pi { arg = a1; result = r1 }, Pi { arg = a2; result = r2 } ->
      conv ctx a1.ty a2.ty &&
      let ctx' = extend ctx a1.name a1.ty in
      conv ctx' r1 (subst a2.name (Var a1.name) r2)
  | Lambda { arg = a1; body = b1 }, Lambda { arg = a2; body = b2 } ->
      conv ctx a1.ty a2.ty &&
      let ctx' = extend ctx a1.name a1.ty in
      conv ctx' b1 (subst a2.name (Var a1.name) b2)
  | App (f1, args1), App (f2, args2) ->
      conv ctx f1 f2 &&
      List.length args1 = List.length args2 &&
      List.for_all2 (conv ctx) args1 args2
  | Eq { ty = t1; lhs = l1; rhs = r1 }, Eq { ty = t2; lhs = l2; rhs = r2 } ->
      conv ctx t1 t2 && conv ctx l1 l2 && conv ctx r1 r2
  | Refl { ty = t1; value = v1 }, Refl { ty = t2; value = v2 } ->
      conv ctx t1 t2 && conv ctx v1 v2
  | _ -> false

(** Substitute a list of (name, term) pairs into a term. *)
let subst_many (substs : (name * term) list) (t : term) : term =
  List.fold_left (fun acc (x, s) -> subst x s acc) t substs

(** Collect leading Π binders from a type. *)
let rec collect_pi_binders (t : term) : binder list * term =
  match t with
  | Pi { arg; result } ->
      let bs, res = collect_pi_binders result in
      (arg :: bs, res)
  | _ -> ([], t)

(** Collect leading lambda binders from a term. *)
let rec collect_lambda_binders (t : term) : binder list * term =
  match t with
  | Lambda { arg; body } ->
      let bs, core = collect_lambda_binders body in
      (arg :: bs, core)
  | _ -> ([], t)

let rec take_n n xs =
  match (n, xs) with
  | 0, _ -> []
  | _, [] -> []
  | n, x :: tl -> x :: take_n (n - 1) tl

(** Pretty printing of typing errors. *)
let string_of_role = function
  | Runtime -> "runtime"
  | ProofOnly -> "proof-only"
  | Both -> "both"

let rec string_of_typing_error (err : typing_error) : string =
  let pp_term = Pretty.term_to_string in
  match err with
  | UnboundVariable x -> Format.sprintf "Unbound variable %s" x
  | TypeMismatch { expected; actual; context } ->
      Format.sprintf "Type mismatch in %s: expected %s but got %s"
        context (pp_term expected) (pp_term actual)
  | NotAFunction t -> Format.sprintf "Cannot apply non-function term: %s" (pp_term t)
  | NotAType t -> Format.sprintf "Expected a type, but got %s" (pp_term t)
  | NotAProp t -> Format.sprintf "Expected a proposition, but got %s" (pp_term t)
  | InvalidApplication (f, arg) ->
      Format.sprintf "Invalid application: %s applied to %s" (pp_term f) (pp_term arg)
  | NonExhaustiveMatch ctors ->
      Format.sprintf "Non-exhaustive match; missing cases for: %s"
        (String.concat ", " ctors)
  | InvalidPattern msg -> Format.sprintf "Invalid pattern: %s" msg
  | TerminationCheckFailed name ->
      Format.sprintf "Termination check failed for %s: recursive call not structurally decreasing" name
  | PositivityCheckFailed (ind, arg_name) ->
      Format.sprintf "Strict positivity violated in %s: constructor argument %s is negative"
        ind arg_name
  | RecArgNotInductive (name, idx) ->
      Format.sprintf "rec_args index %d for %s is not an inductive argument" idx name
  | InvalidRecursiveArg (name, idx) ->
      Format.sprintf "Invalid rec_args index %d for %s" idx name
  | UnknownConstructor c -> Format.sprintf "Unknown constructor %s" c
  | UnknownInductive i -> Format.sprintf "Unknown inductive type %s" i
  | RoleMismatch (name, expected, actual) ->
      Format.sprintf "Role mismatch for %s: expected %s but found %s"
        name (string_of_role expected) (string_of_role actual)
  | InDeclaration (name, _loc, err) ->
      Format.sprintf "While checking %s: %s" name (string_of_typing_error err)

(** Positivity checking: ensure inductive appears only in strictly positive positions. *)
let rec positive_occurrences (target : name) (positive : bool) (t : term) : bool =
  let go = positive_occurrences target in
  match t with
  | Var x | Global x ->
      if String.equal x target then positive else true
  | Universe _ | PrimType _ | Literal _ -> true
  | Pi { arg; result } ->
      (* Domain flips polarity; codomain keeps current polarity. *)
      go (not positive) arg.ty && go positive result
  | Lambda { arg; body } ->
      go positive arg.ty && go positive body
  | App (f, args) ->
      go positive f && List.for_all (go positive) args
  | Eq { ty; lhs; rhs } ->
      go positive ty && go positive lhs && go positive rhs
  | Refl { ty; value } ->
      go positive ty && go positive value
  | Rewrite { proof; body } ->
      go positive proof && go positive body
  | Match { scrutinee; motive; cases; _ } ->
      go positive scrutinee
      && go positive motive
      && List.for_all (fun c -> go positive c.body) cases

(** {1 Type Inference} *)

(** Infer the type of a term. *)
let rec infer (ctx : context) (t : term) : term =
  match t with
  | Var x -> (
      match lookup ctx x with
      | Some (`Local ty) -> ty
      | Some (`Global (GDefinition def)) -> def.def_type
      | Some (`Global (GTheorem thm)) -> thm.thm_type
      | Some (`Global (GInductive ind)) -> inductive_type ind
      | Some (`Global (GConstructor { parent; ctor; _ })) -> (
          match lookup ctx parent with
          | Some (`Global (GInductive ind)) -> constructor_type ind ctor
          | _ -> raise (TypeError (UnknownInductive parent)))
      | Some (`Global (GExternC ext)) -> ext.logical_type
      | Some (`Global (GRepr _)) ->
          raise (TypeError (TypeMismatch { expected = Universe Type; actual = t; context = "repr is not a term" }))
      | None -> raise (TypeError (UnboundVariable x)))
  | Universe Type -> Universe Type  (* Type : Type - impredicative for simplicity *)
  | Universe Prop -> Universe Type  (* Prop : Type *)
  | PrimType _ -> Universe Type
  | Literal (LitInt32 _) -> PrimType Int32
  | Literal (LitInt64 _) -> PrimType Int64
  | Literal (LitFloat64 _) -> PrimType Float64
  | Literal (LitBool _) -> PrimType Bool
  | Pi { arg; result } ->
      let _ = check ctx arg.ty (Universe Type) in
      let ctx' = extend ctx arg.name arg.ty in
      let result_ty = infer ctx' result in
      (match result_ty with
      | Universe u -> Universe u
      | _ -> raise (TypeError (NotAType result)))
  | Lambda { arg; body } ->
      let _ = check ctx arg.ty (Universe Type) in
      let ctx' = extend ctx arg.name arg.ty in
      let body_ty = infer ctx' body in
      Pi { arg; result = body_ty }
  | App (f, args) ->
      List.fold_left
        (fun f_ty arg ->
          let f_ty' = whnf ctx f_ty in
          match f_ty' with
          | Pi { arg = param; result } ->
              let _ = check ctx arg param.ty in
              subst param.name arg result
          | _ -> raise (TypeError (NotAFunction f_ty')))
        (infer ctx f) args
  | Eq { ty; lhs; rhs } ->
      let _ = check ctx ty (Universe Type) in
      let _ = check ctx lhs ty in
      let _ = check ctx rhs ty in
      Universe Prop
  | Refl { ty; value } ->
      let _ = check ctx ty (Universe Type) in
      let _ = check ctx value ty in
      Eq { ty; lhs = value; rhs = value }
  | Rewrite { proof; body } ->
      let proof_ty = infer ctx proof in
      let proof_ty' = whnf ctx proof_ty in
      (match proof_ty' with
      | Eq { ty = _; lhs = _; rhs = _ } ->
          (* For now, just return the body's type *)
          (* Full implementation would substitute based on equality *)
          infer ctx body
      | _ -> raise (TypeError (TypeMismatch { expected = Eq { ty = Universe Type; lhs = Var "_"; rhs = Var "_" }; actual = proof_ty'; context = "rewrite proof" })))
  | Match { scrutinee; motive; as_name; cases; coverage_hint = _ } ->
      let scrut_ty = infer ctx scrutinee in
      let scrut_ty_whnf = whnf ctx scrut_ty in
      let head, args =
        match scrut_ty_whnf with
        | App (f, args) -> (f, args)
        | t -> (t, [])
      in
      let ind =
        match head with
        | Var n | Global n -> (
            match lookup ctx n with
            | Some (`Global (GInductive ind)) -> ind
            | _ -> raise (TypeError (UnknownInductive n)))
        | _ -> raise (TypeError (InvalidPattern "scrutinee is not an inductive type"))
      in
      if List.length args <> List.length ind.params then
        raise (TypeError (TypeMismatch { expected = inductive_type ind; actual = scrut_ty; context = "match scrutinee parameters" }));
      (* Instantiate inductive parameters and check their types. *)
      let param_substs =
        let rec build acc params args =
          match (params, args) with
          | [], [] -> acc
          | p :: ps, a :: as_ ->
              let param_ty = subst_many acc p.ty in
              let _ = check ctx a param_ty in
              build ((p.name, a) :: acc) ps as_
          | _ -> acc
        in
        build [] ind.params args
      in
      let motive_ctx =
        match as_name with
        | Some n -> extend ctx n scrut_ty
        | None -> ctx
      in
      let motive_universe =
        match whnf ctx (infer motive_ctx motive) with
        | Universe u -> u
        | other -> raise (TypeError (NotAType other))
      in
      let _ = motive_universe in
      let seen = Hashtbl.create (List.length cases) in
      let find_ctor name =
        match List.find_opt (fun c -> String.equal c.ctor_name name) ind.constructors with
        | Some ctor -> ctor
        | None -> raise (TypeError (UnknownConstructor name))
      in
      List.iter
        (fun case ->
          let ctor = find_ctor case.pattern.ctor in
          if Hashtbl.mem seen ctor.ctor_name then
            raise (TypeError (InvalidPattern ("duplicate case for constructor " ^ ctor.ctor_name)));
          Hashtbl.add seen ctor.ctor_name ();
          if List.length case.pattern.args <> List.length ctor.ctor_args then
            raise (TypeError (InvalidPattern "constructor argument count mismatch"));
          let ctor_arg_tys =
            List.map (fun arg -> subst_many param_substs arg.ty) ctor.ctor_args
          in
          let branch_ctx =
            List.fold_left2
              (fun c pat arg_ty -> extend c pat.arg_name arg_ty)
              ctx case.pattern.args ctor_arg_tys
          in
          let branch_ctx =
            match as_name with
            | Some n -> extend branch_ctx n scrut_ty
            | None -> branch_ctx
          in
          let ctor_term =
            let ctor_args = args @ List.map (fun a -> Var a.arg_name) case.pattern.args in
            if ctor_args = [] then Var ctor.ctor_name else App (Var ctor.ctor_name, ctor_args)
          in
          let expected_branch_ty =
            let with_scrut =
              match as_name with
              | Some n -> subst n ctor_term motive
              | None -> motive
            in
            subst_many param_substs with_scrut
          in
          check branch_ctx case.body expected_branch_ty)
        cases;
      let missing =
        List.filter (fun c -> not (Hashtbl.mem seen c.ctor_name)) ind.constructors
        |> List.map (fun c -> c.ctor_name)
      in
      if missing <> [] then raise (TypeError (NonExhaustiveMatch missing));
      (match as_name with Some n -> subst n scrutinee motive | None -> motive)
  | Global name -> (
      match lookup ctx name with
      | Some (`Global entry) -> (
          match entry with
          | GInductive ind -> inductive_type ind
          | GConstructor { parent; ctor; _ } -> (
              match lookup ctx parent with
              | Some (`Global (GInductive ind)) -> constructor_type ind ctor
              | _ -> raise (TypeError (UnknownInductive parent)))
          | GDefinition def -> def.def_type
          | GTheorem thm -> thm.thm_type
          | GExternC ext -> ext.logical_type
          | GRepr _ -> raise (TypeError (TypeMismatch { expected = Universe Type; actual = t; context = "repr" })))
      | _ -> raise (TypeError (UnboundVariable name)))

(** Check that a term has a given type. *)
and check (ctx : context) (t : term) (expected : term) : unit =
  let actual = infer ctx t in
  if not (conv ctx actual expected) then
    raise (TypeError (TypeMismatch { expected; actual; context = "check" }))

(** {1 Termination Checking} *)

let rec has_self_reference (self : name) (t : term) : bool =
  match t with
  | Var x | Global x -> String.equal x self
  | Universe _ | PrimType _ | Literal _ -> false
  | Pi { arg; result } -> has_self_reference self arg.ty || has_self_reference self result
  | Lambda { arg; body } -> has_self_reference self arg.ty || has_self_reference self body
  | App (f, args) ->
      has_self_reference self f || List.exists (has_self_reference self) args
  | Eq { ty; lhs; rhs } ->
      has_self_reference self ty || has_self_reference self lhs || has_self_reference self rhs
  | Refl { ty; value } ->
      has_self_reference self ty || has_self_reference self value
  | Rewrite { proof; body } ->
      has_self_reference self proof || has_self_reference self body
  | Match { scrutinee; motive; cases; _ } ->
      has_self_reference self scrutinee
      || has_self_reference self motive
      || List.exists (fun c -> has_self_reference self c.body) cases

let check_termination (def : def_decl) : unit =
  let params, _ = collect_pi_binders def.def_type in
  let param_count = List.length params in
  let lam_params, lam_body = collect_lambda_binders def.def_body in
  if List.length lam_params < param_count then
    raise (TypeError (TerminationCheckFailed def.def_name));
  let param_names = take_n param_count (List.map (fun b -> b.name) lam_params) in
  match def.rec_args with
  | None ->
      if has_self_reference def.def_name lam_body then
        raise (TypeError (TerminationCheckFailed def.def_name))
  | Some rec_args ->
      if rec_args = [] then (
        if has_self_reference def.def_name lam_body then
          raise (TypeError (TerminationCheckFailed def.def_name))
      ) else (
      let rec validate_indices = function
        | [] -> ()
        | idx :: rest ->
            if idx < 0 || idx >= param_count then
              raise (TypeError (InvalidRecursiveArg (def.def_name, idx)));
            validate_indices rest
      in
      validate_indices rec_args;
      let rec_param_names =
        List.fold_left
          (fun acc idx ->
            match List.nth_opt param_names idx with
            | Some n -> (idx, n) :: acc
            | None -> acc)
          [] rec_args
      in
      let rec_param_by_name =
        let tbl = Hashtbl.create (List.length rec_param_names) in
        List.iter (fun (i, n) -> Hashtbl.add tbl n i) rec_param_names;
        tbl
      in
      let initial_allowed =
        List.map (fun idx -> (idx, StringSet.empty)) rec_args
      in
      let rec get_allowed allowed idx =
        match allowed with
        | [] -> StringSet.empty
        | (i, set) :: rest -> if i = idx then set else get_allowed rest idx
      in
      let rec update_allowed allowed idx names =
        match allowed with
        | [] ->
            let set =
              List.fold_left (fun acc n -> StringSet.add n acc) StringSet.empty names
            in
            [ (idx, set) ]
        | (i, set) :: rest when i = idx ->
            (i, List.fold_left (fun acc n -> StringSet.add n acc) set names) :: rest
        | entry :: rest -> entry :: update_allowed rest idx names
      in
  let rec_index_of_var allowed v =
    match Hashtbl.find_opt rec_param_by_name v with
    | Some i -> Some i
    | None ->
        List.find_map
          (fun (i, set) -> if StringSet.mem v set then Some i else None)
          allowed
  in
  let rec_param_inductives =
    List.map
      (fun idx ->
        match List.nth_opt params idx with
        | None -> raise (TypeError (InvalidRecursiveArg (def.def_name, idx)))
        | Some b -> (
            match whnf (make_ctx (empty_sig ())) b.ty with
            | Var n | Global n -> Some n
            | _ -> None))
      rec_args
  in
  List.iter2
    (fun idx ind_opt ->
      match ind_opt with
      | None -> raise (TypeError (RecArgNotInductive (def.def_name, idx)))
      | Some _ -> ())
    rec_args rec_param_inductives;
  let rec check_term allowed t =
    match t with
    | Var x | Global x ->
        if String.equal x def.def_name then
          raise (TypeError (TerminationCheckFailed def.def_name))
        | Universe _ | PrimType _ | Literal _ -> ()
        | Pi { arg; result } ->
            check_term allowed arg.ty;
            check_term allowed result
        | Lambda { arg; body } ->
            check_term allowed arg.ty;
            check_term allowed body
        | App (f, args) ->
            let is_self =
              match f with
              | Var x | Global x -> String.equal x def.def_name
              | _ -> false
            in
            if is_self then (
              let required_arity =
                match List.fold_left max 0 rec_args with
                | max_idx -> max_idx + 1
              in
              if List.length args < required_arity then
                raise (TypeError (TerminationCheckFailed def.def_name));
              List.iter
                (fun idx ->
                  match List.nth_opt args idx with
                  | Some (Var v) ->
                      let allowed_set = get_allowed allowed idx in
                      if not (StringSet.mem v allowed_set) then
                        raise (TypeError (TerminationCheckFailed def.def_name))
                  | Some _ -> raise (TypeError (TerminationCheckFailed def.def_name))
                  | None -> raise (TypeError (TerminationCheckFailed def.def_name)))
                rec_args);
            if not is_self then check_term allowed f;
            List.iter (check_term allowed) args
        | Eq { ty; lhs; rhs } ->
            check_term allowed ty;
            check_term allowed lhs;
            check_term allowed rhs
        | Refl { ty; value } ->
            check_term allowed ty;
            check_term allowed value
        | Rewrite { proof; body } ->
            check_term allowed proof;
            check_term allowed body
        | Match { scrutinee; motive; cases; _ } ->
            check_term allowed scrutinee;
            check_term allowed motive;
            let rec_idx =
              match scrutinee with
              | Var v -> rec_index_of_var allowed v
              | _ -> None
            in
            List.iter
              (fun c ->
                let allowed' =
                  match rec_idx with
                  | Some idx ->
                      let idx_is_rec = List.mem idx rec_args in
                      if not idx_is_rec then raise (TypeError (TerminationCheckFailed def.def_name));
                      let names = List.map (fun a -> a.arg_name) c.pattern.args in
                      update_allowed allowed idx names
                  | None -> allowed
                in
                check_term allowed' c.body)
              cases
      in
      check_term initial_allowed lam_body)

(** {1 Declaration Checking} *)

(** Check a single declaration. *)
let check_declaration (ctx : context) (decl : declaration) : unit =
  let with_decl name loc f =
    try f () with
    | TypeError e -> raise (TypeError (InDeclaration (name, loc, e)))
  in
  match decl with
  | Inductive ind ->
      with_decl ind.ind_name ind.ind_loc (fun () ->
        (* Check parameter types *)
        let ctx' =
          List.fold_left
            (fun c p ->
              let _ = check c p.ty (Universe Type) in
              extend c p.name p.ty)
            ctx ind.params
        in
        (* Check constructor types (simplified - full check needs positivity) *)
        List.iter
          (fun ctor ->
            List.iter
              (fun arg -> check ctx' arg.ty (Universe Type))
              ctor.ctor_args)
          ind.constructors;
        (* Strict positivity: inductive must not appear in negative position in args. *)
        List.iter
          (fun ctor ->
            List.iter
              (fun arg ->
                if not (positive_occurrences ind.ind_name true arg.ty) then
                  raise (TypeError (PositivityCheckFailed (ind.ind_name, arg.name))))
              ctor.ctor_args)
          ind.constructors)
  | Definition def ->
      with_decl def.def_name def.def_loc (fun () ->
        let _ = check ctx def.def_type (Universe Type) in
        check ctx def.def_body def.def_type;
        check_termination def)
  | Theorem thm ->
      with_decl thm.thm_name thm.thm_loc (fun () ->
        let _ = check ctx thm.thm_type (Universe Prop) in
        check ctx thm.thm_proof thm.thm_type)
  | Repr _ -> ()  (* Repr declarations are not type-checked in the logical sense *)
  | ExternC ext ->
      with_decl ext.extern_name ext.extern_loc (fun () ->
        let _ = check ctx ext.logical_type (Universe Type) in
        ())

(** Check an entire module. *)
let check_module (mod_ : module_decl) : (signature, typing_error) result =
  try
    let sig_ = build_signature mod_.declarations in
    let ctx = make_ctx sig_ in
    List.iter (check_declaration ctx) mod_.declarations;
    Ok sig_
  with TypeError e -> Error e
