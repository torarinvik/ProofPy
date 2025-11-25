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
  | PositivityCheckFailed of name * name  (* inductive, problematic param *)
  | InvalidRecursiveArg of name * int
  | UnknownConstructor of name
  | UnknownInductive of name
  | RoleMismatch of name * role * role  (* name, expected, actual *)
[@@deriving show]

exception TypeError of typing_error

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

(** {1 Declaration Checking} *)

(** Check a single declaration. *)
let check_declaration (ctx : context) (decl : declaration) : unit =
  match decl with
  | Inductive ind ->
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
        ind.constructors
  | Definition def ->
      let _ = check ctx def.def_type (Universe Type) in
      check ctx def.def_body def.def_type
      (* TODO: termination checking for recursive definitions *)
  | Theorem thm ->
      let _ = check ctx thm.thm_type (Universe Prop) in
      check ctx thm.thm_proof thm.thm_type
  | Repr _ -> ()  (* Repr declarations are not type-checked in the logical sense *)
  | ExternC ext ->
      let _ = check ctx ext.logical_type (Universe Type) in
      ()

(** Check an entire module. *)
let check_module (mod_ : module_decl) : (signature, typing_error) result =
  try
    let sig_ = build_signature mod_.declarations in
    let ctx = make_ctx sig_ in
    List.iter (check_declaration ctx) mod_.declarations;
    Ok sig_
  with TypeError e -> Error e
