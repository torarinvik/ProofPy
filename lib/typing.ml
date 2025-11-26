(** Type checker for CertiJSON.
    
    This module implements the typing rules from the specification. *)

open Syntax
open Context

(** {1 Typing Errors} *)

type typing_error =
  | UnboundVariable of name
  | TypeMismatch of { expected : term; actual : term; context : string; loc : Loc.t option }
  | NotAFunction of term * Loc.t option
  | NotAType of term * Loc.t option
  | NotAProp of term * Loc.t option
  | InvalidApplication of term * term * Loc.t option
  | NonExhaustiveMatch of name list  (* Missing constructors *)
  | InvalidPattern of string
  | TerminationCheckFailed of name
  | PositivityCheckFailed of name * name  (* inductive, problematic param/ctor arg *)
  | RecArgNotInductive of name * int      (* def name, param index *)
  | InvalidRecursiveArg of name * int
  | UnknownConstructor of name
  | UnknownInductive of name
  | RoleMismatch of name * role * role  (* name, expected, actual *)
  | InvalidRepr of name * string
  | InvalidExternC of name * string
  | InvalidExternIO of name * string
  | InDeclaration of name * Loc.t option * typing_error
[@@deriving show]

exception TypeError of typing_error

(** {1 Utilities} *)

module StringSet = Set.Make (String)

(** {1 Universe Checking} *)

(** Check if a term is a universe. *)
let is_universe (t : term) : bool =
  match t.desc with
  | Universe _ -> true
  | _ -> false

(** Get the universe level of a type. *)
let rec infer_universe (ctx : context) (t : term) : universe option =
  match t.desc with
  | Universe u -> Some u
  | PrimType _ -> Some Type
  | Pi { arg; result } ->
      let _ = infer_universe ctx arg.ty in
      let ctx' = extend ctx arg.name arg.ty in
      infer_universe ctx' result
  | Subset { arg; pred = _ } ->
      let _ = infer_universe ctx arg.ty in
      (* Predicate must be Prop, but Subset lives in same universe as arg *)
      infer_universe ctx arg.ty
  | _ -> None

(** {1 Definitional Equality} *)

(** Weak head normal form reduction. *)
let rec whnf (ctx : context) (t : term) : term =
  match t.desc with
  | App (f, args) -> (
      let f' = whnf ctx f in
      match f'.desc with
      | Lambda { arg; body } when args <> [] ->
          let arg_val = List.hd args in
          let body' = subst arg.name arg_val body in
          let remaining = List.tl args in
          if remaining = [] then whnf ctx body'
          else whnf ctx (mk ?loc:t.loc (App (body', remaining)))
      | _ -> mk ?loc:t.loc (App (f', args)))
  | Var name | Global name -> (
      match lookup ctx name with
      | Some (`Global (GDefinition def)) when def.def_role <> ProofOnly ->
          whnf ctx def.def_body
      | _ -> t)
  | SubsetElim tm -> (
      let tm' = whnf ctx tm in
      match tm'.desc with
      | SubsetIntro { value; _ } -> whnf ctx value
      | _ -> mk ?loc:t.loc (SubsetElim tm'))
  | SubsetProof tm -> (
      let tm' = whnf ctx tm in
      match tm'.desc with
      | SubsetIntro { proof; _ } -> whnf ctx proof
      | _ -> mk ?loc:t.loc (SubsetProof tm'))
  | Match { scrutinee; motive; as_name; cases; coverage_hint } -> (
      let scrut' = whnf ctx scrutinee in
      let reconstruct () =
        mk ?loc:t.loc
          (Match { scrutinee = scrut'; motive; as_name; cases; coverage_hint })
      in
      match scrut'.desc with
      | App ({ desc = Global ctor_name | Var ctor_name; _ }, ctor_args) -> (
          match
            List.find_opt (fun c -> String.equal c.pattern.ctor ctor_name) cases
          with
          | Some case ->
              let pat_args = List.map (fun a -> a.arg_name) case.pattern.args in
              let num_pat_args = List.length pat_args in
              let num_ctor_args = List.length ctor_args in
              if num_ctor_args < num_pat_args then
                reconstruct ()
              else
                let field_args =
                  let skip = num_ctor_args - num_pat_args in
                  let rec drop n xs =
                    match n, xs with
                    | 0, _ -> xs
                    | k, _ :: ys -> drop (k - 1) ys
                    | _, [] -> []
                  in
                  drop skip ctor_args
                in
                let bindings = List.combine pat_args field_args in
                let body =
                  List.fold_left
                    (fun acc (x, v) -> subst x v acc)
                    case.body bindings
                in
                whnf ctx body
          | None -> reconstruct ())
      | Global ctor_name | Var ctor_name -> (
          match
            List.find_opt (fun c -> String.equal c.pattern.ctor ctor_name) cases
          with
          | Some case when case.pattern.args = [] -> whnf ctx case.body
          | _ -> reconstruct ())
      | _ -> reconstruct ())
  | Rewrite { body; _ } -> whnf ctx body  (* rewrite is computationally identity *)
  | If { cond; then_; else_ } -> (
      let cond' = whnf ctx cond in
      match cond'.desc with
      | Literal (LitBool true) -> whnf ctx then_
      | Literal (LitBool false) -> whnf ctx else_
      | _ -> mk ?loc:t.loc (If { cond = cond'; then_; else_ }))
  | _ -> t

(** Check structural equality ignoring locations. *)
let rec equal_ignoring_loc (t1 : term) (t2 : term) : bool =
  match (t1.desc, t2.desc) with
  | Var x, Var y -> String.equal x y
  | Universe u1, Universe u2 -> equal_universe u1 u2
  | PrimType p1, PrimType p2 -> equal_prim_type p1 p2
  | Literal l1, Literal l2 -> equal_literal l1 l2
  | Global n1, Global n2 -> String.equal n1 n2
  | Pi { arg = a1; result = r1 }, Pi { arg = a2; result = r2 } ->
      String.equal a1.name a2.name &&
      equal_ignoring_loc a1.ty a2.ty &&
      equal_ignoring_loc r1 r2
  | Lambda { arg = a1; body = b1 }, Lambda { arg = a2; body = b2 } ->
      String.equal a1.name a2.name &&
      equal_ignoring_loc a1.ty a2.ty &&
      equal_ignoring_loc b1 b2
  | App (f1, args1), App (f2, args2) ->
      equal_ignoring_loc f1 f2 &&
      List.length args1 = List.length args2 &&
      List.for_all2 equal_ignoring_loc args1 args2
  | Eq { ty = t1; lhs = l1; rhs = r1 }, Eq { ty = t2; lhs = l2; rhs = r2 } ->
      equal_ignoring_loc t1 t2 && equal_ignoring_loc l1 l2 && equal_ignoring_loc r1 r2
  | Refl { ty = t1; value = v1 }, Refl { ty = t2; value = v2 } ->
      equal_ignoring_loc t1 t2 && equal_ignoring_loc v1 v2
  | Rewrite { proof = p1; body = b1 }, Rewrite { proof = p2; body = b2 } ->
      equal_ignoring_loc p1 p2 && equal_ignoring_loc b1 b2
  | If { cond = c1; then_ = t1; else_ = e1 }, If { cond = c2; then_ = t2; else_ = e2 } ->
      equal_ignoring_loc c1 c2 && equal_ignoring_loc t1 t2 && equal_ignoring_loc e1 e2
  | Match m1, Match m2 ->
      equal_ignoring_loc m1.scrutinee m2.scrutinee &&
      equal_ignoring_loc m1.motive m2.motive &&
      Option.equal String.equal m1.as_name m2.as_name &&
      List.length m1.cases = List.length m2.cases &&
      List.for_all2 (fun c1 c2 ->
        String.equal c1.pattern.ctor c2.pattern.ctor &&
        List.length c1.pattern.args = List.length c2.pattern.args &&
        List.for_all2 (fun a1 a2 -> String.equal a1.arg_name a2.arg_name) c1.pattern.args c2.pattern.args &&
        equal_ignoring_loc c1.body c2.body
      ) m1.cases m2.cases
  | Subset { arg = a1; pred = p1 }, Subset { arg = a2; pred = p2 } ->
      String.equal a1.name a2.name &&
      equal_ignoring_loc a1.ty a2.ty &&
      equal_ignoring_loc p1 p2
  | SubsetIntro { value = v1; proof = p1 }, SubsetIntro { value = v2; proof = p2 } ->
      equal_ignoring_loc v1 v2 && equal_ignoring_loc p1 p2
  | SubsetElim t1, SubsetElim t2 -> equal_ignoring_loc t1 t2
  | SubsetProof t1, SubsetProof t2 -> equal_ignoring_loc t1 t2
  | _ -> false

(** Check definitional equality of two terms. *)
let rec conv (ctx : context) (t1 : term) (t2 : term) : bool =
  if equal_ignoring_loc t1 t2 then true else
  let t1' = whnf ctx t1 in
  let t2' = whnf ctx t2 in
  if equal_ignoring_loc t1' t2' then true else
  conv_whnf ctx t1' t2'

and conv_whnf (ctx : context) (t1 : term) (t2 : term) : bool =
  match (t1.desc, t2.desc) with
  | Var x, Var y -> String.equal x y
  | Universe u1, Universe u2 -> equal_universe u1 u2
  | PrimType p1, PrimType p2 -> equal_prim_type p1 p2
  | Literal l1, Literal l2 -> equal_literal l1 l2
  | Global n1, Global n2 -> String.equal n1 n2
  | Pi { arg = a1; result = r1 }, Pi { arg = a2; result = r2 } ->
      conv ctx a1.ty a2.ty &&
      let ctx' = extend ctx a1.name a1.ty in
      conv ctx' r1 (subst a2.name (mk ?loc:a1.b_loc (Var a1.name)) r2)
  | Lambda { arg = a1; body = b1 }, Lambda { arg = a2; body = b2 } ->
      conv ctx a1.ty a2.ty &&
      let ctx' = extend ctx a1.name a1.ty in
      conv ctx' b1 (subst a2.name (mk ?loc:a1.b_loc (Var a1.name)) b2)
  | App (f1, args1), App (f2, args2) ->
      conv ctx f1 f2 &&
      List.length args1 = List.length args2 &&
      List.for_all2 (conv ctx) args1 args2
  | Eq { ty = t1; lhs = l1; rhs = r1 }, Eq { ty = t2; lhs = l2; rhs = r2 } ->
      conv ctx t1 t2 && conv ctx l1 l2 && conv ctx r1 r2
  | Refl { ty = t1; value = v1 }, Refl { ty = t2; value = v2 } ->
      conv ctx t1 t2 && conv ctx v1 v2
  | Match { scrutinee = s1; motive = m1; as_name = as1; cases = c1; _ },
    Match { scrutinee = s2; motive = m2; as_name = as2; cases = c2; _ } ->
      conv ctx s1 s2 &&
      (match (as1, as2) with
       | None, None -> conv ctx m1 m2
       | Some n1, Some n2 ->
           let m2' = subst n2 (mk (Var n1)) m2 in
           conv ctx m1 m2'
       | _ -> false) &&
      List.length c1 = List.length c2 &&
      List.for_all2 (fun case1 case2 ->
        String.equal case1.pattern.ctor case2.pattern.ctor &&
        List.length case1.pattern.args = List.length case2.pattern.args &&
        let substs =
          List.map2 (fun a1 a2 -> (a2.arg_name, mk (Var a1.arg_name)))
            case1.pattern.args case2.pattern.args
        in
        let body2 = List.fold_left (fun acc (x, s) -> subst x s acc) case2.body substs in
        let body2 =
          match (as1, as2) with
          | Some n1, Some n2 -> subst n2 (mk (Var n1)) body2
          | _ -> body2
        in
        let ctx' =
          List.fold_left (fun c a -> extend c a.arg_name (mk (Universe Type))) ctx case1.pattern.args
        in
        let ctx' =
          match as1 with
          | Some n -> extend ctx' n (mk (Universe Type))
          | None -> ctx'
        in
        conv ctx' case1.body body2
      ) c1 c2
  | Subset { arg = a1; pred = p1 }, Subset { arg = a2; pred = p2 } ->
      conv ctx a1.ty a2.ty &&
      let ctx' = extend ctx a1.name a1.ty in
      conv ctx' p1 (subst a2.name (mk ?loc:a1.b_loc (Var a1.name)) p2)
  | SubsetIntro { value = v1; proof = p1 }, SubsetIntro { value = v2; proof = p2 } ->
      conv ctx v1 v2 && conv ctx p1 p2
  | SubsetElim t1, SubsetElim t2 -> conv ctx t1 t2
  | SubsetProof t1, SubsetProof t2 -> conv ctx t1 t2
  | _ -> false

(** Substitute a list of (name, term) pairs into a term. *)
let subst_many (substs : (name * term) list) (t : term) : term =
  List.fold_left (fun acc (x, s) -> subst x s acc) t substs

(** Substitute a term [old_t] with [new_t] in [t]. *)
let rec subst_term (old_t : term) (new_t : term) (t : term) : term =
  if equal_ignoring_loc old_t t then new_t
  else
    let fvs = free_vars old_t in
    let is_shadowed x = List.mem x fvs in
    match t.desc with
    | Var _ | Universe _ | PrimType _ | Literal _ | Global _ -> t
    | Pi { arg; result } ->
        let arg_ty = subst_term old_t new_t arg.ty in
        let result =
          if is_shadowed arg.name then result
          else subst_term old_t new_t result
        in
        mk ?loc:t.loc (Pi { arg = { arg with ty = arg_ty }; result })
    | Lambda { arg; body } ->
        let arg_ty = subst_term old_t new_t arg.ty in
        let body =
          if is_shadowed arg.name then body
          else subst_term old_t new_t body
        in
        mk ?loc:t.loc (Lambda { arg = { arg with ty = arg_ty }; body })
    | App (f, args) ->
        mk ?loc:t.loc (App (subst_term old_t new_t f, List.map (subst_term old_t new_t) args))
    | Eq { ty; lhs; rhs } ->
        mk ?loc:t.loc (Eq { ty = subst_term old_t new_t ty; lhs = subst_term old_t new_t lhs; rhs = subst_term old_t new_t rhs })
    | Refl { ty; value } ->
        mk ?loc:t.loc (Refl { ty = subst_term old_t new_t ty; value = subst_term old_t new_t value })
    | Rewrite { proof; body } ->
        mk ?loc:t.loc (Rewrite { proof = subst_term old_t new_t proof; body = subst_term old_t new_t body })
    | If { cond; then_; else_ } ->
        mk ?loc:t.loc (If { cond = subst_term old_t new_t cond; then_ = subst_term old_t new_t then_; else_ = subst_term old_t new_t else_ })
    | Match { scrutinee; motive; as_name; cases; coverage_hint } ->
        let scrutinee = subst_term old_t new_t scrutinee in
        let motive =
          match as_name with
          | Some n when is_shadowed n -> motive
          | _ -> subst_term old_t new_t motive
        in
        let cases =
          List.map (fun c ->
            let bound = List.map (fun a -> a.arg_name) c.pattern.args in
            if List.exists is_shadowed bound then c
            else { c with body = subst_term old_t new_t c.body }
          ) cases
        in
        mk ?loc:t.loc (Match { scrutinee; motive; as_name; cases; coverage_hint })
  | Subset { arg; pred } ->
      let arg_ty = subst_term old_t new_t arg.ty in
      let pred =
        if is_shadowed arg.name then pred
        else subst_term old_t new_t pred
      in
      mk ?loc:t.loc (Subset { arg = { arg with ty = arg_ty }; pred })
  | SubsetIntro { value; proof } ->
      mk ?loc:t.loc (SubsetIntro { value = subst_term old_t new_t value; proof = subst_term old_t new_t proof })
  | SubsetElim tm ->
      mk ?loc:t.loc (SubsetElim (subst_term old_t new_t tm))
  | SubsetProof tm ->
      mk ?loc:t.loc (SubsetProof (subst_term old_t new_t tm))

(** Collect leading Π binders from a type. *)
let rec collect_pi_binders (t : term) : binder list * term =
  match t.desc with
  | Pi { arg; result } ->
      let bs, res = collect_pi_binders result in
      (arg :: bs, res)
  | _ -> ([], t)

(** Collect leading lambda binders from a term. *)
let rec collect_lambda_binders (t : term) : binder list * term =
  match t.desc with
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
  | TypeMismatch { expected; actual; context; _ } ->
      Format.sprintf "Type mismatch in %s: expected %s but got %s"
        context (pp_term expected) (pp_term actual)
  | NotAFunction (t, _) -> Format.sprintf "Cannot apply non-function term: %s" (pp_term t)
  | NotAType (t, _) -> Format.sprintf "Expected a type, but got %s" (pp_term t)
  | NotAProp (t, _) -> Format.sprintf "Expected a proposition, but got %s" (pp_term t)
  | InvalidApplication (f, arg, _) ->
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
  | InvalidRepr (name, msg) ->
      Format.sprintf "Invalid representation %s: %s" name msg
  | InvalidExternC (name, msg) ->
      Format.sprintf "Invalid extern_c %s: %s" name msg
  | InvalidExternIO (name, msg) ->
      Format.sprintf "Invalid extern_io %s: %s" name msg
  | InDeclaration (name, _loc, err) ->
      Format.sprintf "While checking %s: %s" name (string_of_typing_error err)

(** Positivity checking: ensure inductive appears only in strictly positive positions. *)
let rec positive_occurrences (target : name) (positive : bool) (t : term) : bool =
  let go = positive_occurrences target in
  match t.desc with
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
  | If { cond; then_; else_ } ->
      go positive cond && go positive then_ && go positive else_
  | Subset { arg; pred } ->
      go positive arg.ty && go positive pred
  | SubsetIntro { value; proof } ->
      go positive value && go positive proof
  | SubsetElim tm -> go positive tm
  | SubsetProof tm -> go positive tm

(** {1 Type Inference} *)

(** Infer the type of a term. *)
let rec infer (ctx : context) (t : term) : term =
  match t.desc with
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
      | Some (`Global (GExternIO ext)) -> ext.logical_type
      | Some (`Global (GRepr _)) ->
          mk ?loc:t.loc (Universe Type)
      | None -> raise (TypeError (UnboundVariable x)))
  | Universe Type -> mk ?loc:t.loc (Universe Type)  (* Type : Type - impredicative for simplicity *)
  | Universe Prop -> mk ?loc:t.loc (Universe Type)  (* Prop : Type *)
  | PrimType _ -> mk ?loc:t.loc (Universe Type)
  | Literal (LitInt32 _) -> mk ?loc:t.loc (PrimType Int32)
  | Literal (LitInt64 _) -> mk ?loc:t.loc (PrimType Int64)
  | Literal (LitFloat64 _) -> mk ?loc:t.loc (PrimType Float64)
  | Literal (LitBool _) -> mk ?loc:t.loc (PrimType Bool)
  | Literal (LitString _) -> mk ?loc:t.loc (PrimType String)
  | Pi { arg; result } ->
      let arg_kind = infer ctx arg.ty in
      (match arg_kind.desc with
      | Universe _ -> ()
      | _ -> raise (TypeError (NotAType (arg.ty, arg.ty.loc))));
      let ctx' = extend ctx arg.name arg.ty in
      let result_ty = infer ctx' result in
      (match result_ty with
      | { desc = Universe u; _ } -> mk ?loc:t.loc (Universe u)
      | _ -> raise (TypeError (NotAType (result, result.loc))))
  | Lambda { arg; body } ->
      let arg_kind = infer ctx arg.ty in
      (match arg_kind.desc with
      | Universe _ -> ()
      | _ -> raise (TypeError (NotAType (arg.ty, arg.ty.loc))));
      let ctx' = extend ctx arg.name arg.ty in
      let body_ty = infer ctx' body in
      mk ?loc:t.loc (Pi { arg; result = body_ty })
  | App (f, args) ->
      List.fold_left
        (fun f_ty arg ->
          let f_ty' = whnf ctx f_ty in
          match f_ty'.desc with
          | Pi { arg = param; result } ->
              let _ = check ctx arg param.ty in
              subst param.name arg result
          | _ -> raise (TypeError (NotAFunction (f_ty', f_ty'.loc))))
        (infer ctx f) args
  | Eq { ty; lhs; rhs } ->
      let _ = check ctx ty (mk ?loc:ty.loc (Universe Type)) in
      let _ = check ctx lhs ty in
      let _ = check ctx rhs ty in
      mk ?loc:t.loc (Universe Prop)
  | Refl { ty; value } ->
      let _ = check ctx ty (mk ?loc:ty.loc (Universe Type)) in
      let _ = check ctx value ty in
      mk ?loc:t.loc (Eq { ty; lhs = value; rhs = value })
  | Rewrite { proof; body } ->
      let proof_ty = infer ctx proof in
      let proof_ty' = whnf ctx proof_ty in
      (match proof_ty'.desc with
      | Eq { ty = _; lhs = _; rhs = _ } ->
          (* For now, just return the body's type *)
          (* Full implementation would substitute based on equality *)
          infer ctx body
      | _ ->
          raise
            (TypeError
               (TypeMismatch
                  {
                    expected =
                      mk ?loc:t.loc
                        (Eq
                           {
                             ty = mk ?loc:t.loc (Universe Type);
                             lhs = mk ?loc:t.loc (Var "_");
                             rhs = mk ?loc:t.loc (Var "_");
                           });
                    actual = proof_ty';
                    context = "rewrite proof";
                    loc = proof_ty'.loc;
                  })))
  | Match { scrutinee; motive; as_name; cases; coverage_hint = _ } ->
      let scrut_ty = infer ctx scrutinee in
      let scrut_ty_whnf = whnf ctx scrut_ty in
      let head, args =
        match scrut_ty_whnf.desc with
        | App (f, args) -> (f, args)
        | _ -> (scrut_ty_whnf, [])
      in
      let ind =
        match head.desc with
        | Var n | Global n -> (
            match lookup ctx n with
            | Some (`Global (GInductive ind)) -> ind
            | _ -> raise (TypeError (UnknownInductive n)))
        | _ -> raise (TypeError (InvalidPattern "scrutinee is not an inductive type"))
      in
      if List.length args <> List.length ind.params then
        raise (TypeError (TypeMismatch { expected = inductive_type ind; actual = scrut_ty; context = "match scrutinee parameters"; loc = t.loc }));
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
      let motive_type = whnf ctx (infer motive_ctx motive) in
      (match motive_type.desc with
      | Universe u -> u
      | _ -> raise (TypeError (NotAType (motive_type, motive_type.loc)))) |> ignore;
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
            let ctor_args = args @ List.map (fun a -> mk ?loc:a.arg_loc (Var a.arg_name)) case.pattern.args in
            if ctor_args = [] then mk (Var ctor.ctor_name)
            else mk (App (mk (Var ctor.ctor_name), ctor_args))
          in
          let expected_branch_ty =
            match as_name with
            | Some n -> subst n ctor_term motive
            | None -> motive
          in
          check branch_ctx case.body expected_branch_ty)
        cases;
      let missing =
        List.filter (fun c -> not (Hashtbl.mem seen c.ctor_name)) ind.constructors
        |> List.map (fun c -> c.ctor_name)
      in
      if missing <> [] then raise (TypeError (NonExhaustiveMatch missing));
      (match as_name with Some n -> subst n scrutinee motive | None -> motive)
  | If { cond; then_; else_ } ->
      let _ = check ctx cond (mk ?loc:cond.loc (PrimType Bool)) in
      let then_ty = infer ctx then_ in
      let else_ty = infer ctx else_ in
      if not (conv ctx then_ty else_ty) then
        raise (TypeError (TypeMismatch { expected = then_ty; actual = else_ty; context = "if branches"; loc = t.loc }));
      then_ty
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
          | GExternIO ext -> ext.logical_type
          | GRepr _ -> raise (TypeError (TypeMismatch { expected = mk ?loc:t.loc (Universe Type); actual = t; context = "repr"; loc = t.loc })))
      | _ -> raise (TypeError (UnboundVariable name)))
  | Subset { arg; pred } ->
      let arg_kind = infer ctx arg.ty in
      (match arg_kind.desc with
      | Universe _ -> ()
      | _ -> raise (TypeError (NotAType (arg.ty, arg.ty.loc))));
      let ctx' = extend ctx arg.name arg.ty in
      let pred_ty = infer ctx' pred in
      (match pred_ty.desc with
      | Universe Prop -> ()
      | _ -> raise (TypeError (NotAProp (pred, pred.loc))));
      mk ?loc:t.loc (Universe Type)
  | SubsetIntro { value = _; proof = _ } ->
      raise (TypeError (TypeMismatch { expected = mk (Var "Subset type"); actual = t; context = "inference"; loc = t.loc }))
  | SubsetElim tm ->
      let tm_ty = infer ctx tm in
      let tm_ty' = whnf ctx tm_ty in
      (match tm_ty'.desc with
      | Subset { arg; _ } -> arg.ty
      | _ -> raise (TypeError (TypeMismatch { expected = mk (Var "Subset type"); actual = tm_ty'; context = "subset elimination"; loc = tm.loc })))
  | SubsetProof tm ->
      let tm_ty = infer ctx tm in
      let tm_ty' = whnf ctx tm_ty in
      (match tm_ty'.desc with
      | Subset { arg; pred } ->
          let val_tm = mk ?loc:t.loc (SubsetElim tm) in
          subst arg.name val_tm pred
      | _ -> raise (TypeError (TypeMismatch { expected = mk (Var "Subset type"); actual = tm_ty'; context = "subset proof elimination"; loc = tm.loc })))

(** Check that a term has a given type. *)
and check (ctx : context) (t : term) (expected : term) : unit =
  match t.desc with
  | SubsetIntro { value; proof } ->
      let expected' = whnf ctx expected in
      (match expected'.desc with
      | Subset { arg; pred } ->
          check ctx value arg.ty;
          let pred_inst = subst arg.name value pred in
          check ctx proof pred_inst
      | _ ->
          let actual = infer ctx t in
          if not (conv ctx actual expected) then
            raise (TypeError (TypeMismatch { expected; actual; context = "check"; loc = t.loc })))
  | Rewrite { proof; body } ->
      let proof_ty = infer ctx proof in
      let proof_ty' = whnf ctx proof_ty in
      (match proof_ty'.desc with
      | Eq { ty = _; lhs = u; rhs = v } ->
          let expected_body = subst_term v u expected in
          check ctx body expected_body
      | _ ->
          raise (TypeError (TypeMismatch { expected = mk ?loc:t.loc (Eq { ty = mk (Universe Type); lhs = mk (Var "_"); rhs = mk (Var "_") }); actual = proof_ty'; context = "rewrite proof"; loc = proof_ty'.loc })))
  | Lambda { arg; body } ->
      let expected' = whnf ctx expected in
      (match expected'.desc with
      | Pi { arg = expected_arg; result = expected_result } ->
          if not (conv ctx arg.ty expected_arg.ty) then
             raise (TypeError (TypeMismatch { expected = expected_arg.ty; actual = arg.ty; context = "lambda argument type"; loc = arg.ty.loc }));
          if arg.role <> expected_arg.role then
             raise (TypeError (RoleMismatch (arg.name, expected_arg.role, arg.role)));
          let ctx' = extend ctx arg.name arg.ty in
          let expected_body_ty = subst expected_arg.name (mk (Var arg.name)) expected_result in
          check ctx' body expected_body_ty
      | _ ->
          let actual = infer ctx t in
          if not (conv ctx actual expected) then
            raise (TypeError (TypeMismatch { expected; actual; context = "check"; loc = t.loc })))
  | _ ->
      let actual = infer ctx t in
      if not (conv ctx actual expected) then
        raise (TypeError (TypeMismatch { expected; actual; context = "check"; loc = t.loc }))

(** {1 Termination Checking} *)

let rec has_self_reference (self : name) (t : term) : bool =
  match t.desc with
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
  | If { cond; then_; else_ } ->
      has_self_reference self cond || has_self_reference self then_ || has_self_reference self else_
  | Subset { arg; pred } -> has_self_reference self arg.ty || has_self_reference self pred
  | SubsetIntro { value; proof } -> has_self_reference self value || has_self_reference self proof
  | SubsetElim tm -> has_self_reference self tm
  | SubsetProof tm -> has_self_reference self tm

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
            let ty_whnf = whnf (make_ctx (empty_sig ())) b.ty in
            (* Handle both plain inductives (Nat) and parameterized ones (List A) *)
            let head = match ty_whnf.desc with
              | App (f, _) -> f
              | _ -> ty_whnf
            in
            match head.desc with
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
    match t.desc with
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
              match f.desc with
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
                  | Some arg_term -> (
                      match arg_term.desc with
                      | Var v ->
                          let allowed_set = get_allowed allowed idx in
                          if not (StringSet.mem v allowed_set) then
                            raise (TypeError (TerminationCheckFailed def.def_name))
                      | _ -> raise (TypeError (TerminationCheckFailed def.def_name)))
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
              match scrutinee.desc with
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
        | If { cond; then_; else_ } ->
            check_term allowed cond;
            check_term allowed then_;
            check_term allowed else_
        | Subset { arg; pred } ->
            check_term allowed arg.ty;
            check_term allowed pred
        | SubsetIntro { value; proof } ->
            check_term allowed value;
            check_term allowed proof
        | SubsetElim tm -> check_term allowed tm
        | SubsetProof tm -> check_term allowed tm
      in
      check_term initial_allowed lam_body)

(** {1 Declaration Checking} *)

let check_repr (ctx : context) (repr : repr_decl) : unit =
  match repr.kind with
  | Primitive { size_bits; _ } ->
      if size_bits <= 0 then
        raise (TypeError (InvalidRepr (repr.repr_name, "size must be positive")))
  | Struct { fields; size_bytes; _ } ->
      (* Check fields *)
      let _ = List.fold_left (fun offset field ->
        if field.offset_bytes < offset then
          raise (TypeError (InvalidRepr (repr.repr_name, Printf.sprintf "overlapping field %s" field.field_name)));
        (* Lookup field repr *)
        let field_size =
          match lookup ctx field.field_repr with
          | Some (`Global (GRepr r)) -> (
              match r.kind with
              | Primitive p -> p.size_bits / 8
              | Struct s -> s.size_bytes
            )
          | _ -> raise (TypeError (InvalidRepr (repr.repr_name, Printf.sprintf "unknown repr %s for field %s" field.field_repr field.field_name)))
        in
        if field.offset_bytes + field_size > size_bytes then
          raise (TypeError (InvalidRepr (repr.repr_name, Printf.sprintf "field %s exceeds struct size" field.field_name)));
        field.offset_bytes + field_size
      ) 0 fields in
      ()

let check_extern_c (ctx : context) (ext : extern_c_decl) : unit =
  (* Check return repr *)
  (match ext.return_repr with
  | Some r -> (
      match lookup ctx r with
      | Some (`Global (GRepr _)) -> ()
      | _ -> raise (TypeError (InvalidExternC (ext.extern_name, Printf.sprintf "unknown return repr %s" r)))
    )
  | None -> ());
  (* Check arg reprs *)
  List.iter (fun arg ->
    match lookup ctx arg.extern_arg_repr with
    | Some (`Global (GRepr _)) -> ()
    | _ -> raise (TypeError (InvalidExternC (ext.extern_name, Printf.sprintf "unknown arg repr %s for %s" arg.extern_arg_repr arg.extern_arg_name)))
  ) ext.args;
  (* Check logical type *)
  let _ = check ctx ext.logical_type (mk ?loc:ext.extern_loc (Universe Type)) in
  ()

let check_extern_io (ctx : context) (ext : extern_io_decl) : unit =
  (* Check logical type *)
  let _ = check ctx ext.logical_type (mk ?loc:ext.extern_io_loc (Universe Type)) in
  (* Check result repr *)
  (match ext.result_repr with
  | Some r -> (
      match lookup ctx r with
      | Some (`Global (GRepr _)) -> ()
      | _ -> raise (TypeError (InvalidExternIO (ext.extern_io_name, Printf.sprintf "unknown result repr %s" r)))
    )
  | None -> ());
  (* Check arg reprs *)
  List.iter (fun arg ->
    match lookup ctx arg.extern_arg_repr with
    | Some (`Global (GRepr _)) -> ()
    | _ -> raise (TypeError (InvalidExternIO (ext.extern_io_name, Printf.sprintf "unknown arg repr %s for %s" arg.extern_arg_repr arg.extern_arg_name)))
  ) ext.args;
  ()

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
            let p_kind = infer c p.ty in
            (match p_kind.desc with
            | Universe _ -> ()
            | _ -> raise (TypeError (NotAType (p.ty, p.ty.loc))));
            extend c p.name p.ty)
          ctx ind.params
      in
      (* Check constructor types (simplified - full check needs positivity) *)
      List.iter
        (fun ctor ->
          let _ = List.fold_left
            (fun c arg ->
              let arg_kind = infer c arg.ty in
              (match arg_kind.desc with
              | Universe _ -> ()
              | _ -> raise (TypeError (NotAType (arg.ty, arg.ty.loc))));
              extend c arg.name arg.ty)
            ctx' ctor.ctor_args
          in ())
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
        let type_kind = infer ctx def.def_type in
        (match type_kind.desc with
        | Universe _ -> ()
        | _ -> raise (TypeError (NotAType (def.def_type, def.def_type.loc))));
        check ctx def.def_body def.def_type;
        if def.def_role <> Runtime then check_termination def)
  | Theorem thm ->
      with_decl thm.thm_name thm.thm_loc (fun () ->
        let _ = check ctx thm.thm_type (mk ?loc:thm.thm_loc (Universe Prop)) in
        check ctx thm.thm_proof thm.thm_type)
  | Repr repr ->
      with_decl repr.repr_name repr.repr_loc (fun () -> check_repr ctx repr)
  | ExternC ext ->
      with_decl ext.extern_name ext.extern_loc (fun () -> check_extern_c ctx ext)
  | ExternIO ext ->
      with_decl ext.extern_io_name ext.extern_io_loc (fun () -> check_extern_io ctx ext)

(** Check an entire module. *)
let check_module (mod_ : module_decl) (initial_sig : signature) : (signature, typing_error) result =
  try
    let mod_sig = build_signature mod_.declarations in
    let full_sig = merge_signatures initial_sig mod_sig in
    let ctx = make_ctx full_sig in
    List.iter (check_declaration ctx) mod_.declarations;
    Ok full_sig
  with TypeError e -> Error e
