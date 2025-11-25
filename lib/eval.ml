(** Evaluator for CertiJSON terms.
    
    This module implements the evaluation semantics (big-step). *)

open Syntax
open Context

(** {1 Values} *)

(** Runtime values. *)
type value =
  | VLambda of { arg : binder; body : term; env : env }
  | VConstructor of name * value list
  | VUniverse of universe
  | VPi of { arg : binder; result : term; env : env }
  | VEq of { ty : value; lhs : value; rhs : value }
  | VRefl of { ty : value; value : value }
  | VLiteral of literal
  | VPrimType of prim_type
  | VNeutral of neutral

(** Neutral terms (stuck computations). *)
and neutral =
  | NVar of name
  | NApp of neutral * value list
  | NMatch of neutral * term * case list

(** Environment mapping variables to values. *)
and env = (name * value) list

(** {1 Environment Operations} *)

let empty_env : env = []

let extend_env (env : env) (x : name) (v : value) : env =
  (x, v) :: env

let lookup_env (env : env) (x : name) : value option =
  List.assoc_opt x env

(** {1 Evaluation} *)

(** Evaluate a term to a value. *)
let rec eval (ctx : context) (env : env) (t : term) : value =
  match t with
  | Var x -> (
      match lookup_env env x with
      | Some v -> v
      | None -> VNeutral (NVar x))
  | Universe u -> VUniverse u
  | PrimType p -> VPrimType p
  | Literal l -> VLiteral l
  | Pi { arg; result } ->
      VPi { arg; result; env }
  | Lambda { arg; body } ->
      VLambda { arg; body; env }
  | App (f, args) ->
      let f_val = eval ctx env f in
      let arg_vals = List.map (eval ctx env) args in
      apply_all ctx f_val arg_vals
  | Eq { ty; lhs; rhs } ->
      VEq { ty = eval ctx env ty; lhs = eval ctx env lhs; rhs = eval ctx env rhs }
  | Refl { ty; value } ->
      VRefl { ty = eval ctx env ty; value = eval ctx env value }
  | Rewrite { body; _ } ->
      (* Rewrite is computationally the identity *)
      eval ctx env body
  | Match { scrutinee; cases; _ } ->
      let scrut_val = eval ctx env scrutinee in
      eval_match ctx env scrut_val cases
  | Global name -> (
      match lookup ctx name with
      | Some (`Global (GDefinition def)) when def.def_role <> ProofOnly ->
          eval ctx env def.def_body
      | Some (`Global (GConstructor _)) ->
          VConstructor (name, [])
      | _ -> VNeutral (NVar name))

(** Apply a value to arguments. *)
and apply_all (ctx : context) (f : value) (args : value list) : value =
  List.fold_left (apply ctx) f args

and apply (ctx : context) (f : value) (arg : value) : value =
  match f with
  | VLambda { arg = param; body; env } ->
      let env' = extend_env env param.name arg in
      eval ctx env' body
  | VConstructor (name, args) ->
      VConstructor (name, args @ [arg])
  | VNeutral n ->
      VNeutral (NApp (n, [arg]))
  | _ -> VNeutral (NApp (NVar "_stuck_", [f; arg]))

(** Evaluate a pattern match. *)
and eval_match (ctx : context) (env : env) (scrut : value) (cases : case list) : value =
  match scrut with
  | VConstructor (ctor_name, args) -> (
      match List.find_opt (fun c -> String.equal c.pattern.ctor ctor_name) cases with
      | Some case ->
          let bindings =
            List.combine (List.map (fun a -> a.arg_name) case.pattern.args) args
          in
          let env' = List.fold_left (fun e (x, v) -> extend_env e x v) env bindings in
          eval ctx env' case.body
      | None -> VNeutral (NMatch (NVar "_no_case_", Universe Type, cases)))
  | VNeutral n -> VNeutral (NMatch (n, Universe Type, cases))
  | _ -> VNeutral (NMatch (NVar "_stuck_match_", Universe Type, cases))

(** {1 Readback (Quote)} *)

(** Convert a value back to a term. *)
let rec quote (v : value) : term =
  match v with
  | VLambda { arg; body; env = _ } ->
      Lambda { arg; body }  (* Simplified - should do proper closure conversion *)
  | VConstructor (name, []) -> Global name
  | VConstructor (name, args) ->
      App (Global name, List.map quote args)
  | VUniverse u -> Universe u
  | VPi { arg; result; env = _ } ->
      Pi { arg; result }
  | VEq { ty; lhs; rhs } ->
      Eq { ty = quote ty; lhs = quote lhs; rhs = quote rhs }
  | VRefl { ty; value } ->
      Refl { ty = quote ty; value = quote value }
  | VLiteral l -> Literal l
  | VPrimType p -> PrimType p
  | VNeutral n -> quote_neutral n

and quote_neutral (n : neutral) : term =
  match n with
  | NVar x -> Var x
  | NApp (f, args) -> App (quote_neutral f, List.map quote args)
  | NMatch (scrut, motive, cases) ->
      Match { scrutinee = quote_neutral scrut; motive; as_name = None; cases; coverage_hint = Unknown }

(** {1 Normalization} *)

(** Normalize a term (evaluate and quote back). *)
let normalize (ctx : context) (t : term) : term =
  quote (eval ctx empty_env t)

(** {1 Entry Points} *)

(** Evaluate a closed term. *)
let eval_closed (ctx : context) (t : term) : value =
  eval ctx empty_env t

(** Check if two values are equal (for testing). *)
let rec value_eq (v1 : value) (v2 : value) : bool =
  match (v1, v2) with
  | VLiteral l1, VLiteral l2 -> equal_literal l1 l2
  | VConstructor (n1, args1), VConstructor (n2, args2) ->
      String.equal n1 n2 &&
      List.length args1 = List.length args2 &&
      List.for_all2 value_eq args1 args2
  | VUniverse u1, VUniverse u2 -> equal_universe u1 u2
  | VPrimType p1, VPrimType p2 -> equal_prim_type p1 p2
  | _ -> false
