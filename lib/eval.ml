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
  | VWorld
  | VExternIO of extern_io_decl * value list
  | VBuiltin of string * value list

(** Neutral terms (stuck computations). *)
and neutral =
  | NVar of name
  | NApp of neutral * value list
  | NMatch of neutral * term * case list
  | NIf of neutral * term * term

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
  match t.desc with
  | Var x -> (
      match lookup_env env x with
      | Some v -> v
      | None -> (
          match x with
          | "add" | "sub" | "mul" | "div" | "lt" | "gt" | "eq" -> VBuiltin (x, [])
          | _ -> (
              match lookup ctx x with
              | Some (`Global (GDefinition def)) when def.def_role <> ProofOnly ->
                  eval ctx env def.def_body
              | Some (`Global (GConstructor _)) ->
                  VConstructor (x, [])
              | Some (`Global (GExternIO ext)) ->
                  VExternIO (ext, [])
              | _ -> VNeutral (NVar x))))
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
  | If { cond; then_; else_ } ->
      let cond_val = eval ctx env cond in
      (match cond_val with
      | VLiteral (LitBool true) -> eval ctx env then_
      | VLiteral (LitBool false) -> eval ctx env else_
      | VNeutral n -> VNeutral (NIf (n, then_, else_))
      | _ -> failwith "Runtime error: If condition must be a boolean")
  | Global name -> (
      match name with
      | "add" | "sub" | "mul" | "div" | "lt" | "gt" | "eq" -> VBuiltin (name, [])
      | _ -> (
          match lookup ctx name with
          | Some (`Global (GDefinition def)) when def.def_role <> ProofOnly ->
              eval ctx env def.def_body
          | Some (`Global (GConstructor _)) ->
              VConstructor (name, [])
          | Some (`Global (GExternIO ext)) ->
              VExternIO (ext, [])
          | _ -> VNeutral (NVar name)))

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
  | VExternIO (ext, args) ->
      if List.length args < List.length ext.args then
        VExternIO (ext, args @ [arg])
      else
        (* Expecting World argument *)
        (match arg with
        | VWorld ->
            (* Execute IO effect *)
            let result = match ext.c_name with
            | "cj_print_line" | "cj_println" -> (
                match args with
                | [VLiteral (LitString s)] -> print_endline s; VConstructor ("tt", [])
                | [VConstructor ("mk_string", [VLiteral (LitString s)])] -> print_endline s; VConstructor ("tt", [])
                | _ -> Printf.printf "[IO] %s\n" ext.extern_io_name; VConstructor ("tt", [])
              )
            | "cj_print" -> (
                match args with
                | [VLiteral (LitString s)] -> print_string s; VConstructor ("tt", [])
                | _ -> Printf.printf "[IO] %s\n" ext.extern_io_name; VConstructor ("tt", [])
              )
            | "cj_read_line" -> (
                try
                  let s = read_line () in
                  VLiteral (LitString s)
                with End_of_file -> VLiteral (LitString "")
              )
            | "cj_random_u64" -> (
                VLiteral (LitInt64 (Int64.of_int (Random.int 1000000))) (* Mock implementation *)
              )
            | "getenv" -> (
                match args with
                | [VLiteral (LitString s)] -> (
                    try VLiteral (LitString (Sys.getenv s))
                    with Not_found -> VLiteral (LitString "")
                  )
                | _ -> VConstructor ("tt", [])
              )
            | "system" -> (
                match args with
                | [VLiteral (LitString s)] -> VLiteral (LitInt32 (Int32.of_int (Sys.command s)))
                | _ -> VConstructor ("tt", [])
              )
            | "exit" -> (
                match args with
                | [VLiteral (LitInt32 i)] -> exit (Int32.to_int i)
                | _ -> VConstructor ("tt", [])
              )
            | "time" -> (
                 VLiteral (LitInt64 (Int64.of_float (Unix.time ())))
              )
            | "clock" -> (
                 VLiteral (LitInt64 (Int64.of_float (Sys.time () *. 1000000.0)))
              )
            | "malloc" -> (
                 VLiteral (LitInt64 12345L) (* Dummy pointer *)
              )
            | "free" -> (
                 VConstructor ("tt", [])
              )
            | "uintptr_to_ptr" -> (
                match args with
                | [VLiteral (LitInt64 i)] -> VLiteral (LitInt64 i)
                | _ -> VConstructor ("tt", [])
              )
            | "ptr_to_uintptr" -> (
                match args with
                | [VLiteral (LitInt64 i)] -> VLiteral (LitInt64 i)
                | _ -> VConstructor ("tt", [])
              )
            | "sleep" -> (
                match args with
                | [VLiteral (LitInt64 s)] -> 
                    Unix.sleep (Int64.to_int s);
                    VLiteral (LitInt64 0L)
                | _ -> VConstructor ("tt", [])
              )
            | "usleep" -> (
                match args with
                | [VLiteral (LitInt64 us)] -> 
                    let seconds = (Int64.to_float us) /. 1000000.0 in
                    Unix.sleepf seconds;
                    VLiteral (LitInt32 0l)
                | _ -> VConstructor ("tt", [])
              )
            | "getcwd" -> (
                VLiteral (LitString (Sys.getcwd ()))
              )
            | "chdir" -> (
                match args with
                | [VLiteral (LitString s)] -> 
                    Sys.chdir s;
                    VLiteral (LitInt32 0l)
                | _ -> VConstructor ("tt", [])
              )
            | "unlink" -> (
                match args with
                | [VLiteral (LitString s)] -> 
                    Sys.remove s;
                    VLiteral (LitInt32 0l)
                | _ -> VConstructor ("tt", [])
              )
            | "rename" -> (
                match args with
                | [VLiteral (LitString old); VLiteral (LitString new_)] -> 
                    Sys.rename old new_;
                    VLiteral (LitInt32 0l)
                | _ -> VConstructor ("tt", [])
              )
            | _ -> Printf.printf "[IO] %s (c_name: %s)\n" ext.extern_io_name ext.c_name; VConstructor ("tt", [])
            in
            VConstructor ("pair", [result; VWorld])
        | _ -> VNeutral (NApp (NVar "_stuck_io_", [f; arg])))
  | VBuiltin (op, args) ->
      let args' = args @ [arg] in
      if List.length args' = 2 then
        match op, args' with
        | "add", [VLiteral (LitInt32 a); VLiteral (LitInt32 b)] -> VLiteral (LitInt32 (Int32.add a b))
        | "sub", [VLiteral (LitInt32 a); VLiteral (LitInt32 b)] -> VLiteral (LitInt32 (Int32.sub a b))
        | "mul", [VLiteral (LitInt32 a); VLiteral (LitInt32 b)] -> VLiteral (LitInt32 (Int32.mul a b))
        | "div", [VLiteral (LitInt32 a); VLiteral (LitInt32 b)] -> VLiteral (LitInt32 (Int32.div a b))
        | "lt", [VLiteral (LitInt32 a); VLiteral (LitInt32 b)] -> VLiteral (LitBool (a < b))
        | "gt", [VLiteral (LitInt32 a); VLiteral (LitInt32 b)] -> VLiteral (LitBool (a > b))
        | "eq", [VLiteral (LitInt32 a); VLiteral (LitInt32 b)] -> VLiteral (LitBool (a = b))
        | _ -> VNeutral (NApp (NVar ("_stuck_builtin_" ^ op), args'))
      else
        VBuiltin (op, args')
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
      | None -> VNeutral (NMatch (NVar "_no_case_", mk (Universe Type), cases)))
  | VNeutral n -> VNeutral (NMatch (n, mk (Universe Type), cases))
  | _ -> VNeutral (NMatch (NVar "_stuck_match_", mk (Universe Type), cases))

(** {1 Readback (Quote)} *)

(** Convert a value back to a term. *)
let rec quote (v : value) : term =
  match v with
  | VLambda { arg; body; env = _ } ->
      mk ?loc:arg.b_loc (Lambda { arg; body })  (* Simplified - should do proper closure conversion *)
  | VConstructor (name, []) -> mk (Global name)
  | VConstructor (name, args) ->
      mk (App (mk (Global name), List.map quote args))
  | VUniverse u -> mk (Universe u)
  | VPi { arg; result; env = _ } ->
      mk ?loc:arg.b_loc (Pi { arg; result })
  | VEq { ty; lhs; rhs } ->
      mk (Eq { ty = quote ty; lhs = quote lhs; rhs = quote rhs })
  | VRefl { ty; value } ->
      mk (Refl { ty = quote ty; value = quote value })
  | VLiteral l -> mk (Literal l)
  | VPrimType p -> mk (PrimType p)
  | VWorld -> mk (Var "World") (* Should not happen in normal terms *)
  | VExternIO (ext, args) ->
      let head = mk (Global ext.extern_io_name) in
      mk (App (head, List.map quote args))
  | VBuiltin (op, args) ->
      let head = mk (Global op) in
      mk (App (head, List.map quote args))
  | VNeutral n -> quote_neutral n

and quote_neutral (n : neutral) : term =
  match n with
  | NVar x -> mk (Var x)
  | NApp (f, args) -> mk (App (quote_neutral f, List.map quote args))
  | NMatch (scrut, motive, cases) ->
      mk (Match { scrutinee = quote_neutral scrut; motive; as_name = None; cases; coverage_hint = Unknown })
  | NIf (cond, then_, else_) ->
      mk (If { cond = quote_neutral cond; then_; else_ })

(** {1 Normalization} *)

(** Normalize a term (evaluate and quote back). *)
let normalize (ctx : context) (t : term) : term =
  quote (eval ctx empty_env t)

(** {1 Entry Points} *)

(** Evaluate a closed term. *)
let eval_closed (ctx : context) (t : term) : value =
  eval ctx empty_env t

(** Run an IO program. *)
let run_io (ctx : context) (t : term) : unit =
  let v = eval ctx empty_env t in
  let _ = apply ctx v VWorld in
  ()

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
  | VBuiltin (op1, args1), VBuiltin (op2, args2) ->
      String.equal op1 op2 &&
      List.length args1 = List.length args2 &&
      List.for_all2 value_eq args1 args2
  | _ -> false
