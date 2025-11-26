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
  | VSubset of { arg : binder; pred : term; env : env }
  | VArray of { elem_ty : value; size : value }
  | VArrayHandle of { elem_ty : value; size : value }

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

(** {1 Heap for Arrays} *)

let heap : (int64, value array) Hashtbl.t = Hashtbl.create 100
let next_ptr = ref 1L

let alloc_array (size : int) (init : value) : int64 =
  let ptr = !next_ptr in
  next_ptr := Int64.add ptr 1L;
  let arr = Array.make size init in
  Hashtbl.add heap ptr arr;
  ptr

let get_array (ptr : int64) (idx : int) : value =
  match Hashtbl.find_opt heap ptr with
  | Some arr -> 
      if idx >= 0 && idx < Array.length arr then arr.(idx)
      else failwith "Array index out of bounds"
  | None -> failwith "Invalid array pointer"

let set_array (ptr : int64) (idx : int) (v : value) : unit =
  match Hashtbl.find_opt heap ptr with
  | Some arr ->
      if idx >= 0 && idx < Array.length arr then arr.(idx) <- v
      else failwith "Array index out of bounds"
  | None -> failwith "Invalid array pointer"

let free_array (ptr : int64) : unit =
  Hashtbl.remove heap ptr

let rec nat_to_int (v : value) : int =
  match v with
  | VConstructor ("zero", []) -> 0
  | VConstructor ("succ", [n]) -> 1 + nat_to_int n
  | VConstructor ("fzero", _) -> 0
  | VConstructor ("fsucc", [_; i]) -> 1 + nat_to_int i
  | _ -> 0 (* failwith "Not a Nat" - be lenient for now *)

(** {1 Evaluation} *)

(** Evaluate a term to a value. *)
let rec eval (ctx : context) (env : env) (t : term) : value =
  match t.desc with
  | Var x -> (
      match lookup_env env x with
      | Some v -> v
      | None -> (
          match x with
          | "add" | "sub" | "mul" | "div" | "mod" | "neg"
          | "lt" | "gt" | "eq" | "le" | "ge" | "ne"
          | "add64_builtin" | "sub64_builtin" | "mul64_builtin" | "div64_builtin"
          | "strlen" | "strcmp" | "strncmp" | "strcasecmp"
          | "atoi" | "atol" | "atof"
          | "isalnum" | "isalpha" | "isblank" | "iscntrl" | "isdigit"
          | "isgraph" | "islower" | "isprint" | "ispunct" | "isspace"
          | "isupper" | "isxdigit" | "tolower" | "toupper"
          -> VBuiltin (x, [])
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
  | Subset { arg; pred } -> VSubset { arg; pred; env }
  | SubsetIntro { value; proof = _ } -> eval ctx env value
  | SubsetElim tm -> eval ctx env tm
  | SubsetProof _ -> VConstructor ("tt", [])
  | Array { elem_ty; size } ->
      VArray { elem_ty = eval ctx env elem_ty; size = eval ctx env size }
  | ArrayHandle { elem_ty; size } ->
      VArrayHandle { elem_ty = eval ctx env elem_ty; size = eval ctx env size }
  | If { cond; then_; else_ } ->
      let cond_val = eval ctx env cond in
      (match cond_val with
      | VLiteral (LitBool true) -> eval ctx env then_
      | VLiteral (LitBool false) -> eval ctx env else_
      | VNeutral n -> VNeutral (NIf (n, then_, else_))
      | _ -> failwith "Runtime error: If condition must be a boolean")
  | Global name -> (
      match name with
      | "add" | "sub" | "mul" | "div" | "mod" | "neg"
      | "lt" | "gt" | "eq" | "le" | "ge" | "ne"
      | "add64_builtin" | "sub64_builtin" | "mul64_builtin" | "div64_builtin"
      | "strlen" | "strcmp" | "strncmp" | "strcasecmp"
      | "atoi" | "atol" | "atof"
      | "isalnum" | "isalpha" | "isblank" | "iscntrl" | "isdigit"
      | "isgraph" | "islower" | "isprint" | "ispunct" | "isspace"
      | "isupper" | "isxdigit" | "tolower" | "toupper"
      -> VBuiltin (name, [])
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
            | "cj_array_new" -> (
                match args with
                | [_; n; v] ->
                    let size = nat_to_int n in
                    let ptr = alloc_array size v in
                    let handle_val = VLiteral (LitInt64 ptr) in
                    handle_val
                | _ -> VConstructor ("tt", [])
              )
            | "cj_array_get" -> (
                match args with
                | [_; _; handle; i] ->
                    let ptr = match handle with VLiteral (LitInt64 p) -> p | _ -> 0L in
                    let idx = nat_to_int i in
                    let val_ = get_array ptr idx in
                    val_
                | _ -> VConstructor ("tt", [])
              )
            | "cj_array_set" -> (
                match args with
                | [_; _; handle; i; v] ->
                    let ptr = match handle with VLiteral (LitInt64 p) -> p | _ -> 0L in
                    let idx = nat_to_int i in
                    set_array ptr idx v;
                    VConstructor ("tt", [])
                | _ -> VConstructor ("tt", [])
              )
            | "cj_array_drop" -> (
                match args with
                | [_; _; handle] ->
                    let ptr = match handle with VLiteral (LitInt64 p) -> p | _ -> 0L in
                    free_array ptr;
                    VConstructor ("tt", [])
                | _ -> VConstructor ("tt", [])
              )
            | _ -> Printf.printf "[IO] %s (c_name: %s)\n" ext.extern_io_name ext.c_name; VConstructor ("tt", [])
            in
            VConstructor ("pair", [result; VWorld])
        | _ -> VNeutral (NApp (NVar "_stuck_io_", [f; arg])))
  | VBuiltin (op, args) ->
      let args' = args @ [arg] in
      (match op, args' with
      (* Unary operations *)
      | "neg", [VLiteral (LitInt32 a)] -> VLiteral (LitInt32 (Int32.neg a))
      | "atoi", [VLiteral (LitString s)] -> (try VLiteral (LitInt32 (Int32.of_string s)) with _ -> VLiteral (LitInt32 0l))
      | "atol", [VLiteral (LitString s)] -> (try VLiteral (LitInt64 (Int64.of_string s)) with _ -> VLiteral (LitInt64 0L))
      | "atof", [VLiteral (LitString s)] -> (try VLiteral (LitFloat64 (Float.of_string s)) with _ -> VLiteral (LitFloat64 0.0))
      | "strlen", [VLiteral (LitString s)] -> VLiteral (LitInt32 (Int32.of_int (String.length s)))
      (* Character classification - convert Int32 to char and test *)
      | "isalnum", [VLiteral (LitInt32 c)] ->
          let ch = Char.chr (Int32.to_int c land 0xFF) in
          VLiteral (LitInt32 (if (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9') then 1l else 0l))
      | "isalpha", [VLiteral (LitInt32 c)] ->
          let ch = Char.chr (Int32.to_int c land 0xFF) in
          VLiteral (LitInt32 (if (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') then 1l else 0l))
      | "isblank", [VLiteral (LitInt32 c)] ->
          let ch = Char.chr (Int32.to_int c land 0xFF) in
          VLiteral (LitInt32 (if ch = ' ' || ch = '\t' then 1l else 0l))
      | "iscntrl", [VLiteral (LitInt32 c)] ->
          let ci = Int32.to_int c land 0xFF in
          VLiteral (LitInt32 (if ci < 32 || ci = 127 then 1l else 0l))
      | "isdigit", [VLiteral (LitInt32 c)] ->
          let ch = Char.chr (Int32.to_int c land 0xFF) in
          VLiteral (LitInt32 (if ch >= '0' && ch <= '9' then 1l else 0l))
      | "isgraph", [VLiteral (LitInt32 c)] ->
          let ci = Int32.to_int c land 0xFF in
          VLiteral (LitInt32 (if ci > 32 && ci < 127 then 1l else 0l))
      | "islower", [VLiteral (LitInt32 c)] ->
          let ch = Char.chr (Int32.to_int c land 0xFF) in
          VLiteral (LitInt32 (if ch >= 'a' && ch <= 'z' then 1l else 0l))
      | "isprint", [VLiteral (LitInt32 c)] ->
          let ci = Int32.to_int c land 0xFF in
          VLiteral (LitInt32 (if ci >= 32 && ci < 127 then 1l else 0l))
      | "ispunct", [VLiteral (LitInt32 c)] ->
          let ci = Int32.to_int c land 0xFF in
          let ch = Char.chr ci in
          VLiteral (LitInt32 (if ci >= 33 && ci < 127 && not ((ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9')) then 1l else 0l))
      | "isspace", [VLiteral (LitInt32 c)] ->
          let ch = Char.chr (Int32.to_int c land 0xFF) in
          VLiteral (LitInt32 (if ch = ' ' || ch = '\t' || ch = '\n' || ch = '\r' || ch = '\x0b' || ch = '\x0c' then 1l else 0l))
      | "isupper", [VLiteral (LitInt32 c)] ->
          let ch = Char.chr (Int32.to_int c land 0xFF) in
          VLiteral (LitInt32 (if ch >= 'A' && ch <= 'Z' then 1l else 0l))
      | "isxdigit", [VLiteral (LitInt32 c)] ->
          let ch = Char.chr (Int32.to_int c land 0xFF) in
          VLiteral (LitInt32 (if (ch >= '0' && ch <= '9') || (ch >= 'a' && ch <= 'f') || (ch >= 'A' && ch <= 'F') then 1l else 0l))
      | "tolower", [VLiteral (LitInt32 c)] ->
          let ch = Char.chr (Int32.to_int c land 0xFF) in
          VLiteral (LitInt32 (Int32.of_int (Char.code (Char.lowercase_ascii ch))))
      | "toupper", [VLiteral (LitInt32 c)] ->
          let ch = Char.chr (Int32.to_int c land 0xFF) in
          VLiteral (LitInt32 (Int32.of_int (Char.code (Char.uppercase_ascii ch))))
      (* Binary Int32 operations *)
      | "add", [VLiteral (LitInt32 a); VLiteral (LitInt32 b)] -> VLiteral (LitInt32 (Int32.add a b))
      | "sub", [VLiteral (LitInt32 a); VLiteral (LitInt32 b)] -> VLiteral (LitInt32 (Int32.sub a b))
      | "mul", [VLiteral (LitInt32 a); VLiteral (LitInt32 b)] -> VLiteral (LitInt32 (Int32.mul a b))
      | "div", [VLiteral (LitInt32 a); VLiteral (LitInt32 b)] -> VLiteral (LitInt32 (Int32.div a b))
      | "mod", [VLiteral (LitInt32 a); VLiteral (LitInt32 b)] -> VLiteral (LitInt32 (Int32.rem a b))
      | "lt", [VLiteral (LitInt32 a); VLiteral (LitInt32 b)] -> VLiteral (LitBool (a < b))
      | "gt", [VLiteral (LitInt32 a); VLiteral (LitInt32 b)] -> VLiteral (LitBool (a > b))
      | "eq", [VLiteral (LitInt32 a); VLiteral (LitInt32 b)] -> VLiteral (LitBool (a = b))
      | "le", [VLiteral (LitInt32 a); VLiteral (LitInt32 b)] -> VLiteral (LitBool (a <= b))
      | "ge", [VLiteral (LitInt32 a); VLiteral (LitInt32 b)] -> VLiteral (LitBool (a >= b))
      | "ne", [VLiteral (LitInt32 a); VLiteral (LitInt32 b)] -> VLiteral (LitBool (a <> b))
      (* Binary Int64 operations *)
      | "add64_builtin", [VLiteral (LitInt64 a); VLiteral (LitInt64 b)] -> VLiteral (LitInt64 (Int64.add a b))
      | "sub64_builtin", [VLiteral (LitInt64 a); VLiteral (LitInt64 b)] -> VLiteral (LitInt64 (Int64.sub a b))
      | "mul64_builtin", [VLiteral (LitInt64 a); VLiteral (LitInt64 b)] -> VLiteral (LitInt64 (Int64.mul a b))
      | "div64_builtin", [VLiteral (LitInt64 a); VLiteral (LitInt64 b)] -> VLiteral (LitInt64 (Int64.div a b))
      (* String comparisons *)
      | "strcmp", [VLiteral (LitString s1); VLiteral (LitString s2)] -> VLiteral (LitInt32 (Int32.of_int (String.compare s1 s2)))
      | "strcasecmp", [VLiteral (LitString s1); VLiteral (LitString s2)] -> VLiteral (LitInt32 (Int32.of_int (String.compare (String.lowercase_ascii s1) (String.lowercase_ascii s2))))
      (* String comparisons with length *)
      | "strncmp", [VLiteral (LitString s1); VLiteral (LitString s2); VLiteral (LitInt32 n)] ->
          let n = Int32.to_int n in
          let s1' = if String.length s1 <= n then s1 else String.sub s1 0 n in
          let s2' = if String.length s2 <= n then s2 else String.sub s2 0 n in
          VLiteral (LitInt32 (Int32.of_int (String.compare s1' s2')))
      (* Still collecting args *)
      | _ -> VBuiltin (op, args'))
  | VNeutral n ->
      VNeutral (NApp (n, [arg]))
  | _ -> VNeutral (NApp (NVar "_stuck_", [f; arg]))

(** Evaluate a pattern match. *)
and eval_match (ctx : context) (env : env) (scrut : value) (cases : case list) : value =
  match scrut with
  | VConstructor (ctor_name, args) -> (
      match List.find_opt (fun c -> String.equal c.pattern.ctor ctor_name) cases with
      | Some case ->
          let pat_args = List.map (fun a -> a.arg_name) case.pattern.args in
          let num_pat_args = List.length pat_args in
          let num_ctor_args = List.length args in
          (* Skip type parameters: constructor args include params, pattern args don't *)
          let field_args =
            let skip = num_ctor_args - num_pat_args in
            let rec drop n xs =
              match n, xs with
              | 0, _ -> xs
              | k, _ :: ys -> drop (k - 1) ys
              | _, [] -> []
            in
            drop skip args
          in
          let bindings = List.combine pat_args field_args in
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
  | VSubset { arg; pred; env = _ } -> mk ?loc:arg.b_loc (Subset { arg; pred })
  | VArray { elem_ty; size } -> mk (Array { elem_ty = quote elem_ty; size = quote size })
  | VArrayHandle { elem_ty; size } -> mk (ArrayHandle { elem_ty = quote elem_ty; size = quote size })
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
  | VArray { elem_ty=t1; size=s1 }, VArray { elem_ty=t2; size=s2 } ->
      value_eq t1 t2 && value_eq s1 s2
  | VArrayHandle { elem_ty=t1; size=s1 }, VArrayHandle { elem_ty=t2; size=s2 } ->
      value_eq t1 t2 && value_eq s1 s2
  | _ -> false


