(** Extraction to C. *)

open Syntax
open Context

type c_type =
  | CVoid
  | CInt32
  | CInt64
  | CDouble
  | CBool
  | CString
  | CStruct of string
  | CPtr of c_type
  | CUserType of string

type c_expr =
  | CVar of string
  | CLitInt32 of int32
  | CLitInt64 of int64
  | CLitFloat of float
  | CLitBool of bool
  | CLitString of string
  | CCall of string * c_expr list
  | CAssign of string * c_expr
  | CTernary of c_expr * c_expr * c_expr
  | CBinOp of string * c_expr * c_expr
  | CUnOp of string * c_expr
  | CFieldAccess of c_expr * string

type c_stmt =
  | CReturn of c_expr
  | CExpr of c_expr
  | CDecl of c_type * string * c_expr option
  | CBlock of c_stmt list
  | CIf of c_expr * c_stmt * c_stmt option
  | CWhile of c_expr * c_stmt

type c_func = {
  name : string;
  ret_type : c_type;
  args : (c_type * string) list;
  body : c_stmt;
}

type c_program = {
  includes : string list;
  structs : string list; (* definitions *)
  funcs : c_func list;
}

let rec pp_c_type fmt = function
  | CVoid -> Format.fprintf fmt "void"
  | CInt32 -> Format.fprintf fmt "int32_t"
  | CInt64 -> Format.fprintf fmt "int64_t"
  | CDouble -> Format.fprintf fmt "double"
  | CBool -> Format.fprintf fmt "bool"
  | CString -> Format.fprintf fmt "char*"
  | CStruct s -> Format.fprintf fmt "struct %s" s
  | CPtr t -> Format.fprintf fmt "%a*" pp_c_type t
  | CUserType s -> Format.fprintf fmt "%s" s

let rec pp_c_expr fmt = function
  | CVar s -> Format.fprintf fmt "%s" s
  | CLitInt32 i -> Format.fprintf fmt "%ld" i
  | CLitInt64 i -> Format.fprintf fmt "%LdLL" i
  | CLitFloat f -> Format.fprintf fmt "%f" f
  | CLitBool b -> Format.fprintf fmt "%s" (if b then "true" else "false")
  | CLitString s -> Format.fprintf fmt "\"%s\"" (String.escaped s)
  | CCall (f, args) ->
      Format.fprintf fmt "%s(%a)" f
        (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ") pp_c_expr) args
  | CAssign (v, e) -> Format.fprintf fmt "%s = %a" v pp_c_expr e
  | CTernary (c, t, e) -> Format.fprintf fmt "(%a ? %a : %a)" pp_c_expr c pp_c_expr t pp_c_expr e
  | CBinOp (op, l, r) -> Format.fprintf fmt "(%a %s %a)" pp_c_expr l op pp_c_expr r
  | CUnOp (op, e) -> Format.fprintf fmt "(%s%a)" op pp_c_expr e
  | CFieldAccess (e, f) -> Format.fprintf fmt "%a.%s" pp_c_expr e f

(* Print expression without outer parens for use in if/while conditions *)
let pp_c_expr_cond fmt = function
  | CBinOp (op, l, r) -> Format.fprintf fmt "%a %s %a" pp_c_expr l op pp_c_expr r
  | e -> pp_c_expr fmt e

let rec pp_c_stmt fmt = function
  | CReturn e -> Format.fprintf fmt "return %a;" pp_c_expr e
  | CExpr e -> Format.fprintf fmt "%a;" pp_c_expr e
  | CDecl (ty, name, init) ->
      (match init with
      | Some e -> Format.fprintf fmt "%a %s = %a;" pp_c_type ty name pp_c_expr e
      | None -> Format.fprintf fmt "%a %s;" pp_c_type ty name)
  | CBlock stmts ->
      Format.fprintf fmt "{@\n%a@\n}"
        (Format.pp_print_list ~pp_sep:Format.pp_print_cut pp_c_stmt) stmts
  | CIf (cond, then_, else_) ->
      Format.fprintf fmt "if (%a) %a" pp_c_expr_cond cond pp_c_stmt then_;
      (match else_ with
      | Some e -> Format.fprintf fmt " else %a" pp_c_stmt e
      | None -> ())
  | CWhile (cond, body) ->
      Format.fprintf fmt "while (%a) %a" pp_c_expr_cond cond pp_c_stmt body

let pp_c_func_sig fmt f =
  Format.fprintf fmt "%a %s(%a);"
    pp_c_type f.ret_type
    f.name
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
       (fun fmt (ty, name) -> Format.fprintf fmt "%a %s" pp_c_type ty name))
    f.args

let pp_c_func fmt f =
  Format.fprintf fmt "%a %s(%a) %a"
    pp_c_type f.ret_type
    f.name
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
       (fun fmt (ty, name) -> Format.fprintf fmt "%a %s" pp_c_type ty name))
    f.args
    pp_c_stmt f.body

let pp_c_program fmt p =
  List.iter (fun inc -> Format.fprintf fmt "#include %s@\n" inc) p.includes;
  Format.fprintf fmt "@\n";
  List.iter (fun s -> Format.fprintf fmt "%s@\n" s) p.structs;
  Format.fprintf fmt "@\n";
  List.iter (fun f -> Format.fprintf fmt "%a@\n" pp_c_func_sig f) p.funcs;
  Format.fprintf fmt "@\n";
  List.iter (fun f -> Format.fprintf fmt "%a@\n@\n" pp_c_func f) p.funcs

(* Extraction Logic *)

let mangle_name s =
  String.map (function '.' -> '_' | c -> c) s

let rec flatten_app t args =
  match t.desc with
  | App (f, args') -> flatten_app f (args' @ args)
  | _ -> (t, args)

let list_take_last n l =
  let len = List.length l in
  if len <= n then l
  else
    let rec drop k l =
      if k <= 0 then l
      else match l with [] -> [] | _ :: t -> drop (k - 1) t
    in
    drop (len - n) l

let rec string_of_c_type = function
  | CVoid -> "void"
  | CInt32 -> "Int32"
  | CInt64 -> "Int64"
  | CDouble -> "Double"
  | CBool -> "Bool"
  | CString -> "String"
  | CStruct s -> s
  | CPtr t -> "Ptr_" ^ string_of_c_type t
  | CUserType s -> s

let pair_registry : (string, (c_type * c_type)) Hashtbl.t = Hashtbl.create 10

let get_pair_struct_name ta tb =
  let name = "Pair_" ^ string_of_c_type ta ^ "_" ^ string_of_c_type tb in
  if not (Hashtbl.mem pair_registry name) then
    Hashtbl.add pair_registry name (ta, tb);
  name

let translate_prim_type = function
  | Syntax.Int32 -> CInt32
  | Syntax.Int64 -> CInt64
  | Syntax.Float64 -> CDouble
  | Syntax.Bool -> CBool
  | Syntax.String -> CString
  | Syntax.Size -> CInt64 (* Approximation *)

let translate_repr (ctx : Context.context) (name : string) : c_type =
  match Context.lookup ctx name with
  | Some (`Global (GRepr { kind = Primitive { c_type; _ }; _ })) ->
      if String.equal c_type "int" then CInt32
      else if String.equal c_type "double" then CDouble
      else if String.equal c_type "char*" then CString
      else CUserType c_type
  | Some (`Global (GRepr { kind = Struct { c_struct_name; _ }; _ })) ->
      CStruct c_struct_name
  | _ -> CUserType name

let rec translate_type (ctx : Context.context) (t : Syntax.term) : c_type =
  let is_global name t =
    match t.desc with
    | Global n | Var n -> String.equal n name
    | _ -> false
  in
  match t.desc with
  | PrimType p -> translate_prim_type p
  | Universe _ -> CVoid (* Erased *)
  | Array _ -> CVoid (* Functional arrays are erased *)
  | ArrayHandle _ -> CInt64 (* Handles are int64 *)
  | App (f, args) ->
      if is_global "IO" f then
        match args with [arg] -> translate_type ctx arg | _ -> CVoid
      else if is_global "ArrayHandle" f then
        CInt64
      else if is_global "ArrayView" f then
         match args with
         | [a; _] -> CPtr (translate_type ctx a)
         | _ -> CVoid
      else if is_global "Pair" f then
         match args with
         | [a; b] -> 
             let ca = translate_type ctx a in
             let cb = translate_type ctx b in
             CStruct (get_pair_struct_name ca cb)
         | _ -> CVoid
      else if is_global "Array" f then
        CVoid
      else
        CVoid (* Fallback *)
  | Global "Unit" | Var "Unit" -> CVoid
  | Subset { arg; _ } -> translate_type ctx arg.ty (* Refinement types extract to base type *)
  | Global name | Var name -> 
      (match Context.lookup ctx name with
       | Some (`Global (GRepr _)) -> translate_repr ctx name
       | Some (`Global (GDefinition def)) ->
           (* Check if this is a refinement type definition (nullary function returning Type) *)
           (match def.def_type.desc with
            | Universe Type ->
                (* This is a type alias/refinement - look at the body *)
                let body = def.def_body in
                (match body.desc with
                 | Subset { arg; _ } -> translate_type ctx arg.ty
                 | _ -> translate_type ctx body)
            | _ -> CUserType name)
       | _ -> CUserType name)
  | _ -> CVoid (* Fallback *)

let is_type (t : Syntax.term) : bool =
  match t.desc with
  | Universe _ -> true
  | PrimType _ -> true
  | Array _ -> true
  | ArrayHandle _ -> true
  | Global "Unit" -> true
  | Var "Unit" -> true
  | App (f, _) -> 
      (match f.desc with
       | Global "Pair" | Var "Pair" -> true
       | Global "List" | Var "List" -> true
       | Global "Option" | Var "Option" -> true
       | Global "Result" | Var "Result" -> true
       | Global "Either" | Var "Either" -> true
       | Global "Array" | Var "Array" -> true
       | Global "ArrayHandle" | Var "ArrayHandle" -> true
       | _ -> false)
  | _ -> false

let rec translate_term (ctx : Context.context) (env : (string * string) list) (t : Syntax.term) : c_expr =
  match t.desc with
  | Literal (LitInt32 i) -> CLitInt32 i
  | Literal (LitInt64 i) -> CLitInt64 i
  | Literal (LitFloat64 f) -> CLitFloat f
  | Literal (LitBool b) -> CLitBool b
  | Literal (LitString s) -> CLitString s
  | Var x -> (
      if String.equal x "tt" then CLitInt32 0l
      else
      match List.assoc_opt x env with
      | Some fresh -> CVar fresh
      | None -> CVar (mangle_name x)
    )
  | App _ -> (
      let (f, args) = flatten_app t [] in
      let name_opt =
        match f.desc with
        | Global n -> Some n
        | Var n -> Some n
        | _ -> None
      in
      match name_opt with
      | Some "add" -> (match args with [a; b] -> CBinOp ("+", translate_term ctx env a, translate_term ctx env b) | _ -> CVar "<invalid_add>")
      | Some "sub" -> (match args with [a; b] -> CBinOp ("-", translate_term ctx env a, translate_term ctx env b) | _ -> CVar "<invalid_sub>")
      | Some "mul" -> (match args with [a; b] -> CBinOp ("*", translate_term ctx env a, translate_term ctx env b) | _ -> CVar "<invalid_mul>")
      | Some "Std.Int.mul64" | Some "mul64" | Some "mul64_builtin" -> (match args with [a; b] -> CBinOp ("*", translate_term ctx env a, translate_term ctx env b) | _ -> CVar "<invalid_mul64>")
      | Some "Std.Int.add64" | Some "add64" | Some "add64_builtin" -> (match args with [a; b] -> CBinOp ("+", translate_term ctx env a, translate_term ctx env b) | _ -> CVar "<invalid_add64>")
      | Some "Std.Int.sub64" | Some "sub64" | Some "sub64_builtin" -> (match args with [a; b] -> CBinOp ("-", translate_term ctx env a, translate_term ctx env b) | _ -> CVar "<invalid_sub64>")
      | Some "Std.Int.div64" | Some "div64" | Some "div64_builtin" -> (match args with [a; b] -> CBinOp ("/", translate_term ctx env a, translate_term ctx env b) | _ -> CVar "<invalid_div64>")
      | Some "div" -> (match args with [a; b] -> CBinOp ("/", translate_term ctx env a, translate_term ctx env b) | _ -> CVar "<invalid_div>")
      | Some "lt" -> (match args with [a; b] -> CBinOp ("<", translate_term ctx env a, translate_term ctx env b) | _ -> CVar "<invalid_lt>")
      | Some "gt" -> (match args with [a; b] -> CBinOp (">", translate_term ctx env a, translate_term ctx env b) | _ -> CVar "<invalid_gt>")
      | Some "eq" -> (match args with [a; b] -> CBinOp ("==", translate_term ctx env a, translate_term ctx env b) | _ -> CVar "<invalid_eq>")
      | Some "le" -> (match args with [a; b] -> CBinOp ("<=", translate_term ctx env a, translate_term ctx env b) | _ -> CVar "<invalid_le>")
      | Some "ge" -> (match args with [a; b] -> CBinOp (">=", translate_term ctx env a, translate_term ctx env b) | _ -> CVar "<invalid_ge>")
      | Some "ne" -> (match args with [a; b] -> CBinOp ("!=", translate_term ctx env a, translate_term ctx env b) | _ -> CVar "<invalid_ne>")
      | Some "mod" -> (match args with [a; b] -> CBinOp ("%", translate_term ctx env a, translate_term ctx env b) | _ -> CVar "<invalid_mod>")
      | Some "and" -> (match args with [a; b] -> CBinOp ("&&", translate_term ctx env a, translate_term ctx env b) | _ -> CVar "<invalid_and>")
      | Some "or" -> (match args with [a; b] -> CBinOp ("||", translate_term ctx env a, translate_term ctx env b) | _ -> CVar "<invalid_or>")
      | Some "not" -> (match args with [a] -> CUnOp ("!", translate_term ctx env a) | _ -> CVar "<invalid_not>")
      | Some "neg" -> (match args with [a] -> CUnOp ("-", translate_term ctx env a) | _ -> CVar "<invalid_neg>")
      | Some "fst" -> (
          let args' = args |> List.filter (fun a -> not (is_type a)) |> List.map (translate_term ctx env) |> List.filter (function CVar "tt" -> false | _ -> true) in
          match args' with [p] -> CFieldAccess (p, "fst") | _ -> CVar "<invalid_fst>")
      | Some "snd" -> (
          let args' = args |> List.filter (fun a -> not (is_type a)) |> List.map (translate_term ctx env) |> List.filter (function CVar "tt" -> false | _ -> true) in
          match args' with [p] -> CFieldAccess (p, "snd") | _ -> CVar "<invalid_snd>")
      | Some name -> (
          let args' = 
            args
            |> List.filter (fun a -> not (is_type a))
            |> List.map (translate_term ctx env) 
            |> List.filter (function CVar "tt" -> false | _ -> true)
          in
          match Context.lookup ctx name with
          | Some (`Global (GExternIO ext)) ->
              let args_len = List.length ext.args in
              let args_to_pass = list_take_last args_len args' in
              CCall (ext.c_name, args_to_pass)
          | Some (`Global (GExternC ext)) ->
              let args_len = List.length ext.args in
              let args_to_pass = list_take_last args_len args' in
              CCall (ext.c_name, args_to_pass)
          | _ -> CCall (mangle_name name, args')
        )
      | None -> CCall ("<indirect>", List.map (translate_term ctx env) args)
    )
  | If { cond; then_; else_ } ->
      CTernary (translate_term ctx env cond, translate_term ctx env then_, translate_term ctx env else_)
  | _ -> CVar "<unsupported>"

let rec returns_universe (t : Syntax.term) : bool =
  match t.desc with
  | Universe _ -> true
  | Pi { result; _ } -> returns_universe result
  | _ -> false

let rec collect_args_and_body (t : Syntax.term) : (string * Syntax.term) list * Syntax.term =
  match t.desc with
  | Lambda { arg; body } ->
      let args, body' = collect_args_and_body body in
      ((arg.name, arg.ty) :: args, body')
  | _ -> ([], t)

let rec get_return_type (t : Syntax.term) : Syntax.term =
  match t.desc with
  | Pi { result; _ } -> get_return_type result
  | _ -> t

let extract_def (ctx : Context.context) (def : Syntax.def_decl) : c_func option =
  if def.def_role = Syntax.ProofOnly || returns_universe def.def_type 
     || String.equal def.def_name "bind" || String.equal def.def_name "return" then None
  else
    let args, body = collect_args_and_body def.def_body in
    let c_args = 
      List.map (fun (n, ty) -> (translate_type ctx ty, n)) args 
      |> List.filter (fun (ty, _) -> ty <> CVoid)
    in
    let return_type = get_return_type def.def_type in
    let ret_type = translate_type ctx return_type in
    
    let is_io = 
      match return_type.desc with
      | App (f, _) -> 
          (match f.desc with
           | Global "IO" | Var "IO" -> true
           | _ -> false)
      | _ -> false
    in

    let counter = ref 0 in
    let fresh_name base =
      incr counter;
      Printf.sprintf "%s_%d" base !counter
    in

    let rec translate_io (ctx : Context.context) (env : (string * string) list) (t : Syntax.term) (res_var : string option) (ret_ty : c_type) : c_stmt list =
      let is_global name t =
        match t.desc with
        | Global n | Var n -> String.equal n name
        | _ -> false
      in
      match t.desc with
      | App (f, args) when is_global "Std.SafeMemory.stack_alloc" f || is_global "stack_alloc" f ->
          (match args with
           | [_; n_term; _; callback] ->
               (match callback.desc with
                | Lambda { arg; body } ->
                    let var_name = fresh_name arg.name in
                    let env' = (arg.name, var_name) :: env in
                    let n_expr = translate_term ctx env n_term in
                    (* Use calloc(n, 4) for Int32. TODO: Handle other types *)
                    let alloc_stmt = CDecl (CInt64, var_name, Some (CUnOp ("(int64_t)", CCall ("calloc", [n_expr; CLitInt32 4l])))) in
                    let free_stmt = CExpr (CCall ("free", [CUnOp ("(void*)", CVar var_name)])) in
                    let (res_var_for_body, ret_decl, ret_stmt) =
                      match res_var with
                      | None when ret_ty <> CVoid ->
                          let tmp = fresh_name "res" in
                          (Some tmp, [CDecl (ret_ty, tmp, None)], [CReturn (CVar tmp)])
                      | _ -> (res_var, [], [])
                    in
                    let body_stmts = translate_io ctx env' body res_var_for_body ret_ty in
                    alloc_stmt :: (ret_decl @ body_stmts @ [free_stmt] @ ret_stmt)
                | _ -> [CExpr (CVar "/* stack_alloc callback must be a lambda */")]
               )
           | _ -> [CExpr (CVar "/* invalid stack_alloc args */")]
          )
      | App (f, args) when is_global "Std.SafeMemory.as_view" f || is_global "as_view" f ->
          (match args with
           | [ty_arg; _; _; handle; callback] ->
               (match callback.desc with
                | Lambda { arg; body } ->
                    let var_name = fresh_name arg.name in
                    let env' = (arg.name, var_name) :: env in
                    let handle_expr = translate_term ctx env handle in
                    let elem_ty = translate_type ctx ty_arg in
                    let decl = CDecl (CPtr elem_ty, var_name, Some (CUnOp ("(void*)", handle_expr))) in

                    (* Determine second component type of the Pair result, if any. *)
                    let pair_name = string_of_c_type ret_ty in
                    let (_, ty_snd) =
                      match Hashtbl.find_opt pair_registry pair_name with
                      | Some p -> p
                      | None -> (CInt64, CVoid)
                    in

                    let body_stmts =
                      match res_var with
                      | Some v ->
                          (* Caller manages the struct; we just fill its fields. *)
                          let res_body_var = fresh_name "res_body" in
                          let res_var_for_body = if ty_snd = CVoid then None else Some res_body_var in
                          let body_stmts = translate_io ctx env' body res_var_for_body ty_snd in
                          let decl_res =
                            if ty_snd = CVoid then []
                            else [CDecl (ty_snd, res_body_var, None)]
                          in
                          let assign_stmt =
                            [
                              CExpr (CAssign (v ^ ".fst", handle_expr));
                              (if ty_snd <> CVoid then CExpr (CAssign (v ^ ".snd", CVar res_body_var)) else CExpr (CVar "/* unit snd */"));
                            ]
                          in
                          decl_res @ body_stmts @ assign_stmt
                      | None ->
                          (* We own the struct: create, fill, and return it. *)
                          let res_struct_var = fresh_name "res_struct" in
                          let decl_struct = CDecl (ret_ty, res_struct_var, None) in
                          let res_body_var = fresh_name "res_body" in
                          let res_var_for_body = if ty_snd = CVoid then None else Some res_body_var in
                          let body_stmts = translate_io ctx env' body res_var_for_body ty_snd in
                          let decl_res =
                            if ty_snd = CVoid then []
                            else [CDecl (ty_snd, res_body_var, None)]
                          in
                          let assign_stmt =
                            [
                              CExpr (CAssign (res_struct_var ^ ".fst", handle_expr));
                              (if ty_snd <> CVoid then CExpr (CAssign (res_struct_var ^ ".snd", CVar res_body_var)) else CExpr (CVar "/* unit snd */"));
                              CReturn (CVar res_struct_var);
                            ]
                          in
                          [decl_struct] @ decl_res @ body_stmts @ assign_stmt
                    in
                    [decl] @ body_stmts
                | _ -> [CExpr (CVar "/* as_view callback must be a lambda */")]
               )
           | _ -> [CExpr (CVar "/* invalid as_view args */")]
          )
      | App (f, [ty_a; _; m; lam]) when is_global "bind" f || (match f.desc with Global n | Var n -> String.ends_with ~suffix:".bind" n | _ -> false) ->
          (match lam.desc with
           | Lambda { arg; body } ->
               let var_name = fresh_name arg.name in
               let env' = (arg.name, var_name) :: env in
               let ty = translate_type ctx ty_a in
               let res_var_for_m = if ty = CVoid then None else Some var_name in
               let m_stmts = translate_io ctx env m res_var_for_m ty in
               let decl = 
                 if ty = CVoid then [] 
                 else [CDecl (ty, var_name, None)]
               in
               let f_stmts = translate_io ctx env' body res_var ret_ty in
               decl @ m_stmts @ f_stmts
           | _ -> [CExpr (CVar "/* bind with non-lambda */")]
          )
      | App (f, [_; x]) when is_global "return" f ->
          (match res_var with
           | Some v -> [CExpr (CAssign (v, translate_term ctx env x))]
           | None -> 
               let t = translate_term ctx env x in
               (match t with
                | CVar "tt" -> [] (* return tt is a no-op *)
                | CLitInt32 0l -> if ret_ty = CVoid then [] else [CReturn t]
                | _ -> [CReturn t])
          )
      | App (f, args) when (match f.desc with Global n | Var n -> String.contains n '.' && String.length n >= 7 && String.sub n (String.length n - 7) 7 = ".return" | _ -> false) ->
          (* Handle qualified return like Std.IO.return *)
          let actual_args = List.filter (fun a -> not (is_type a)) args in
          (match actual_args with
           | [x] ->
               (match res_var with
                | Some v -> [CExpr (CAssign (v, translate_term ctx env x))]
                | None -> 
                    let t = translate_term ctx env x in
                    if ret_ty = CVoid then [] else [CReturn t])
           | _ -> [] (* return with no real args is a no-op *))
      | App (_, _) ->
          (* Check for let-binding pattern: (λx.body) arg *)
          let is_let_binding () =
            match t.desc with
            | App (lam, [arg]) ->
                (match lam.desc with
                 | Lambda _ -> Some (lam, arg)
                 | _ -> None)
            | _ -> None
          in
          (match is_let_binding () with
           | Some (lam, arg) ->
               (match lam.desc with
                | Lambda { arg = binder; body } ->
                    let var_name = fresh_name binder.name in
                    let env' = (binder.name, var_name) :: env in
                    let ty = translate_type ctx binder.ty in
                    let arg_expr = translate_term ctx env arg in
                    let decl = 
                      if ty = CVoid then 
                        (* For void/Unit types, still execute the expression for side effects *)
                        [CExpr arg_expr]
                      else [CDecl (ty, var_name, Some arg_expr)]
                    in
                    let body_stmts = translate_io ctx env' body res_var ret_ty in
                    decl @ body_stmts
                | _ -> [CExpr (CVar "/* unexpected in let */")])
           | None ->
               let call = translate_term ctx env t in
               (match res_var with
                | Some v -> [CExpr (CAssign (v, call))] 
                | None -> 
                    if ret_ty <> CVoid then [CReturn call] else [CExpr call])
          )
      | If { cond; then_; else_ } ->
          let cond_expr = translate_term ctx env cond in
          let then_stmts = translate_io ctx env then_ res_var ret_ty in
          let else_stmts = translate_io ctx env else_ res_var ret_ty in
          let then_block = CBlock then_stmts in
          let else_block = match else_stmts with [] -> None | _ -> Some (CBlock else_stmts) in
          [CIf (cond_expr, then_block, else_block)]
      | While { cond; body } ->
          let cond_expr = translate_term ctx env cond in
          let body_stmts = translate_io ctx env body None CVoid in
          [CWhile (cond_expr, CBlock body_stmts)]
      | Assign { name; value } ->
          let val_expr = translate_term ctx env value in
          let var_name = 
            match List.assoc_opt name env with
            | Some v -> v
            | None -> name
          in
          [CExpr (CAssign (var_name, val_expr))]
      | Var name | Global name ->
          let call = CCall (mangle_name name, []) in
          (match res_var with
           | Some v -> [CExpr (CAssign (v, call))]
           | None -> 
               if ret_ty <> CVoid then [CReturn call] else [CExpr call])
      | _ -> 
          Format.eprintf "translate_io fallback: %a@." Syntax.pp_term t;
          [CExpr (translate_term ctx env t)]
    in
    
    if is_io then
      let ret_ty = 
        if String.equal def.def_name "main" then CInt32
        else
          match return_type.desc with
          | App (_, [arg]) -> translate_type ctx arg
          | _ -> CVoid
      in
      let body_ret_ty = if String.equal def.def_name "main" then CVoid else ret_ty in
      let body_stmts = translate_io ctx [] body None body_ret_ty in
      if String.equal def.def_name "main" then
        Some {
          name = "main";
          ret_type = CInt32; (* int main *)
          args = c_args;
          body = CBlock (body_stmts @ [CReturn (CLitInt32 0l)]);
        }
      else
        Some {
          name = mangle_name def.def_name;
          ret_type = ret_ty;
          args = c_args;
          body = CBlock body_stmts;
        }
    else
      (* Pure function - need to handle let-bindings *)
      let rec translate_pure (env : (string * string) list) (t : Syntax.term) (res_var : string option) (ret_ty : c_type) : c_stmt list =
        match t.desc with
        | Match { scrutinee; cases; _ } ->
            let scrut_expr = translate_term ctx env scrutinee in
            let is_bool_case c = 
              match c.pattern.ctor with 
              | "True" | "False" -> true 
              | _ -> false 
            in
            
            if List.exists is_bool_case cases then
              (* Convert to if/else chain *)
              let rec cases_to_if = function
                | [] -> []
                | c :: rest ->
                    let cond = 
                      if c.pattern.ctor = "True" then scrut_expr
                      else CUnOp ("!", scrut_expr)
                    in
                    let body_stmts = translate_pure env c.body res_var ret_ty in
                    let then_block = CBlock body_stmts in
                    let else_block = 
                      match rest with
                      | [] -> None
                      | _ -> Some (CBlock (cases_to_if rest)) (* This nests ifs, could be optimized *)
                    in
                    [CIf (cond, then_block, else_block)]
              in
              cases_to_if cases
            else
              (* Assume Int32 switch *)
              let switch_cases = 
                List.map (fun c ->
                  let val_expr = 
                    if c.pattern.ctor = "_" then None
                    else Some (CLitInt32 (Int32.of_string c.pattern.ctor))
                  in
                  (val_expr, translate_pure env c.body res_var ret_ty)
                ) cases
              in
              
              (* Check if there's a default case *)
              let has_default = List.exists (fun (v, _) -> v = None) switch_cases in
              
              let rec build_if_chain = function
                | [] -> []
                | (Some v, stmts) :: rest ->
                    let cond = CBinOp ("==", scrut_expr, v) in
                    let then_block = CBlock stmts in
                    let else_block = 
                      match build_if_chain rest with
                      | [] -> None
                      | else_stmts -> Some (CBlock else_stmts)
                    in
                    [CIf (cond, then_block, else_block)]
                | (None, stmts) :: _ -> stmts (* Default case *)
              in
              let if_chain = build_if_chain switch_cases in
              (* Add fallback return for non-void functions without default case *)
              if has_default || ret_ty = CVoid then
                if_chain
              else
                let fallback = 
                  match ret_ty with
                  | CInt32 -> [CReturn (CLitInt32 0l)]
                  | CInt64 -> [CReturn (CLitInt64 0L)]
                  | CDouble -> [CReturn (CLitFloat 0.0)]
                  | CBool -> [CReturn (CLitBool false)]
                  | _ -> [CReturn (CLitInt32 0l)]
                in
                if_chain @ fallback

        | App (lam, [arg]) ->
            (match lam.desc with
             | Lambda { arg = binder; body } ->
                 (* Let-binding pattern: (λx.body) arg *)
                 let var_name = fresh_name binder.name in
                 let env' = (binder.name, var_name) :: env in
                 let ty = translate_type ctx binder.ty in
                 
                 (* Check if this is a discarded binding (underscore pattern) *)
                 let is_discarded = String.equal binder.name "_" in
                 
                 (* Check if arg is complex *)
                 let arg_stmts, arg_init = 
                   match arg.desc with
                   | Match _ | If _ | App _ ->
                       (* Complex: generate statements to compute arg into var_name *)
                       (* But if ty is void or discarded, don't try to assign - just execute *)
                       if ty = CVoid || is_discarded then
                         (translate_pure env arg None CVoid, None)
                       else
                         (translate_pure env arg (Some var_name) ty, None)
                   | _ ->
                       (* Simple: use initializer, but if discarded just execute as expression *)
                       if is_discarded then
                         ([CExpr (translate_term ctx env arg)], None)
                       else
                         ([], Some (translate_term ctx env arg))
                 in
                 
                 let decl = 
                   if ty = CVoid || is_discarded then []
                   else [CDecl (ty, var_name, arg_init)]
                 in
                 decl @ arg_stmts @ translate_pure env' body res_var ret_ty
             | _ -> 
                 let body_expr = translate_term ctx env t in
                 match res_var with
                 | Some v -> [CExpr (CAssign (v, body_expr))]
                 | None -> 
                     if ret_ty = CVoid then
                       (* Skip generating "0;" for Unit values (tt) *)
                       match body_expr with
                       | CLitInt32 0l -> []
                       | _ -> [CExpr body_expr]
                     else [CReturn body_expr])
        | If { cond; then_; else_ } ->
            let cond_expr = translate_term ctx env cond in
            let then_stmts = translate_pure env then_ res_var ret_ty in
            let else_stmts = translate_pure env else_ res_var ret_ty in
            let then_block = CBlock then_stmts in
            let else_block = match else_stmts with [] -> None | _ -> Some (CBlock else_stmts) in
            [CIf (cond_expr, then_block, else_block)]
        | _ ->
            let body_expr = translate_term ctx env t in
            match res_var with
            | Some v -> [CExpr (CAssign (v, body_expr))]
            | None -> 
                if ret_ty = CVoid then
                  (* Skip generating "0;" for Unit values (tt) *)
                  match body_expr with
                  | CLitInt32 0l -> []
                  | _ -> [CExpr body_expr]
                else [CReturn body_expr]
      in
      let body_stmts = translate_pure [] body None ret_type in
      Some {
        name = mangle_name def.def_name;
        ret_type;
        args = c_args;
        body = CBlock body_stmts;
      }

let extract_module (mod_ : Syntax.module_decl) (sig_ : Context.signature) : c_program =
  Hashtbl.clear pair_registry;
  let mod_sig = Context.build_signature mod_.declarations in
  let full_sig = Context.merge_signatures sig_ mod_sig in
  let ctx = Context.make_ctx full_sig in
  let funcs =
    List.filter_map (function
      | Syntax.Definition def -> extract_def ctx def
      | _ -> None
    ) mod_.declarations
  in
  let base_includes = ["<stdio.h>"; "<stdlib.h>"; "<stdint.h>"; "<stdbool.h>"; "<certijson_io.h>"; "<certijson_memory.h>"] in
  let extra_includes =
    let collect_includes _ entry acc =
      match entry with
      | Context.GExternC { header; _ } -> if List.mem header acc then acc else header :: acc
      | Context.GExternIO { header; _ } -> if List.mem header acc then acc else header :: acc
      | _ -> acc
    in
    let incs = Hashtbl.fold collect_includes full_sig.entries [] in
    List.sort String.compare incs
  in
  let structs =
    List.filter_map (function
      | Syntax.Repr { kind = Struct { c_struct_name; fields; _ }; _ } ->
          let fields_str =
            List.map (fun f ->
              let ty = translate_repr ctx f.field_repr in
              Format.asprintf "%a %s;" pp_c_type ty f.field_name
            ) fields
            |> String.concat " "
          in
          Some (Printf.sprintf "struct %s { %s };" c_struct_name fields_str)
      | _ -> None
    ) mod_.declarations
  in
  let pair_structs = 
    Hashtbl.fold (fun name (ta, tb) acc ->
      let pp_field_type fmt ty =
        match ty with
        | CVoid -> Format.fprintf fmt "char" (* Dummy type for void fields *)
        | _ -> pp_c_type fmt ty
      in
      let s = Format.asprintf "struct %s { %a fst; %a snd; };" name pp_field_type ta pp_field_type tb in
      s :: acc
    ) pair_registry []
  in
  let structs = structs @ pair_structs in
  let includes = base_includes @ (List.filter (fun i -> not (List.mem i base_includes)) extra_includes) in
  { includes; structs; funcs }
