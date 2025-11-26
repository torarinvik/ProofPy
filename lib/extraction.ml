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

type c_stmt =
  | CReturn of c_expr
  | CExpr of c_expr
  | CDecl of c_type * string * c_expr option
  | CBlock of c_stmt list
  | CIf of c_expr * c_stmt * c_stmt option

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
      Format.fprintf fmt "if (%a) %a" pp_c_expr cond pp_c_stmt then_;
      (match else_ with
      | Some e -> Format.fprintf fmt " else %a" pp_c_stmt e
      | None -> ())

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
  | App (f, [arg]) when is_global "IO" f ->
      (* IO A -> A (or void if A is Unit) *)
      translate_type ctx arg
  | Global "Unit" | Var "Unit" -> CVoid
  | Global name | Var name -> 
      (match Context.lookup ctx name with
       | Some (`Global (GRepr _)) -> translate_repr ctx name
       | _ -> CUserType name)
  | _ -> CVoid (* Fallback *)

let rec translate_term (ctx : Context.context) (env : (string * string) list) (t : Syntax.term) : c_expr =
  match t.desc with
  | Literal (LitInt32 i) -> CLitInt32 i
  | Literal (LitInt64 i) -> CLitInt64 i
  | Literal (LitFloat64 f) -> CLitFloat f
  | Literal (LitBool b) -> CLitBool b
  | Literal (LitString s) -> CLitString s
  | Var x -> (
      match List.assoc_opt x env with
      | Some fresh -> CVar fresh
      | None -> CVar x
    )
  | App (f, args) -> (
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
      | Some name -> (
          let args' = 
            List.map (translate_term ctx env) args 
            |> List.filter (function CVar "tt" -> false | _ -> true)
          in
          match Context.lookup ctx name with
          | Some (`Global (GExternIO ext)) ->
              CCall (ext.c_name, args')
          | Some (`Global (GExternC ext)) ->
              CCall (ext.c_name, args')
          | _ -> CCall (name, args')
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
      | App (f, [_; _; m; lam]) when is_global "bind" f ->
          (match lam.desc with
           | Lambda { arg; body } ->
               let var_name = fresh_name arg.name in
               let env' = (arg.name, var_name) :: env in
               let ty = translate_type ctx arg.ty in
               let res_var_for_m = if ty = CVoid then None else Some var_name in
               let m_stmts = translate_io ctx env m res_var_for_m CVoid in
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
                | _ -> [CReturn t])
          )
      | App (f, args) when (match f.desc with Global n | Var n -> String.contains n '.' && String.sub n (String.length n - 7) 7 = ".return" | _ -> false) ->
          (* Handle qualified return like Std.IO.return *)
          let actual_args = List.filter (fun a -> match a.desc with | Universe _ -> false | Var "Unit" | Global "Unit" -> false | _ -> true) args in
          (match actual_args with
           | [x] ->
               (match res_var with
                | Some v -> [CExpr (CAssign (v, translate_term ctx env x))]
                | None -> 
                    let t = translate_term ctx env x in
                    (match t with
                     | CVar "tt" -> [] (* return tt is a no-op *)
                     | _ -> [CReturn t]))
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
                      if ty = CVoid then []
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
      | Var name | Global name ->
          let call = CCall (name, []) in
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
          name = def.def_name;
          ret_type = ret_ty;
          args = c_args;
          body = CBlock body_stmts;
        }
    else
      let body_expr = translate_term ctx [] body in
      let stmt =
        if ret_type = CVoid then CExpr body_expr
        else CReturn body_expr
      in
      Some {
        name = def.def_name;
        ret_type;
        args = c_args;
        body = CBlock [stmt];
      }

let extract_module (mod_ : Syntax.module_decl) (sig_ : Context.signature) : c_program =
  let mod_sig = Context.build_signature mod_.declarations in
  let full_sig = Context.merge_signatures sig_ mod_sig in
  let ctx = Context.make_ctx full_sig in
  let funcs =
    List.filter_map (function
      | Syntax.Definition def -> extract_def ctx def
      | _ -> None
    ) mod_.declarations
  in
  let base_includes = ["<stdio.h>"; "<stdint.h>"; "<stdbool.h>"; "<certijson_io.h>"] in
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
  let includes = base_includes @ (List.filter (fun i -> not (List.mem i base_includes)) extra_includes) in
  { includes; structs; funcs }

