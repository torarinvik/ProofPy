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
  | App (f, [arg]) when is_global "IO" f ->
      (* IO A -> A (or void if A is Unit) *)
      translate_type ctx arg
  | Global "Unit" | Var "Unit" -> CVoid
  | Global name | Var name -> 
      (match Context.lookup ctx name with
       | Some (`Global (GRepr _)) -> translate_repr ctx name
       | _ -> CUserType name)
  | _ -> CVoid (* Fallback *)

let rec translate_term (ctx : Context.context) (t : Syntax.term) : c_expr =
  match t.desc with
  | Literal (LitInt32 i) -> CLitInt32 i
  | Literal (LitInt64 i) -> CLitInt64 i
  | Literal (LitFloat64 f) -> CLitFloat f
  | Literal (LitBool b) -> CLitBool b
  | Literal (LitString s) -> CLitString s
  | Var x -> CVar x
  | App (f, args) -> (
      let name_opt =
        match f.desc with
        | Global n -> Some n
        | Var n -> Some n
        | _ -> None
      in
      match name_opt with
      | Some name -> (
          match Context.lookup ctx name with
          | Some (`Global (GExternIO ext)) ->
              CCall (ext.c_name, List.map (translate_term ctx) args)
          | Some (`Global (GExternC ext)) ->
              CCall (ext.c_name, List.map (translate_term ctx) args)
          | _ -> CCall (name, List.map (translate_term ctx) args)
        )
      | None -> CCall ("<indirect>", List.map (translate_term ctx) args)
    )
  | _ -> CVar "<unsupported>"

let rec returns_universe (t : Syntax.term) : bool =
  match t.desc with
  | Universe _ -> true
  | Pi { result; _ } -> returns_universe result
  | _ -> false

let rec translate_io (ctx : Context.context) (t : Syntax.term) (res_var : string option) : c_stmt list =
  let is_global name t =
    match t.desc with
    | Global n | Var n -> String.equal n name
    | _ -> false
  in
  match t.desc with
  | App (f, [_; _; m; lam]) when is_global "bind" f ->
      (match lam.desc with
       | Lambda { arg; body } ->
           let var_name = arg.name in (* TODO: fresh name *)
           let ty = translate_type ctx arg.ty in
           let res_var_for_m = if ty = CVoid then None else Some var_name in
           let m_stmts = translate_io ctx m res_var_for_m in
           let decl = 
             if ty = CVoid then [] 
             else [CDecl (ty, var_name, None)]
           in
           let f_stmts = translate_io ctx body res_var in
           m_stmts @ decl @ f_stmts
       | _ -> [CExpr (CVar "/* bind with non-lambda */")]
      )
  | App (f, [_; x]) when is_global "return" f ->
      (match res_var with
       | Some v -> [CExpr (CAssign (v, translate_term ctx x))]
       | None -> []
      )
  | App (_, _) ->
      let call = translate_term ctx t in
      (match res_var with
       | Some v -> [CExpr (CAssign (v, call))] 
       | None -> [CExpr call]
      )
  | _ -> 
      Format.eprintf "translate_io fallback: %a@." Syntax.pp_term t;
      [CExpr (translate_term ctx t)]

let extract_def (ctx : Context.context) (def : Syntax.def_decl) : c_func option =
  if def.def_role = Syntax.ProofOnly || returns_universe def.def_type then None
  else
    let ret_type = translate_type ctx def.def_type in
    let is_io = 
      match def.def_type.desc with
      | App (f, _) -> 
          (match f.desc with
           | Global "IO" | Var "IO" -> true
           | _ -> false)
      | _ -> false
    in
    if is_io then
      let body_stmts = translate_io ctx def.def_body None in
      if String.equal def.def_name "main" then
        Some {
          name = "main";
          ret_type = CInt32; (* int main *)
          args = [];
          body = CBlock (body_stmts @ [CReturn (CLitInt32 0l)]);
        }
      else
        Some {
          name = def.def_name;
          ret_type = CVoid; (* IO Unit -> void *)
          args = [];
          body = CBlock body_stmts;
        }
    else
      let body_expr = translate_term ctx def.def_body in
      let stmt =
        if ret_type = CVoid then CExpr body_expr
        else CReturn body_expr
      in
      Some {
        name = def.def_name;
        ret_type;
        args = []; (* TODO: Handle arguments *)
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
    let collect_includes acc = function
      | Syntax.ExternC { header; _ } -> if List.mem header acc then acc else header :: acc
      | Syntax.ExternIO { header; _ } -> if List.mem header acc then acc else header :: acc
      | _ -> acc
    in
    List.fold_left collect_includes [] mod_.declarations
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
  let includes = base_includes @ extra_includes in
  { includes; structs; funcs }

