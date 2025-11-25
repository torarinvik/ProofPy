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

let rec translate_type (ctx : Context.context) (t : Syntax.term) : c_type =
  match t.desc with
  | PrimType p -> translate_prim_type p
  | Universe _ -> CVoid (* Erased *)
  | App ({ desc = Global "IO"; _ }, [arg]) ->
      (* IO A -> A (or void if A is Unit) *)
      translate_type ctx arg
  | Global "Unit" -> CVoid
  | Global name -> CUserType name (* Assuming struct or typedef exists *)
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

let extract_def (ctx : Context.context) (def : Syntax.def_decl) : c_func option =
  if def.def_role = Syntax.ProofOnly || returns_universe def.def_type then None
  else
    let ret_type = translate_type ctx def.def_type in
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
  let includes = ["<stdio.h>"; "<stdint.h>"; "<stdbool.h>"; "<certijson_io.h>"] in
  { includes; structs = []; funcs }

