(** JSON parser for CertiJSON modules using Jsonm (location-aware scanning).
    
    This module parses JSON files into the abstract syntax defined in {!Syntax}. *)

open Syntax
module Loc = Loc

(** {1 Error Types} *)

type parse_error =
  | MissingField of string
  | InvalidNodeKind of string
  | InvalidValue of string * string  (* field, message *)
  | UnexpectedType of string * string  (* expected, got *)
  | JsonError of string
[@@deriving show]

exception ParseError of parse_error

(** {1 Lightweight JSON AST} *)

type range = (int * int) * (int * int)

type json = {
  loc : range;
  value : json_value;
}

and json_value =
  | JObject of (string * json) list
  | JArray of json list
  | JString of string
  | JFloat of float
  | JBool of bool
  | JNull

let json_to_string (j : json) =
  match j.value with
  | JObject _ -> "<object>"
  | JArray _ -> "<array>"
  | JString s -> Printf.sprintf "\"%s\"" s
  | JFloat f -> string_of_float f
  | JBool b -> string_of_bool b
  | JNull -> "null"

(** {1 Jsonm decoding} *)

let parse_error_of_jsonm err =
  let msg = Format.asprintf "%a" Jsonm.pp_error err in
  ParseError (JsonError msg)

let combine_range ((s1, c1), _) (_, (e2, c2)) = ((s1, c1), (e2, c2))

let next dec =
  match Jsonm.decode dec with
  | `Lexeme l -> (
      let r = Jsonm.decoded_range dec in
      (l, r))
  | `Error e -> raise (parse_error_of_jsonm e)
  | `End -> raise (ParseError (JsonError "unexpected end of input"))
  | `Await -> assert false

let rec decode_value dec : json =
  let lex, range = next dec in
  match lex with
  | `Os -> decode_object dec range []
  | `As -> decode_array dec range []
  | `Null -> { loc = range; value = JNull }
  | `Bool b -> { loc = range; value = JBool b }
  | `String s -> { loc = range; value = JString s }
  | `Float f -> { loc = range; value = JFloat f }
  | `Name _ -> raise (ParseError (UnexpectedType ("value", "name")))
  | `Ae | `Oe -> raise (ParseError (JsonError "unexpected array/object end"))

and decode_object dec start_range acc =
  let lex, range = next dec in
  match lex with
  | `Name n ->
      let v = decode_value dec in
      decode_object dec start_range ((n, v) :: acc)
  | `Oe ->
      { loc = combine_range start_range range; value = JObject (List.rev acc) }
  | _ -> raise (ParseError (JsonError "invalid object lexeme"))

and decode_array dec start_range acc =
  let lex, range = next dec in
  match lex with
  | `Ae -> { loc = combine_range start_range range; value = JArray (List.rev acc) }
  | `Os ->
      let v = decode_object dec range [] in
      decode_array dec start_range (v :: acc)
  | `As ->
      let v = decode_array dec range [] in
      decode_array dec start_range (v :: acc)
  | `Null -> decode_array dec start_range ({ loc = range; value = JNull } :: acc)
  | `Bool b -> decode_array dec start_range ({ loc = range; value = JBool b } :: acc)
  | `String s -> decode_array dec start_range ({ loc = range; value = JString s } :: acc)
  | `Float f -> decode_array dec start_range ({ loc = range; value = JFloat f } :: acc)
  | `Name _ -> raise (ParseError (UnexpectedType ("value", "name")))
  | `Oe -> raise (ParseError (JsonError "unexpected array/object end"))

let decode_json_string (s : string) : json =
  let dec = Jsonm.decoder (`String s) in
  decode_value dec

(** {1 Helper Functions} *)

let get_field (json : json) (field : string) : json =
  match json.value with
  | JObject fields -> (
      match List.assoc_opt field fields with
      | Some v -> v
      | None -> raise (ParseError (MissingField field)))
  | _ -> raise (ParseError (UnexpectedType ("object", json_to_string json)))

let get_field_opt (json : json) (field : string) : json option =
  match json.value with
  | JObject fields -> List.assoc_opt field fields
  | _ -> None

let get_string (json : json) : string =
  match json.value with
  | JString s -> s
  | _ -> raise (ParseError (UnexpectedType ("string", json_to_string json)))

let get_int (json : json) : int =
  match json.value with
  | JFloat f -> int_of_float f
  | _ -> raise (ParseError (UnexpectedType ("int", json_to_string json)))

let get_float (json : json) : float =
  match json.value with
  | JFloat f -> f
  | _ -> raise (ParseError (UnexpectedType ("float", json_to_string json)))

let get_bool (json : json) : bool =
  match json.value with
  | JBool b -> b
  | _ -> raise (ParseError (UnexpectedType ("bool", json_to_string json)))

let get_list (json : json) : json list =
  match json.value with
  | JArray l -> l
  | _ -> raise (ParseError (UnexpectedType ("list", json_to_string json)))

let has_field (json : json) (field : string) : bool =
  match json.value with
  | JObject fields -> List.mem_assoc field fields
  | _ -> false

let parse_role (s : string) : role =
  match s with
  | "runtime" -> Runtime
  | "proof-only" | "proof_only" -> ProofOnly
  | "both" -> Both
  | _ -> raise (ParseError (InvalidValue ("role", s)))

(** {1 Term Parsing} *)

let rec parse_term ~(file : string option) (json : json) : term =
  let loc = Some (Loc.loc_of_range ?file json.loc) in
  match json with
  | _ when has_field json "var" ->
      { desc = Var (get_string (get_field json "var")); loc }
  | _ when has_field json "universe" ->
      let u = get_string (get_field json "universe") in
      {
        desc =
          Universe
            (match u with
            | "Type" -> Type
            | "Prop" -> Prop
            | _ -> raise (ParseError (InvalidValue ("universe", u))));
        loc;
      }
  | _ when has_field json "prim" ->
      let p = get_string (get_field json "prim") in
      {
        desc =
          PrimType
            (match p with
            | "Int32" -> Int32
            | "Int64" -> Int64
            | "Float64" -> Float64
            | "Bool" -> Bool
            | "String" -> String
            | "Size" -> Size
            | _ -> raise (ParseError (InvalidValue ("prim", p))));
        loc;
      }
  | _ when has_field json "pi" ->
      let pi = get_field json "pi" in
      let arg_json = get_field pi "arg" in
      let arg =
        {
          name = get_string (get_field arg_json "name");
          ty = parse_term ~file (get_field arg_json "type");
          role = (match get_field_opt arg_json "role" with
                  | Some j -> (match j.value with JString s -> parse_role s | _ -> Runtime)
                  | None -> Runtime);
          b_loc = loc;
        }
      in
      let result = parse_term ~file (get_field pi "result") in
      { desc = Pi { arg; result }; loc }
  | _ when has_field json "forall" ->
      let forall = get_field json "forall" in
      let arg_json = get_field forall "arg" in
      let arg =
        {
          name = get_string (get_field arg_json "name");
          ty = parse_term ~file (get_field arg_json "type");
          role = (match get_field_opt arg_json "role" with
                  | Some j -> (match j.value with JString s -> parse_role s | _ -> Runtime)
                  | None -> Runtime);
          b_loc = loc;
        }
      in
      let result = parse_term ~file (get_field forall "result") in
      { desc = Pi { arg; result }; loc }
  | _ when has_field json "lambda" ->
      let lam = get_field json "lambda" in
      let arg_json = get_field lam "arg" in
      let arg =
        {
          name = get_string (get_field arg_json "name");
          ty = parse_term ~file (get_field arg_json "type");
          role = (match get_field_opt arg_json "role" with
                  | Some j -> (match j.value with JString s -> parse_role s | _ -> Runtime)
                  | None -> Runtime);
          b_loc = loc;
        }
      in
      let body = parse_term ~file (get_field lam "body") in
      { desc = Lambda { arg; body }; loc }
  | _ when has_field json "subset" ->
      let sub = get_field json "subset" in
      let arg_json = get_field sub "arg" in
      let arg =
        {
          name = get_string (get_field arg_json "name");
          ty = parse_term ~file (get_field arg_json "type");
          role = Runtime;
          b_loc = loc;
        }
      in
      let pred = parse_term ~file (get_field sub "pred") in
      { desc = Subset { arg; pred }; loc }
  | _ when has_field json "subset_intro" ->
      let intro = get_field json "subset_intro" in
      {
        desc =
          SubsetIntro
            {
              value = parse_term ~file (get_field intro "value");
              proof = parse_term ~file (get_field intro "proof");
            };
        loc;
      }
  | _ when has_field json "subset_elim" ->
      let elim = get_field json "subset_elim" in
      let value = parse_term ~file (get_field elim "value") in
      { desc = SubsetElim value; loc }
  | _ when has_field json "subset_proof" ->
      let proof = get_field json "subset_proof" in
      let value = parse_term ~file (get_field proof "value") in
      { desc = SubsetProof value; loc }
  | _ when has_field json "array" ->
      let arr = get_field json "array" in
      {
        desc =
          Array
            {
              elem_ty = parse_term ~file (get_field arr "type");
              size = parse_term ~file (get_field arr "size");
            };
        loc;
      }
  | _ when has_field json "array_handle" ->
      let arr = get_field json "array_handle" in
      {
        desc =
          ArrayHandle
            {
              elem_ty = parse_term ~file (get_field arr "type");
              size = parse_term ~file (get_field arr "size");
            };
        loc;
      }
  | _ when has_field json "app" ->
      let apps = get_list (get_field json "app") in
      (match apps with
      | [] -> raise (ParseError (InvalidValue ("app", "empty application list")))
      | [ _ ] ->
          raise (ParseError (InvalidValue ("app", "application needs at least 2 terms")))
      | f :: args ->
          {
            desc = App (parse_term ~file f, List.map (parse_term ~file) args);
            loc;
          })
  | _ when has_field json "eq" ->
      let eq = get_field json "eq" in
      {
        desc =
          Eq
            {
              ty = parse_term ~file (get_field eq "type");
              lhs = parse_term ~file (get_field eq "lhs");
              rhs = parse_term ~file (get_field eq "rhs");
            };
        loc;
      }
  | _ when has_field json "refl" ->
      let refl = get_field json "refl" in
      let eq = get_field refl "eq" in
      {
        desc =
          Refl
            {
              ty = parse_term ~file (get_field eq "type");
              value = parse_term ~file (get_field eq "lhs");
            };
        loc;
      }
  | _ when has_field json "rewrite" ->
      let rw = get_field json "rewrite" in
      {
        desc =
          Rewrite
            {
              proof = parse_term ~file (get_field rw "proof");
              body = parse_term ~file (get_field rw "in");
            };
        loc;
      }
  | _ when has_field json "if" ->
      let if_ = get_field json "if" in
      {
        desc =
          If
            {
              cond = parse_term ~file (get_field if_ "cond");
              then_ = parse_term ~file (get_field if_ "then");
              else_ = parse_term ~file (get_field if_ "else");
            };
        loc;
      }
  | _ when has_field json "match" ->
      let m = get_field json "match" in
      let scrutinee = parse_term ~file (get_field m "scrutinee") in
      let motive = parse_term ~file (get_field m "motive") in
      let as_name = Option.map get_string (get_field_opt m "as") in
      let cases = List.map (parse_case ~file) (get_list (get_field m "cases")) in
      let coverage_hint =
        match get_field_opt m "coverage_hint" with
        | Some j -> (
            match j.value with
            | JString "complete" -> Complete
            | _ -> Unknown)
        | None -> Unknown
      in
      { desc = Match { scrutinee; motive; as_name; cases; coverage_hint }; loc }
  | _ when has_field json "int32" ->
      { desc = Literal (LitInt32 (Int32.of_int (get_int (get_field json "int32")))); loc }
  | _ when has_field json "int64" ->
      { desc = Literal (LitInt64 (Int64.of_int (get_int (get_field json "int64")))); loc }
  | _ when has_field json "float64" ->
      { desc = Literal (LitFloat64 (get_float (get_field json "float64"))); loc }
  | _ when has_field json "bool" ->
      { desc = Literal (LitBool (get_bool (get_field json "bool"))); loc }
  | _ when has_field json "string" ->
      { desc = Literal (LitString (get_string (get_field json "string"))); loc }
  | _ ->
      raise (ParseError (InvalidNodeKind (json_to_string json)))

and parse_case ~(file : string option) (json : json) : case =
  let pat_json = get_field json "pattern" in
  let ctor = get_string (get_field pat_json "ctor") in
  let args =
    match get_field_opt pat_json "args" with
    | Some args_json ->
        List.map
          (fun a -> { arg_name = get_string (get_field a "name"); arg_loc = Some (Loc.loc_of_range ?file a.loc) })
          (get_list args_json)
    | None -> []
  in
  let body = parse_term ~file (get_field json "body") in
  {
    pattern = { ctor; args; pat_loc = Some (Loc.loc_of_range ?file pat_json.loc) };
    body;
    case_loc = Some (Loc.loc_of_range ?file json.loc);
  }

(** {1 Binder Parsing} *)

let parse_binder ~(file : string option) (json : json) : binder =
  {
    name = get_string (get_field json "name");
    ty = parse_term ~file (get_field json "type");
    role = (match get_field_opt json "role" with
            | Some j -> (match j.value with JString s -> parse_role s | _ -> Runtime)
            | None -> Runtime);
    b_loc = Some (Loc.loc_of_range ?file json.loc);
  }

(** {1 Declaration Parsing} *)

let parse_inductive ~(file : string option) (json : json) : inductive_decl =
  let name = get_string (get_field json "name") in
  let params =
    match get_field_opt json "params" with
    | Some ps -> List.map (parse_binder ~file) (get_list ps)
    | None -> []
  in
  let universe =
    match get_string (get_field json "universe") with
    | "Type" -> Type
    | "Prop" -> Prop
    | u -> raise (ParseError (InvalidValue ("universe", u)))
  in
  let constructors =
    List.map
      (fun c ->
        let ctor_name = get_string (get_field c "name") in
        let ctor_args =
          match get_field_opt c "args" with
          | Some args -> List.map (parse_binder ~file) (get_list args)
          | None -> []
        in
        { ctor_name; ctor_args; ctor_loc = Some (Loc.loc_of_range ?file c.loc) })
      (get_list (get_field json "constructors"))
  in
  { ind_name = name; params; ind_universe = universe; constructors; ind_loc = Some (Loc.loc_of_range ?file json.loc) }

let parse_def ~(file : string option) (json : json) : def_decl =
  let name = get_string (get_field json "name") in
  let role =
    match get_field_opt json "role" with
    | Some j -> (
        match j.value with
        | JString s -> parse_role s
        | _ -> Both)
    | None -> Both
  in
  let ty = parse_term ~file (get_field json "type") in
  let body = parse_term ~file (get_field json "body") in
  let rec_args =
    match get_field_opt json "rec_args" with
    | Some args -> Some (List.map get_int (get_list args))
    | None -> None
  in
  { def_name = name; def_role = role; def_type = ty; def_body = body; rec_args; def_loc = Some (Loc.loc_of_range ?file json.loc) }

let parse_theorem ~(file : string option) (json : json) : theorem_decl =
  let name = get_string (get_field json "name") in
  let ty = parse_term ~file (get_field json "type") in
  let proof = parse_term ~file (get_field json "proof") in
  { thm_name = name; thm_type = ty; thm_proof = proof; thm_loc = Some (Loc.loc_of_range ?file json.loc) }

let parse_repr ~(file : string option) (json : json) : repr_decl =
  let name = get_string (get_field json "name") in
  let kind_str = get_string (get_field json "kind") in
  let kind =
    match kind_str with
    | "primitive" ->
        Primitive
          {
            c_type = get_string (get_field json "c_type");
            size_bits = get_int (get_field json "size_bits");
            signed = get_bool (get_field json "signed");
          }
    | "struct" ->
        let fields =
          List.map
            (fun f ->
              {
                field_name = get_string (get_field f "name");
                field_repr = get_string (get_field f "repr");
                offset_bytes = get_int (get_field f "offset_bytes");
              })
            (get_list (get_field json "fields"))
        in
        Struct
          {
            c_struct_name = get_string (get_field json "c_struct_name");
            size_bytes = get_int (get_field json "size_bytes");
            align_bytes = get_int (get_field json "align_bytes");
            fields;
          }
    | _ -> raise (ParseError (InvalidValue ("kind", kind_str)))
  in
  { repr_name = name; kind; repr_loc = Some (Loc.loc_of_range ?file json.loc) }

let parse_extern_c ~(file : string option) (json : json) : extern_c_decl =
  let name = get_string (get_field json "name") in
  let c_name = get_string (get_field json "c_name") in
  let header = get_string (get_field json "header") in
  let sig_json = get_field json "signature" in
  let return_repr =
    match get_field_opt sig_json "return" with
    | Some r -> (
        match r.value with
        | JNull -> None
        | _ -> Some (get_string (get_field r "repr"))
      )
    | None -> None
  in
  let args =
    match get_field_opt sig_json "args" with
    | Some args_json ->
        List.map
          (fun a ->
            {
              extern_arg_name = get_string (get_field a "name");
              extern_arg_repr = get_string (get_field a "repr");
            })
          (get_list args_json)
    | None -> []
  in
  let logical_type = parse_term ~file (get_field json "type") in
  let safety =
    match get_field_opt json "safety" with
    | Some j -> (
        match j.value with
        | JString "pure" -> Pure
        | JString "impure" -> Impure
        | _ -> Pure)
    | None -> Pure
  in
  let axioms =
    match get_field_opt json "axioms" with
    | Some axs -> List.map get_string (get_list axs)
    | None -> []
  in
  { extern_name = name; c_name; header; return_repr; args; logical_type; safety; axioms; extern_loc = Some (Loc.loc_of_range ?file json.loc) }

let parse_extern_io ~(file : string option) (json : json) : extern_io_decl =
  let name = get_string (get_field json "name") in
  let c_name = get_string (get_field json "c_name") in
  let header = get_string (get_field json "header") in
  let args =
    match get_field_opt json "args" with
    | Some args_json ->
        List.map
          (fun a ->
            {
              extern_arg_name = get_string (get_field a "name");
              extern_arg_repr = get_string (get_field a "repr");
            })
          (get_list args_json)
    | None -> []
  in
  let result_repr =
    match get_field_opt json "result" with
    | Some j -> (
        match j.value with
        | JNull -> None
        | _ -> Some (get_string (get_field j "repr")))
    | None -> None
  in
  let logical_type = parse_term ~file (get_field json "type") in
  let pre_cond, post_cond =
    match get_field_opt json "spec" with
    | Some j ->
        let pre = Option.map get_string (get_field_opt j "pre") in
        let post = Option.map get_string (get_field_opt j "post") in
        (pre, post)
    | None -> (None, None)
  in
  { extern_io_name = name; c_name; header; args; result_repr; logical_type; pre_cond; post_cond; extern_io_loc = Some (Loc.loc_of_range ?file json.loc) }

let parse_declaration ~file (json : json) : declaration =
  if has_field json "inductive" then
    Inductive (parse_inductive ~file (get_field json "inductive"))
  else if has_field json "def" then
    Definition (parse_def ~file (get_field json "def"))
  else if has_field json "theorem" then
    Theorem (parse_theorem ~file (get_field json "theorem"))
  else if has_field json "repr" then
    Repr (parse_repr ~file (get_field json "repr"))
  else if has_field json "extern_c" then
    ExternC (parse_extern_c ~file (get_field json "extern_c"))
  else if has_field json "extern_io" then
    ExternIO (parse_extern_io ~file (get_field json "extern_io"))
  else
    raise (ParseError (InvalidNodeKind (json_to_string json)))

(** {1 Module Parsing} *)

let parse_module ~(file : string option) ?(loc_of_name = (fun _ -> None)) (json : json) : module_decl =
  let module_name = get_string (get_field json "module") in
  let imports =
    match get_field_opt json "imports" with
    | Some imps -> List.map get_string (get_list imps)
    | None -> []
  in
  let declarations =
    List.map (parse_declaration ~file) (get_list (get_field json "declarations"))
    |> List.map (function
           | Inductive ind ->
               Inductive
                 {
                   ind with
                   ind_loc = loc_of_name ind.ind_name;
                   constructors =
                     List.map
                       (fun c -> { c with ctor_loc = loc_of_name c.ctor_name })
                       ind.constructors;
                 }
           | Definition def ->
               Definition { def with def_loc = loc_of_name def.def_name }
           | Theorem thm ->
               Theorem { thm with thm_loc = loc_of_name thm.thm_name }
           | Repr repr ->
               Repr { repr with repr_loc = loc_of_name repr.repr_name }
           | ExternC ext ->
               ExternC { ext with extern_loc = loc_of_name ext.extern_name }
           | ExternIO ext ->
               ExternIO { ext with extern_io_loc = loc_of_name ext.extern_io_name })
  in
  let module_loc =
    match loc_of_name module_name with
    | Some l -> (
        match file with Some f -> Some (Loc.with_file f l) | None -> Some l)
    | None -> None
  in
  { module_name; imports; declarations; module_loc }

(** {1 Entry Points} *)

let parse_string (s : string) : (module_decl, parse_error) result =
  try
    let json = decode_json_string s in
    let loc_tbl = Loc.index_name_locations s in
    let loc_of_name name = Hashtbl.find_opt loc_tbl name in
    Ok (parse_module ~file:None ~loc_of_name json)
  with
  | ParseError e -> Error e
  | _ -> Error (JsonError "unknown JSON parse error")

let parse_file (filename : string) : (module_decl, parse_error) result =
  try
    let content =
      let ch = open_in_bin filename in
      let len = in_channel_length ch in
      let s = really_input_string ch len in
      close_in ch;
      s
    in
    let json = decode_json_string content in
    let loc_tbl = Loc.index_name_locations content in
    let loc_of_name name =
      match Hashtbl.find_opt loc_tbl name with
      | Some loc -> Some (Loc.with_file filename loc)
      | None -> None
    in
    Ok (parse_module ~file:(Some filename) ~loc_of_name json)
  with
  | ParseError e -> Error e
  | Sys_error msg -> Error (JsonError msg)
  | _ -> Error (JsonError "unknown JSON parse error")
