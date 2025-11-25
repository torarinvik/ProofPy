(** JSON parser for CertiJSON modules.
    
    This module parses JSON files into the abstract syntax defined in {!Syntax}. *)

open Syntax

(** {1 Error Types} *)

type parse_error =
  | MissingField of string
  | InvalidNodeKind of string
  | InvalidValue of string * string  (* field, message *)
  | UnexpectedType of string * string  (* expected, got *)
  | JsonError of string
[@@deriving show]

exception ParseError of parse_error

(** {1 Helper Functions} *)

let get_field (json : Yojson.Safe.t) (field : string) : Yojson.Safe.t =
  match json with
  | `Assoc fields -> (
      match List.assoc_opt field fields with
      | Some v -> v
      | None -> raise (ParseError (MissingField field)))
  | _ -> raise (ParseError (UnexpectedType ("object", Yojson.Safe.to_string json)))

let get_field_opt (json : Yojson.Safe.t) (field : string) : Yojson.Safe.t option =
  match json with
  | `Assoc fields -> List.assoc_opt field fields
  | _ -> None

let get_string (json : Yojson.Safe.t) : string =
  match json with
  | `String s -> s
  | _ -> raise (ParseError (UnexpectedType ("string", Yojson.Safe.to_string json)))

let get_int (json : Yojson.Safe.t) : int =
  match json with
  | `Int i -> i
  | _ -> raise (ParseError (UnexpectedType ("int", Yojson.Safe.to_string json)))

let get_float (json : Yojson.Safe.t) : float =
  match json with
  | `Float f -> f
  | `Int i -> Float.of_int i
  | _ -> raise (ParseError (UnexpectedType ("float", Yojson.Safe.to_string json)))

let get_bool (json : Yojson.Safe.t) : bool =
  match json with
  | `Bool b -> b
  | _ -> raise (ParseError (UnexpectedType ("bool", Yojson.Safe.to_string json)))

let get_list (json : Yojson.Safe.t) : Yojson.Safe.t list =
  match json with
  | `List l -> l
  | _ -> raise (ParseError (UnexpectedType ("list", Yojson.Safe.to_string json)))

let has_field (json : Yojson.Safe.t) (field : string) : bool =
  match json with
  | `Assoc fields -> List.mem_assoc field fields
  | _ -> false

(** {1 Term Parsing} *)

let rec parse_term (json : Yojson.Safe.t) : term =
  match json with
  | `Assoc _ when has_field json "var" ->
      Var (get_string (get_field json "var"))
  | `Assoc _ when has_field json "universe" ->
      let u = get_string (get_field json "universe") in
      Universe
        (match u with
        | "Type" -> Type
        | "Prop" -> Prop
        | _ -> raise (ParseError (InvalidValue ("universe", u))))
  | `Assoc _ when has_field json "pi" ->
      let pi = get_field json "pi" in
      let arg_json = get_field pi "arg" in
      let arg =
        {
          name = get_string (get_field arg_json "name");
          ty = parse_term (get_field arg_json "type");
        }
      in
      let result = parse_term (get_field pi "result") in
      Pi { arg; result }
  | `Assoc _ when has_field json "forall" ->
      (* Sugar for pi *)
      let forall = get_field json "forall" in
      let arg_json = get_field forall "arg" in
      let arg =
        {
          name = get_string (get_field arg_json "name");
          ty = parse_term (get_field arg_json "type");
        }
      in
      let result = parse_term (get_field forall "result") in
      Pi { arg; result }
  | `Assoc _ when has_field json "lambda" ->
      let lam = get_field json "lambda" in
      let arg_json = get_field lam "arg" in
      let arg =
        {
          name = get_string (get_field arg_json "name");
          ty = parse_term (get_field arg_json "type");
        }
      in
      let body = parse_term (get_field lam "body") in
      Lambda { arg; body }
  | `Assoc _ when has_field json "app" ->
      let apps = get_list (get_field json "app") in
      (match apps with
      | [] -> raise (ParseError (InvalidValue ("app", "empty application list")))
      | [ _ ] ->
          raise (ParseError (InvalidValue ("app", "application needs at least 2 terms")))
      | f :: args -> App (parse_term f, List.map parse_term args))
  | `Assoc _ when has_field json "eq" ->
      let eq = get_field json "eq" in
      Eq
        {
          ty = parse_term (get_field eq "type");
          lhs = parse_term (get_field eq "lhs");
          rhs = parse_term (get_field eq "rhs");
        }
  | `Assoc _ when has_field json "refl" ->
      let refl = get_field json "refl" in
      let eq = get_field refl "eq" in
      Refl
        {
          ty = parse_term (get_field eq "type");
          value = parse_term (get_field eq "lhs");
        }
  | `Assoc _ when has_field json "rewrite" ->
      let rw = get_field json "rewrite" in
      Rewrite
        {
          proof = parse_term (get_field rw "proof");
          body = parse_term (get_field rw "in");
        }
  | `Assoc _ when has_field json "match" ->
      let m = get_field json "match" in
      let scrutinee = parse_term (get_field m "scrutinee") in
      let motive = parse_term (get_field m "motive") in
      let as_name = Option.map get_string (get_field_opt m "as") in
      let cases = List.map parse_case (get_list (get_field m "cases")) in
      let coverage_hint =
        match get_field_opt m "coverage_hint" with
        | Some (`String "complete") -> Complete
        | _ -> Unknown
      in
      Match { scrutinee; motive; as_name; cases; coverage_hint }
  | `Assoc _ when has_field json "int32" ->
      Literal (LitInt32 (Int32.of_int (get_int (get_field json "int32"))))
  | `Assoc _ when has_field json "int64" ->
      Literal (LitInt64 (Int64.of_int (get_int (get_field json "int64"))))
  | `Assoc _ when has_field json "float64" ->
      Literal (LitFloat64 (get_float (get_field json "float64")))
  | `Assoc _ when has_field json "bool" ->
      Literal (LitBool (get_bool (get_field json "bool")))
  | _ ->
      raise (ParseError (InvalidNodeKind (Yojson.Safe.to_string json)))

and parse_case (json : Yojson.Safe.t) : case =
  let pat_json = get_field json "pattern" in
  let ctor = get_string (get_field pat_json "ctor") in
  let args =
    match get_field_opt pat_json "args" with
    | Some args_json ->
        List.map
          (fun a -> { arg_name = get_string (get_field a "name") })
          (get_list args_json)
    | None -> []
  in
  let body = parse_term (get_field json "body") in
  { pattern = { ctor; args }; body }

(** {1 Binder Parsing} *)

let parse_binder (json : Yojson.Safe.t) : binder =
  {
    name = get_string (get_field json "name");
    ty = parse_term (get_field json "type");
  }

(** {1 Declaration Parsing} *)

let parse_role (s : string) : role =
  match s with
  | "runtime" -> Runtime
  | "proof-only" -> ProofOnly
  | "both" -> Both
  | _ -> raise (ParseError (InvalidValue ("role", s)))

let parse_inductive (json : Yojson.Safe.t) : inductive_decl =
  let name = get_string (get_field json "name") in
  let params =
    match get_field_opt json "params" with
    | Some ps -> List.map parse_binder (get_list ps)
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
          | Some args -> List.map parse_binder (get_list args)
          | None -> []
        in
        { ctor_name; ctor_args })
      (get_list (get_field json "constructors"))
  in
  { ind_name = name; params; ind_universe = universe; constructors }

let parse_def (json : Yojson.Safe.t) : def_decl =
  let name = get_string (get_field json "name") in
  let role =
    match get_field_opt json "role" with
    | Some (`String s) -> parse_role s
    | _ -> Both
  in
  let ty = parse_term (get_field json "type") in
  let body = parse_term (get_field json "body") in
  let rec_args =
    match get_field_opt json "rec_args" with
    | Some args -> Some (List.map get_int (get_list args))
    | None -> None
  in
  { def_name = name; def_role = role; def_type = ty; def_body = body; rec_args }

let parse_theorem (json : Yojson.Safe.t) : theorem_decl =
  let name = get_string (get_field json "name") in
  let ty = parse_term (get_field json "type") in
  let proof = parse_term (get_field json "proof") in
  { thm_name = name; thm_type = ty; thm_proof = proof }

let parse_repr (json : Yojson.Safe.t) : repr_decl =
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
  { repr_name = name; kind }

let parse_extern_c (json : Yojson.Safe.t) : extern_c_decl =
  let name = get_string (get_field json "name") in
  let c_name = get_string (get_field json "c_name") in
  let header = get_string (get_field json "header") in
  let sig_json = get_field json "signature" in
  let return_repr =
    match get_field_opt sig_json "return" with
    | Some r -> Some (get_string (get_field r "repr"))
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
  let logical_type = parse_term (get_field json "type") in
  let safety =
    match get_field_opt json "safety" with
    | Some (`String "pure") -> Pure
    | Some (`String "impure") -> Impure
    | _ -> Pure
  in
  let axioms =
    match get_field_opt json "axioms" with
    | Some axs -> List.map get_string (get_list axs)
    | None -> []
  in
  { extern_name = name; c_name; header; return_repr; args; logical_type; safety; axioms }

let parse_declaration (json : Yojson.Safe.t) : declaration =
  if has_field json "inductive" then
    Inductive (parse_inductive (get_field json "inductive"))
  else if has_field json "def" then
    Definition (parse_def (get_field json "def"))
  else if has_field json "theorem" then
    Theorem (parse_theorem (get_field json "theorem"))
  else if has_field json "repr" then
    Repr (parse_repr (get_field json "repr"))
  else if has_field json "extern_c" then
    ExternC (parse_extern_c (get_field json "extern_c"))
  else
    raise (ParseError (InvalidNodeKind (Yojson.Safe.to_string json)))

(** {1 Module Parsing} *)

let parse_module (json : Yojson.Safe.t) : module_decl =
  let module_name = get_string (get_field json "module") in
  let imports =
    match get_field_opt json "imports" with
    | Some imps -> List.map get_string (get_list imps)
    | None -> []
  in
  let declarations =
    List.map parse_declaration (get_list (get_field json "declarations"))
  in
  { module_name; imports; declarations }

(** {1 Entry Points} *)

let parse_string (s : string) : (module_decl, parse_error) result =
  try
    let json = Yojson.Safe.from_string s in
    Ok (parse_module json)
  with
  | ParseError e -> Error e
  | Yojson.Json_error msg -> Error (JsonError msg)

let parse_file (filename : string) : (module_decl, parse_error) result =
  try
    let json = Yojson.Safe.from_file filename in
    Ok (parse_module json)
  with
  | ParseError e -> Error e
  | Yojson.Json_error msg -> Error (JsonError msg)
  | Sys_error msg -> Error (JsonError msg)
