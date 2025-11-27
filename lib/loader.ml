(** Module loader for CertiJSON. *)

open Syntax
open Context

type error =
  | ParseError of Json_parser.parse_error
  | TypeError of Typing.typing_error
  | ImportError of string
  | CycleDetected of string list

let pp_error fmt = function
  | ParseError e -> Json_parser.pp_parse_error fmt e
  | TypeError e -> Typing.pp_typing_error fmt e
  | ImportError msg -> Format.fprintf fmt "Import error: %s" msg
  | CycleDetected cycle -> Format.fprintf fmt "Cycle detected: %s" (String.concat " -> " cycle)

type config = {
  include_paths : string list;
}

let default_config = {
  include_paths = ["."; "stdlib"];
}

type cache = (name, signature) Hashtbl.t

let create_cache () : cache = Hashtbl.create 16

let resolve_import (config : config) (name : name) : string option =
  let candidates =
    match name with
    | "Std.IO" -> ["std_io.json"]
    | "Std.Math" -> ["std_math.json"]
    | "Std.Memory" -> ["std_memory.json"]
    | "Std.CStdIO" -> ["std_stdio.json"]
    | "Std.CTime" -> ["std_time.json"]
    | "Std.CCtype" -> ["std_ctype.json"]
    | "Std.CEnv" -> ["std_env.json"]
    | "Std.CLocale" -> ["std_locale.json"]
    | "Std.POSIX" -> ["std_posix.json"]
    | "Std.POSIXSockets" -> ["std_posix_sockets.json"]
    | "Std.CMath" -> ["std_cmath.json"]
    | "Std.CErrno" -> ["std_errno.json"]
    | "Std.CAssert" -> ["std_assert.json"]
    | "Std.Option" -> ["std_option.json"]
    | "Std.Result" -> ["std_result.json"]
    | "Std.Bool" -> ["std_bool.json"]
    | "Std.Pair" -> ["std_pair.json"]
    | "Std.Int" -> ["std_int.json"]
    | "Std.String" -> ["std_string.json"]
    | "Std.Char" -> ["std_char.json"]
    | "Std.List" -> ["std_list.json"]
    | "Std.Eq" -> ["std_eq.json"]
    | "Std.Nat" -> ["std_nat.json"]
    | "Std.Fin" -> ["std_fin.json"]
    | "Std.Relation" -> ["std_relation.json"]
    | "Std.Decidable" -> ["std_decidable.json"]
    | "Std.Array" -> ["std_array.json"]
    | "Std.Either" -> ["std_either.json"]
    | "Std.Pointer" -> ["std_pointer.json"]
    | "Std.Vec" -> ["std_vec.json"]
    | "Std.SafeMemory" -> ["std_safe_memory.json"]
    | "Std.File" -> ["std_file.json"]
    | _ ->
        [ name ^ ".json";
          String.lowercase_ascii name ^ ".json";
          name ^ ".cj";
          String.lowercase_ascii name ^ ".cj" ]
  in
  List.find_map (fun dir ->
    List.find_map (fun filename ->
      let path = Filename.concat dir filename in
      if Sys.file_exists path then Some path else None
    ) candidates
  ) config.include_paths

let parse_file (path : string) : (module_decl, error) result =
  let parse_result =
    if Filename.check_suffix path ".json" then
      Json_parser.parse_file path
    else if Filename.check_suffix path ".cj" then
      try
        let ch = open_in path in
        let len = in_channel_length ch in
        let source = really_input_string ch len in
        close_in ch;
        let tokens = Py_lexer.tokenize source in
        Ok (Py_parser.parse_program tokens)
      with
      | Py_lexer.LexerError (e) -> Error (Json_parser.JsonError (Py_lexer.show_error e))
      | Py_parser.ParseError msg -> Error (Json_parser.JsonError msg)
      | Sys_error msg -> Error (Json_parser.JsonError msg)
    else
      Error (Json_parser.JsonError "Unknown file extension")
  in
  match parse_result with
  | Error e -> Error (ParseError e)
  | Ok mod_ -> Ok mod_

let rec load_module (config : config) (cache : cache) (stack : name list) (name : name) : (signature, error) result =
  if List.mem name stack then
    Error (CycleDetected (List.rev (name :: stack)))
  else
    match Hashtbl.find_opt cache name with
    | Some sig_ -> Ok sig_
    | None ->
        match resolve_import config name with
        | None -> Error (ImportError (Printf.sprintf "Module %s not found" name))
        | Some path ->
            match parse_file path with
            | Error e -> Error e
            | Ok mod_ ->
                if mod_.module_name <> name then
                  Error (ImportError (Printf.sprintf "File %s declares module %s, expected %s" path mod_.module_name name))
                else
                  load_imports config cache (name :: stack) mod_

and load_imports (config : config) (cache : cache) (stack : name list) (mod_ : module_decl) : (signature, error) result =
  let rec loop acc imports =
    match imports with
    | [] -> Ok acc
    | imp :: rest ->
        match load_module config cache stack imp with
        | Error e -> Error e
        | Ok imp_sig ->
            let acc' = Context.merge_signatures acc imp_sig in
            let qualified_sig = Context.qualify_signature imp imp_sig in
            let acc'' = Context.merge_signatures acc' qualified_sig in
            loop acc'' rest
  in
  match loop (Context.empty_sig ()) mod_.imports with
  | Error e -> Error e
  | Ok imports_sig ->
      match Typing.check_module mod_ imports_sig with
      | Error e -> Error (TypeError e)
      | Ok full_sig ->
          Hashtbl.add cache mod_.module_name full_sig;
          Ok full_sig
