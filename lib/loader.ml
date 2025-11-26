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

type cache = (name, signature) Hashtbl.t

let create_cache () : cache = Hashtbl.create 16

let resolve_import (name : name) : string option =
  (* Convert dot notation to path separators if needed, but for now assume flat names or handle manually *)
  (* Actually, Std.IO -> stdlib/std_io.json is a specific mapping we might want. *)
  (* Or we can just map "Std.IO" -> "std_io.json" and look in stdlib. *)
  
  let filename = 
    match name with
    | "Std.IO" -> "std_io.json"
    | "Std.Math" -> "std_math.json"
    | "Std.Memory" -> "std_memory.json"
    | "Std.CStdIO" -> "std_stdio.json"
    | "Std.CTime" -> "std_time.json"
    | "Std.CCtype" -> "std_ctype.json"
    | "Std.CEnv" -> "std_env.json"
    | "Std.CLocale" -> "std_locale.json"
    | "Std.POSIX" -> "std_posix.json"
    | "Std.POSIXSockets" -> "std_posix_sockets.json"
    | "Std.CMath" -> "std_cmath.json"
    | "Std.CErrno" -> "std_errno.json"
    | "Std.CAssert" -> "std_assert.json"
    | "Std.Option" -> "std_option.json"
    | "Std.Result" -> "std_result.json"
    | "Std.Bool" -> "std_bool.json"
    | "Std.Pair" -> "std_pair.json"
    | "Std.Int" -> "std_int.json"
    | "Std.String" -> "std_string.json"
    | "Std.Char" -> "std_char.json"
    | "Std.List" -> "std_list.json"
    | "Std.Eq" -> "std_eq.json"
    | "Std.Nat" -> "std_nat.json"
    | "Std.Either" -> "std_either.json"
    | _ ->
        name ^ ".json" 
  in
  let paths = ["."; "stdlib"] in
  List.find_map (fun dir ->
    let path = Filename.concat dir filename in
    if Sys.file_exists path then Some path else None
  ) paths

let rec load_module (cache : cache) (stack : name list) (name : name) : (signature, error) result =
  if List.mem name stack then
    Error (CycleDetected (List.rev (name :: stack)))
  else
    match Hashtbl.find_opt cache name with
    | Some sig_ -> Ok sig_
    | None ->
        match resolve_import name with
        | None -> Error (ImportError (Printf.sprintf "Module %s not found" name))
        | Some path ->
            match Json_parser.parse_file path with
            | Error e -> Error (ParseError e)
            | Ok mod_ ->
                if mod_.module_name <> name then
                  Error (ImportError (Printf.sprintf "File %s declares module %s, expected %s" path mod_.module_name name))
                else
                  load_imports cache (name :: stack) mod_

and load_imports (cache : cache) (stack : name list) (mod_ : module_decl) : (signature, error) result =
  let rec loop acc imports =
    match imports with
    | [] -> Ok acc
    | imp :: rest ->
        match load_module cache stack imp with
        | Error e -> Error e
        | Ok imp_sig ->
            let acc' = Context.merge_signatures acc imp_sig in
            loop acc' rest
  in
  match loop (Context.empty_sig ()) mod_.imports with
  | Error e -> Error e
  | Ok imports_sig ->
      match Typing.check_module mod_ imports_sig with
      | Error e -> Error (TypeError e)
      | Ok full_sig ->
          Hashtbl.add cache mod_.module_name full_sig;
          Ok full_sig
