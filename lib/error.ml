(** Error types and utilities for CertiJSON. *)

(** {1 Error Locations} *)

type location = {
  file : string option;
  line : int option;
  column : int option;
}

let no_loc : location = { file = None; line = None; column = None }

let pp_location fmt loc =
  match (loc.file, loc.line, loc.column) with
  | Some f, Some l, Some c -> Format.fprintf fmt "%s:%d:%d" f l c
  | Some f, Some l, None -> Format.fprintf fmt "%s:%d" f l
  | Some f, None, None -> Format.fprintf fmt "%s" f
  | None, Some l, Some c -> Format.fprintf fmt "line %d, column %d" l c
  | None, Some l, None -> Format.fprintf fmt "line %d" l
  | _ -> Format.fprintf fmt "<unknown location>"

(** {1 Error Kinds} *)

type error_kind =
  | ParseError of Json_parser.parse_error
  | TypingError of Typing.typing_error
  | InternalError of string

(** {1 Errors} *)

type error = {
  kind : error_kind;
  location : location;
  message : string;
}

let make_error ?(loc = no_loc) kind message =
  { kind; location = loc; message }

(** {1 Error Formatting} *)

let pp_error_kind fmt = function
  | ParseError e -> Format.fprintf fmt "Parse error: %s" (Json_parser.show_parse_error e)
  | TypingError e -> Format.fprintf fmt "Type error: %s" (Typing.string_of_typing_error e)
  | InternalError msg -> Format.fprintf fmt "Internal error: %s" msg

let pp_error fmt err =
  Format.fprintf fmt "@[<v>%a: %s@,%a@]"
    pp_location err.location
    err.message
    pp_error_kind err.kind

let error_to_string err =
  Format.asprintf "%a" pp_error err

(** {1 Result Utilities} *)

type 'a result = ('a, error) Result.t

let ok x = Ok x
let error e = Error e

let ( let* ) = Result.bind

let map_error f = function
  | Ok x -> Ok x
  | Error e -> Error (f e)

(** {1 Converting from component errors} *)

let parse_error_location ?file = function
  | Json_parser.JsonError msg -> (
      (* Attempt to extract line number from Yojson's "Line n, bytes ..." message. *)
      match Scanf.sscanf_opt msg "Line %d, bytes %d-%d:%!" (fun line _ _ -> line) with
      | Some line -> { file; line = Some line; column = None }
      | None -> { file; line = None; column = None })
  | _ -> { file; line = None; column = None }

let find_substring_from ?(start = 0) (sub : string) (s : string) : int option =
  let len_sub = String.length sub in
  let len = String.length s in
  let rec loop i =
    if i + len_sub > len then None
    else if String.sub s i len_sub = sub then Some i
    else loop (i + 1)
  in
  loop start

let line_col_of_index (s : string) (idx : int) : int * int =
  let line = ref 1 in
  let col = ref 1 in
  for i = 0 to idx - 1 do
    if s.[i] = '\n' then (
      incr line;
      col := 1)
    else incr col
  done;
  (!line, !col)

let index_name_locations (content : string) : (string, location) Hashtbl.t =
  let tbl = Hashtbl.create 64 in
  let len = String.length content in
  let rec skip_ws i =
    if i >= len then len
    else
      match content.[i] with
      | ' ' | '\n' | '\t' | '\r' -> skip_ws (i + 1)
      | _ -> i
  in
  let rec find_string_literal i =
    if i >= len then None
    else if content.[i] = '"' then
      let start = i + 1 in
      let rec find_end j =
        if j >= len then None
        else
          match content.[j] with
          | '\\' -> find_end (j + 2)  (* skip escaped char *)
          | '"' -> Some (start, j)
          | _ -> find_end (j + 1)
      in
      find_end start
    else find_string_literal (i + 1)
  in
  let rec scan i =
    match find_substring_from ~start:i "\"name\"" content with
    | None -> ()
    | Some idx_name ->
        let after_name = idx_name + 6 in
        let after_ws = skip_ws after_name in
        let after_colon =
          if after_ws < len && content.[after_ws] = ':' then skip_ws (after_ws + 1) else after_ws
        in
        (match find_string_literal after_colon with
        | Some (start, stop) ->
            let name = String.sub content start (stop - start) in
            let line, col = line_col_of_index content start in
            Hashtbl.replace tbl name { file = None; line = Some line; column = Some col };
            scan (stop + 1)
        | None -> ())
  in
  scan 0;
  tbl

let name_location_cache : (string, (string, location) Hashtbl.t) Hashtbl.t =
  Hashtbl.create 8

let name_locations_for_file (file : string) : (string, location) Hashtbl.t =
  match Hashtbl.find_opt name_location_cache file with
  | Some tbl -> tbl
  | None ->
      let tbl =
        try
          let ch = open_in_bin file in
          let len = in_channel_length ch in
          let content = really_input_string ch len in
          close_in ch;
          let tbl = index_name_locations content in
          Hashtbl.add name_location_cache file tbl;
          tbl
        with _ ->
          let tbl = Hashtbl.create 1 in
          Hashtbl.add name_location_cache file tbl;
          tbl
      in
      tbl

let location_of_name_in_file (file : string) (name : string) : location option =
  let tbl = name_locations_for_file file in
  match Hashtbl.find_opt tbl name with
  | Some loc -> Some { loc with file = Some file }
  | None ->
      (* Fallback: naive search *)
      try
        let ch = open_in_bin file in
        let len = in_channel_length ch in
        let content = really_input_string ch len in
        close_in ch;
        match find_substring_from name content with
        | None -> None
        | Some idx ->
            let line, col = line_col_of_index content idx in
            Some { file = Some file; line = Some line; column = Some col }
      with _ -> None

let rec typing_location ?file (e : Typing.typing_error) : location =
  match (file, e) with
  | Some f, Typing.InDeclaration (name, inner) -> (
      match location_of_name_in_file f name with
      | Some loc -> loc
      | None -> typing_location ~file:f inner)
  | Some f, _ -> { file = Some f; line = None; column = None }
  | None, _ -> no_loc

let error_of_parse ?file (e : Json_parser.parse_error) : error =
  {
    kind = ParseError e;
    location = parse_error_location ?file e;
    message = Json_parser.show_parse_error e;
  }

let error_of_typing ?file (e : Typing.typing_error) : error =
  {
    kind = TypingError e;
    location = typing_location ?file e;
    message = Typing.string_of_typing_error e;
  }
