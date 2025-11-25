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
