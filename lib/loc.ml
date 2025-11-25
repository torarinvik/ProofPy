(** Source code locations (file/line/column) and helpers. *)

type t = {
  file : string option;
  line : int option;
  column : int option;
}
[@@deriving show, eq]

let none = { file = None; line = None; column = None }

let with_file file loc = { loc with file = Some file }

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

let index_name_locations (content : string) : (string, t) Hashtbl.t =
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

let name_location_cache : (string, (string, t) Hashtbl.t) Hashtbl.t = Hashtbl.create 8

let name_locations_for_file (file : string) : (string, t) Hashtbl.t =
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

let location_of_name_in_file (file : string) (name : string) : t option =
  let tbl = name_locations_for_file file in
  match Hashtbl.find_opt tbl name with
  | Some loc -> Some (with_file file loc)
  | None -> None

(** Line index for offset-to-line/column mapping. *)
let loc_of_range ?file (((line, col), _) : (int * int) * (int * int)) : t =
  { file; line = Some line; column = Some col }
