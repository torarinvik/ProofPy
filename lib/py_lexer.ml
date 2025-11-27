module Loc = Loc

type token =
  | DEF | RETURN | IF | ELSE | ELIF | WHILE | MATCH | CASE | CLASS | IMPORT
  | THEOREM | FORALL | PROOF | PROP | IN
  | IDENT of string
  | INT of int32
  | INT64 of int64
  | STRING of string
  | BOOL of bool
  | LPAREN | RPAREN | LBRACK | RBRACK | LBRACE | RBRACE
  | COLON | SEMICOLON | COMMA | DOT
  | ARROW (* -> *)
  | ASSIGN (* = *)
  | EQ (* == *) | NEQ (* != *) | LT | GT | LE | GE
  | PLUS | MINUS | STAR | SLASH | PERCENT
  | AND | OR | NOT
  | PIPE
  | LARROW (* <- *)
  | BACKSLASH (* \ *)
  | INDENT | DEDENT | NEWLINE
  | EOF
[@@deriving show, eq]

type error =
  | IllegalCharacter of char * Loc.t
  | UnterminatedString of Loc.t
  | IndentationError of string * Loc.t
[@@deriving show]

exception LexerError of error

let is_digit c = c >= '0' && c <= '9'
let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_'
let is_alphanum c = is_alpha c || is_digit c

let keywords = [
  ("def", DEF);
  ("return", RETURN);
  ("if", IF);
  ("else", ELSE);
  ("elif", ELIF);
  ("while", WHILE);
  ("match", MATCH);
  ("case", CASE);
  ("class", CLASS);
  ("import", IMPORT);
  ("theorem", THEOREM);
  ("forall", FORALL);
  ("proof", PROOF);
  ("prop", PROP);
  ("in", IN);
  ("True", BOOL true);
  ("False", BOOL false);
  ("and", AND);
  ("or", OR);
  ("not", NOT);
]

let tokenize (source : string) : token list =
  let len = String.length source in
  let tokens = ref [] in
  let add t = tokens := t :: !tokens in
  
  let i = ref 0 in
  let line = ref 1 in
  let col = ref 0 in
  let indent_stack = ref [0] in
  
  let current_loc () =
    { Loc.file = None; line = Some !line; column = Some !col }
  in

  let peek () =
    if !i >= len then '\000' else source.[!i]
  in
  
  let advance () =
    if !i < len then (
      let c = source.[!i] in
      incr i;
      if c = '\n' then (incr line; col := 0) else incr col;
      c
    ) else '\000'
  in

  let rec skip_comment () =
    let c = peek () in
    if c <> '\n' && c <> '\000' then (
      ignore (advance ());
      skip_comment ()
    )
  in

  let rec read_indentation () =
    let rec get_indent n = 
       match peek () with
       | ' ' -> ignore (advance ()); get_indent (n + 1)
       | '\t' -> ignore (advance ()); get_indent (n + 4)
       | '#' -> skip_comment (); -1 (* Signal to restart *)
       | '\n' -> ignore (advance ()); -1 (* Signal to restart *)
       | '\000' -> -2 (* EOF *)
       | _ -> n
    in
    
    let spaces = get_indent 0 in
    if spaces = -1 then read_indentation ()
    else if spaces = -2 then ()
    else
      let current_indent = List.hd !indent_stack in
      if spaces > current_indent then (
        indent_stack := spaces :: !indent_stack;
        add INDENT
      ) else if spaces < current_indent then (
        let rec dedent stack =
          match stack with
          | top :: rest when spaces < top ->
              add DEDENT;
              dedent rest
          | top :: _ when spaces = top ->
              indent_stack := stack
          | _ -> raise (LexerError (IndentationError ("Inconsistent indentation", current_loc ())))
        in
        dedent !indent_stack
      ) else ()
  in

  (* Initial indentation check *)
  (* read_indentation (); *) (* Actually, we handle this in the loop *)

  let at_line_start = ref true in

  while !i < len do
    if !at_line_start then (
      read_indentation ();
      at_line_start := false
    );
    
    let c = peek () in
    match c with
    | ' ' | '\t' | '\r' -> ignore (advance ())
    | '\n' ->
        ignore (advance ());
        add NEWLINE;
        at_line_start := true
    | '#' ->
        skip_comment ()
    | '(' -> ignore (advance ()); add LPAREN
    | ')' -> ignore (advance ()); add RPAREN
    | '[' -> ignore (advance ()); add LBRACK
    | ']' -> ignore (advance ()); add RBRACK
    | '{' -> ignore (advance ()); add LBRACE
    | '}' -> ignore (advance ()); add RBRACE
    | ':' -> ignore (advance ()); add COLON
    | ';' -> ignore (advance ()); add SEMICOLON
    | ',' -> ignore (advance ()); add COMMA
    | '.' -> ignore (advance ()); add DOT
    | '+' -> ignore (advance ()); add PLUS
    | '-' -> 
        ignore (advance ());
        if peek () = '>' then (ignore (advance ()); add ARROW)
        else add MINUS
    | '*' -> ignore (advance ()); add STAR
    | '/' -> ignore (advance ()); add SLASH
    | '%' -> ignore (advance ()); add PERCENT
    | '|' -> ignore (advance ()); add PIPE
    | '\\' -> ignore (advance ()); add BACKSLASH
    | '=' -> 
        ignore (advance ());
        if peek () = '=' then (ignore (advance ()); add EQ)
        else add ASSIGN
    | '!' ->
        ignore (advance ());
        if peek () = '=' then (ignore (advance ()); add NEQ)
        else raise (LexerError (IllegalCharacter ('!', current_loc ())))
    | '<' ->
        ignore (advance ());
        if peek () = '=' then (ignore (advance ()); add LE)
        else if peek () = '-' then (ignore (advance ()); add LARROW)
        else add LT
    | '>' ->
        ignore (advance ());
        if peek () = '=' then (ignore (advance ()); add GE)
        else add GT
    | '"' ->
        ignore (advance ());
        let buf = Buffer.create 16 in
        let rec read_string () =
          let c = advance () in
          match c with
          | '"' -> add (STRING (Buffer.contents buf))
          | '\\' -> 
              let c2 = advance () in
              (match c2 with
               | 'n' -> Buffer.add_char buf '\n'
               | 't' -> Buffer.add_char buf '\t'
               | 'r' -> Buffer.add_char buf '\r'
               | '\\' -> Buffer.add_char buf '\\'
               | '"' -> Buffer.add_char buf '"'
               | _ -> Buffer.add_char buf '\\'; Buffer.add_char buf c2);
              read_string ()
          | '\000' -> raise (LexerError (UnterminatedString (current_loc ())))
          | c -> Buffer.add_char buf c; read_string ()
        in
        read_string ()
    | _ when is_digit c ->
        let buf = Buffer.create 16 in
        let rec read_int () =
          let c = peek () in
          if is_digit c then (
            Buffer.add_char buf (advance ());
            read_int ()
          ) else if c = 'L' then (
            ignore (advance ());
            add (INT64 (Int64.of_string (Buffer.contents buf)))
          ) else (
            add (INT (Int32.of_string (Buffer.contents buf)))
          )
        in
        read_int ()
    | _ when is_alpha c ->
        let buf = Buffer.create 16 in
        let rec read_ident () =
          let c = peek () in
          if is_alphanum c then (
            Buffer.add_char buf (advance ());
            read_ident ()
          ) else (
            let s = Buffer.contents buf in
            match List.assoc_opt s keywords with
            | Some tok -> add tok
            | None -> add (IDENT s)
          )
        in
        read_ident ()
    | '\000' -> ()
    | _ -> raise (LexerError (IllegalCharacter (c, current_loc ())))
  done;
  
  (* Dedent remaining levels at EOF *)
  let rec dedent_all stack =
    match stack with
    | _ :: rest when rest <> [] ->
        add DEDENT;
        dedent_all rest
    | _ -> ()
  in
  dedent_all !indent_stack;
  
  add EOF;
  List.rev !tokens
