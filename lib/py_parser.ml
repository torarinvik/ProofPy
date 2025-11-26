open Syntax
open Py_lexer

let mk_term desc _ _ = mk ?loc:None desc

type parser_state = {
  tokens : token list;
  mutable pos : int;
}

exception ParseError of string

let init_parser tokens = { tokens; pos = 0 }

let peek state =
  if state.pos < List.length state.tokens then
    List.nth state.tokens state.pos
  else
    EOF

let advance state =
  if state.pos < List.length state.tokens then
    state.pos <- state.pos + 1

let consume state expected =
  match peek state with
  | t when t = expected -> advance state; true
  | _ -> false

let expect state expected msg =
  if consume state expected then ()
  else raise (ParseError (msg ^ ", got " ^ (show_token (peek state))))

let rec parse_type state =
  match peek state with
  | LBRACE ->
      advance state;
      (match peek state with
       | IDENT name ->
           advance state;
           expect state COLON "Expected ':' in refinement type";
           let ty = parse_type state in
           expect state PIPE "Expected '|' in refinement type";
           let pred = parse_expr state in
           expect state RBRACE "Expected '}'";
           mk_term (Subset { arg = { name; ty; role = Runtime; b_loc = None }; pred }) None None
       | _ -> raise (ParseError "Expected identifier in refinement type"))
  | IDENT name ->
      advance state;
      let rec parse_dotted acc =
        match peek state with
        | DOT ->
            advance state;
            (match peek state with
             | IDENT n -> advance state; parse_dotted (acc ^ "." ^ n)
             | _ -> raise (ParseError ("Expected identifier after dot, got " ^ (show_token (peek state)))))
        | _ -> acc
      in
      let full_name = parse_dotted name in
      (match full_name with
       | "Int32" -> mk_term (PrimType Int32) None None
       | "Int64" -> mk_term (PrimType Int64) None None
       | "Float64" -> mk_term (PrimType Float64) None None
       | "Bool" -> mk_term (PrimType Bool) None None
       | "String" -> mk_term (PrimType String) None None
       | _ ->
           (match peek state with
            | LPAREN ->
                advance state;
                let args = parse_type_args state in
                expect state RPAREN "Expected ')'";
                mk_term (App (mk_term (Var full_name) None None, args)) None None
            | _ -> mk_term (Var full_name) None None))
  | LPAREN ->
      advance state;
      (match peek state with
       | IDENT name ->
           advance state;
           if consume state COLON then (
             let ty = parse_type state in
             expect state RPAREN "Expected ')'";
             expect state ARROW "Expected '->'";
             let result = parse_type state in
             mk_term (Pi { arg = { name; ty; role = Runtime; b_loc = None }; result }) None None
           ) else (
              (* Assume it was a type name in parens, e.g. (Int) *)
              (* But we consumed IDENT. We need to parse the rest of the type? *)
              (* For now, let's just support (x: A) -> B *)
              raise (ParseError "Only dependent function types (x: A) -> B supported in parens")
           )
       | _ -> raise (ParseError "Expected identifier in dependent type"))
  | _ -> raise (ParseError "Expected type")

and parse_type_args state =
  match peek state with
  | RPAREN -> []
  | _ ->
      let first = parse_type state in
      match peek state with
      | COMMA -> advance state; first :: parse_type_args state
      | _ -> [first]

and parse_expr state =
  let left = parse_or_expr state in
  match peek state with
  | IF ->
      advance state;
      let cond = parse_or_expr state in
      expect state ELSE "Expected 'else' in if expression";
      let right = parse_expr state in
      mk_term (If { cond; then_ = left; else_ = right }) None None
  | _ -> left

and parse_or_expr state =
  let left = parse_and_expr state in
  match peek state with
  | OR ->
      advance state;
      let right = parse_or_expr state in
      mk_term (App (mk_term (Var "or") None None, [left; right])) None None
  | _ -> left

and parse_and_expr state =
  let left = parse_comp_expr state in
  match peek state with
  | AND ->
      advance state;
      let right = parse_and_expr state in
      mk_term (App (mk_term (Var "and") None None, [left; right])) None None
  | _ -> left

and parse_comp_expr state =
  let left = parse_add_expr state in
  match peek state with
  | EQ -> advance state; let right = parse_add_expr state in mk_term (App (mk_term (Var "eq") None None, [left; right])) None None
  | NEQ -> advance state; let right = parse_add_expr state in mk_term (App (mk_term (Var "ne") None None, [left; right])) None None
  | LT -> advance state; let right = parse_add_expr state in mk_term (App (mk_term (Var "lt") None None, [left; right])) None None
  | GT -> advance state; let right = parse_add_expr state in mk_term (App (mk_term (Var "gt") None None, [left; right])) None None
  | LE -> advance state; let right = parse_add_expr state in mk_term (App (mk_term (Var "le") None None, [left; right])) None None
  | GE -> advance state; let right = parse_add_expr state in mk_term (App (mk_term (Var "ge") None None, [left; right])) None None
  | _ -> left

and parse_add_expr state =
  let left = parse_mul_expr state in
  match peek state with
  | PLUS -> advance state; let right = parse_add_expr state in mk_term (App (mk_term (Var "add") None None, [left; right])) None None
  | MINUS -> advance state; let right = parse_add_expr state in mk_term (App (mk_term (Var "sub") None None, [left; right])) None None
  | _ -> left

and parse_mul_expr state =
  let left = parse_unary_expr state in
  match peek state with
  | STAR -> advance state; let right = parse_mul_expr state in mk_term (App (mk_term (Var "mul") None None, [left; right])) None None
  | SLASH -> advance state; let right = parse_mul_expr state in mk_term (App (mk_term (Var "div") None None, [left; right])) None None
  | PERCENT -> advance state; let right = parse_mul_expr state in mk_term (App (mk_term (Var "mod") None None, [left; right])) None None
  | _ -> left

and parse_unary_expr state =
  match peek state with
  | NOT -> advance state; let e = parse_unary_expr state in mk_term (App (mk_term (Var "not") None None, [e])) None None
  | MINUS -> advance state; let e = parse_unary_expr state in mk_term (App (mk_term (Var "neg") None None, [e])) None None
  | _ -> parse_primary_expr state

and parse_primary_expr state =
  match peek state with
  | IDENT name ->
      advance state;
      let rec parse_dotted acc =
        match peek state with
        | DOT ->
            advance state;
            (match peek state with
             | IDENT n -> advance state; parse_dotted (acc ^ "." ^ n)
             | RETURN -> advance state; parse_dotted (acc ^ ".return")
             | _ -> raise (ParseError ("Expected identifier after dot, got " ^ (show_token (peek state)))))
        | _ -> acc
      in
      let full_name = parse_dotted name in
      (match full_name with
       | "Int32" -> mk_term (PrimType Int32) None None
       | "Int64" -> mk_term (PrimType Int64) None None
       | "Float64" -> mk_term (PrimType Float64) None None
       | "Bool" -> mk_term (PrimType Bool) None None
       | "String" -> mk_term (PrimType String) None None
       | _ ->
           (match peek state with
            | LPAREN ->
                advance state;
                let args = parse_args state in
                expect state RPAREN "Expected ')'";
                mk_term (App (mk_term (Var full_name) None None, args)) None None
            | _ -> mk_term (Var full_name) None None))
  | INT i -> advance state; mk_term (Literal (LitInt32 i)) None None
  | INT64 i -> advance state; mk_term (Literal (LitInt64 i)) None None
  | STRING s -> advance state; mk_term (Literal (LitString s)) None None
  | BOOL b -> advance state; mk_term (Literal (LitBool b)) None None
  | LPAREN ->
      advance state;
      let e = parse_expr state in
      expect state RPAREN "Expected ')'";
      e
  | _ -> raise (ParseError ("Unexpected token in expression: " ^ (show_token (peek state))))

and parse_args state =
  match peek state with
  | RPAREN -> []
  | _ ->
      let first = parse_expr state in
      match peek state with
      | COMMA -> advance state; first :: parse_args state
      | _ -> [first]

let rec guess_io_type (t : term) : term =
  match t.desc with
  | App ({ desc = Var "bind"; _ }, [_; b; _; _]) -> b
  | App ({ desc = Var "return"; _ }, [b; _]) -> b
  | App ({ desc = Var "Std.IO.return"; _ }, [b; _]) -> b
  | If { then_; _ } -> guess_io_type then_
  | Match { cases; _ } -> (match cases with [] -> mk_term (Var "Unit") None None | c :: _ -> guess_io_type c.body)
  | _ -> mk_term (Var "Unit") None None

let rec parse_block state =
  expect state INDENT "Expected indented block";
  let stmts = parse_stmts state in
  expect state DEDENT "Expected dedent";
  stmts

and parse_stmts state =
  match peek state with
  | DEDENT | EOF -> []
  | _ ->
      let stmt = parse_stmt state in
      stmt :: parse_stmts state

and parse_stmt state =
  match peek state with
  | RETURN ->
      advance state;
      let e = parse_expr state in
      expect state NEWLINE "Expected newline after return";
      (fun _ -> e)
  | IF ->
      advance state;
      let cond = parse_expr state in
      expect state COLON "Expected ':' after if condition";
      expect state NEWLINE "Expected newline after ':'";
      let then_stmts = parse_block state in
      let then_body = fold_stmts then_stmts in
      let else_body =
        match peek state with
        | ELSE ->
            advance state;
            expect state COLON "Expected ':' after else";
            expect state NEWLINE "Expected newline after ':'";
            let else_stmts = parse_block state in
            fold_stmts else_stmts
        | _ -> mk_term (Var "tt") None None
      in
      (fun rest -> 
         match rest.desc with
         | Var "tt" -> mk_term (If { cond; then_ = then_body; else_ = else_body }) None None
         | _ ->
             let b_ty = guess_io_type rest in
             mk_term (App (mk_term (Var "bind") None None, 
               [mk_term (Universe Type) None None;
                b_ty;
                mk_term (If { cond; then_ = then_body; else_ = else_body }) None None;
                mk_term (Lambda { arg = { name = "_"; ty = mk_term (Universe Type) None None; role = Runtime; b_loc = None }; body = rest }) None None])) None None)
  | IDENT name ->
      (* Assignment or expression statement *)
      advance state;
      let rec parse_dotted acc =
        match peek state with
        | DOT ->
            advance state;
            (match peek state with
             | IDENT n -> advance state; parse_dotted (acc ^ "." ^ n)
             | RETURN -> advance state; parse_dotted (acc ^ ".return")
             | _ -> raise (ParseError ("Expected identifier after dot, got " ^ (show_token (peek state)))))
        | _ -> acc
      in
      
      (match peek state with
      | DOT ->
          let full_name = parse_dotted name in
           let expr_rest = 
             match peek state with
             | LPAREN -> 
                 advance state;
                 let args = parse_args state in
                 expect state RPAREN "Expected ')'";
                 mk_term (App (mk_term (Var full_name) None None, args)) None None
             | _ -> mk_term (Var full_name) None None
           in
           expect state NEWLINE "Expected newline after expression statement";
           (fun rest -> 
              match rest.desc with
              | Var "tt" -> expr_rest
              | _ ->
                  let b_ty = guess_io_type rest in
                  mk_term (App (mk_term (Var "bind") None None, 
                    [mk_term (Var "Unit") None None;
                     b_ty;
                     expr_rest;
                     mk_term (Lambda { arg = { name = "_"; ty = mk_term (Var "Unit") None None; role = Runtime; b_loc = None }; body = rest }) None None])) None None)
      | COLON ->
           advance state;
           let ty = parse_type state in
           (match peek state with
            | ASSIGN ->
                advance state;
                let e = parse_expr state in
                expect state NEWLINE "Expected newline";
                (fun rest -> 
                   mk_term (App (mk_term (Lambda { arg = { name = name; ty = ty; role = Runtime; b_loc = None }; body = rest }) None None, [e])) None None)
            | LARROW ->
                advance state;
                let e = parse_expr state in
                expect state NEWLINE "Expected newline";
                (fun rest -> 
                   let b_ty = guess_io_type rest in
                   mk_term (App (mk_term (Var "bind") None None, 
                     [ty;
                      b_ty;
                      e;
                      mk_term (Lambda { arg = { name = name; ty = ty; role = Runtime; b_loc = None }; body = rest }) None None])) None None)
            | _ -> raise (ParseError "Expected '=' or '<-' after type annotation"))
       | ASSIGN ->
           raise (ParseError "Type annotation required for assignment (x: T = e)")
       | _ ->
           (* Backtrack or handle expression stmt *)
           (* For simplicity, let's assume expression statement if not assignment *)
           (* But we already consumed IDENT. Reconstruct expr. *)
           (* This is tricky with single token lookahead. *)
           (* Let's assume it's a function call or variable access *)
           let expr_rest = 
             match peek state with
             | LPAREN -> 
                 advance state;
                 let args = parse_args state in
                 expect state RPAREN "Expected ')'";
                 mk_term (App (mk_term (Var name) None None, args)) None None
             | _ -> mk_term (Var name) None None
           in
           (* Continue parsing expression if needed? No, statement level expressions are usually calls. *)
           expect state NEWLINE "Expected newline after expression statement";
           (fun rest -> 
              match rest.desc with
              | Var "tt" -> expr_rest
              | _ ->
                  let b_ty = guess_io_type rest in
                  mk_term (App (mk_term (Var "bind") None None, 
                    [mk_term (Var "Unit") None None;
                     b_ty;
                     expr_rest;
                     mk_term (Lambda { arg = { name = "_"; ty = mk_term (Var "Unit") None None; role = Runtime; b_loc = None }; body = rest }) None None])) None None)
      )
  | NEWLINE -> advance state; parse_stmt state (* Skip empty lines *)
  | _ -> raise (ParseError ("Unexpected token in statement: " ^ (show_token (peek state))))

and fold_stmts stmts =
  match stmts with
  | [] -> mk_term (Var "tt") None None
  | [f] -> f (mk_term (Var "tt") None None)
  | f :: rest -> f (fold_stmts rest)

let parse_arg state =
  match peek state with
  | IDENT name ->
      advance state;
      expect state COLON "Expected ':' in argument";
      let ty = parse_type state in
      { name; ty; role = Runtime; b_loc = None }
  | _ -> raise (ParseError "Expected argument name")

let rec parse_arg_list state =
  match peek state with
  | RPAREN -> []
  | _ ->
      let arg = parse_arg state in
      match peek state with
      | COMMA -> advance state; arg :: parse_arg_list state
      | _ -> [arg]

let parse_def state =
  expect state DEF "Expected 'def'";
  match peek state with
  | IDENT name ->
      advance state;
      expect state LPAREN "Expected '('";
      let args = parse_arg_list state in
      expect state RPAREN "Expected ')'";
      expect state ARROW "Expected '->'";
      let ret_ty = parse_type state in
      expect state COLON "Expected ':'";
      expect state NEWLINE "Expected newline after def";
      let stmts = parse_block state in
      let body = fold_stmts stmts in
      
      let full_type = List.fold_right (fun b acc -> mk_term (Pi { arg = b; result = acc }) None None) args ret_ty in
      let full_body = List.fold_right (fun b acc -> mk_term (Lambda { arg = b; body = acc }) None None) args body in
      
      Definition {
        def_name = name;
        def_role = Runtime;
        def_type = full_type;
        def_body = full_body;
        rec_args = None;
        def_loc = None;
      }
  | _ -> raise (ParseError "Expected function name")

type top_level_item =
  | Import of string
  | Decl of declaration

let rec parse_top_level_items state =
  match peek state with
  | EOF -> []
  | NEWLINE -> advance state; parse_top_level_items state
  | IMPORT ->
      advance state;
      let rec parse_dotted_name acc =
        match peek state with
        | IDENT name ->
            advance state;
            let new_acc = if acc = "" then name else acc ^ "." ^ name in
            (match peek state with
             | DOT -> advance state; parse_dotted_name new_acc
             | _ -> new_acc)
        | _ -> raise (ParseError "Expected module name")
      in
      let name = parse_dotted_name "" in
      expect state NEWLINE "Expected newline after import";
      Import name :: parse_top_level_items state
  | DEF ->
      let def = parse_def state in
      Decl def :: parse_top_level_items state
  | _ -> raise (ParseError ("Unexpected token at top level: " ^ (show_token (peek state))))

let parse_program tokens =
  let state = init_parser tokens in
  let items = parse_top_level_items state in
  let imports = List.filter_map (function Import i -> Some i | _ -> None) items in
  let decls = List.filter_map (function Decl d -> Some d | _ -> None) items in
  { module_name = "Main"; imports; declarations = decls; module_loc = None }
