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

(* Moved helpers *)

let rec guess_io_type (t : term) : term =
  match t.desc with
  | App ({ desc = Var "bind"; _ }, [_; b; _; _]) -> b
  | App ({ desc = Var "return"; _ }, [b; _]) -> b
  | App ({ desc = Var "Std.IO.return"; _ }, [b; _]) -> b
  | If { then_; _ } -> guess_io_type then_
  | Match { cases; _ } -> (match cases with [] -> mk_term (Var "Unit") None None | c :: _ -> guess_io_type c.body)
  | _ -> mk_term (Var "Unit") None None

let is_capitalized s =
  String.length s > 0 && let c = s.[0] in c >= 'A' && c <= 'Z'

let parse_pattern_arg state =
  match peek state with
  | IDENT name ->
      advance state;
      { arg_name = name; arg_loc = None }
  | _ -> raise (ParseError "Expected pattern argument")

let rec parse_pattern_args state =
  match peek state with
  | RPAREN -> []
  | _ ->
      let arg = parse_pattern_arg state in
      match peek state with
      | COMMA -> advance state; arg :: parse_pattern_args state
      | _ -> [arg]

let parse_pattern state =
  match peek state with
  | IDENT name ->
      advance state;
      (* Parse dotted pattern like Kind.I or just I *)
      let rec parse_dotted_pattern acc =
        match peek state with
        | DOT ->
            advance state;
            (match peek state with
             | IDENT n -> advance state; parse_dotted_pattern (acc ^ "." ^ n)
             | _ -> acc)
        | _ -> acc
      in
      let full_name = parse_dotted_pattern name in
      (match peek state with
       | LPAREN ->
           advance state;
           let args = parse_pattern_args state in
           expect state RPAREN "Expected ')' in pattern";
           { ctor = full_name; args; pat_loc = None }
       | _ -> 
           { ctor = full_name; args = []; pat_loc = None }
      )
  | INT i ->
      advance state;
      { ctor = Int32.to_string i; args = []; pat_loc = None }
  | BOOL b ->
      advance state;
      { ctor = if b then "True" else "False"; args = []; pat_loc = None }
  | _ -> raise (ParseError "Expected pattern")

let rec fold_stmts stmts =
  match stmts with
  | [] -> mk_term (Var "tt") None None
  | [f] -> f (mk_term (Var "tt") None None)
  | f :: rest -> f (fold_stmts rest)

(* Main parser functions *)

let rec parse_type state =
  match peek state with
  | FORALL ->
      (* forall x: T, body -- creates a Pi type *)
      advance state;
      (match peek state with
       | IDENT name ->
           advance state;
           expect state COLON "Expected ':' after forall variable";
           let ty = parse_type state in
           expect state COMMA "Expected ',' after forall type";
           let result = parse_type state in
           mk_term (Pi { arg = { name; ty; role = Runtime; b_loc = None }; result }) None None
       | LPAREN ->
           (* forall (x: T), body *)
           advance state;
           (match peek state with
            | IDENT name ->
                advance state;
                expect state COLON "Expected ':' in forall binding";
                let ty = parse_type state in
                expect state RPAREN "Expected ')' after forall binding";
                expect state COMMA "Expected ',' after forall type";
                let result = parse_type state in
                mk_term (Pi { arg = { name; ty; role = Runtime; b_loc = None }; result }) None None
            | _ -> raise (ParseError "Expected identifier in forall binding"))
       | _ -> raise (ParseError "Expected identifier or '(' after forall"))
  | EXISTS ->
      (* exists x: T, body -- creates an Exists type *)
      advance state;
      (match peek state with
       | IDENT name ->
           advance state;
           expect state COLON "Expected ':' after exists variable";
           let ty = parse_type state in
           expect state COMMA "Expected ',' after exists type";
           let body = parse_type state in
           mk_term (Exists { arg = { name; ty; role = Runtime; b_loc = None }; body }) None None
       | LPAREN ->
           (* exists (x: T), body *)
           advance state;
           (match peek state with
            | IDENT name ->
                advance state;
                expect state COLON "Expected ':' in exists binding";
                let ty = parse_type state in
                expect state RPAREN "Expected ')' after exists binding";
                expect state COMMA "Expected ',' after exists type";
                let body = parse_type state in
                mk_term (Exists { arg = { name; ty; role = Runtime; b_loc = None }; body }) None None
            | _ -> raise (ParseError "Expected identifier in exists binding"))
       | _ -> raise (ParseError "Expected identifier or '(' after exists"))
  | LBRACE ->
      advance state;
      (match peek state with
       | IDENT name ->
           advance state;
           (* Could be refinement type { x : T | pred } or struct update { base with field := value } *)
           (match peek state with
            | COLON ->
                (* Refinement type: { name : type | pred } *)
                advance state;
                let ty = parse_type state in
                expect state PIPE "Expected '|' in refinement type";
                let pred = parse_expr state in
                expect state RBRACE "Expected '}'";
                mk_term (Subset { arg = { name; ty; role = Runtime; b_loc = None }; pred }) None None
            | WITH ->
                (* Struct update: { base with field := value, ... } *)
                advance state;
                (* Parse field updates *)
                let rec parse_updates () =
                  match peek state with
                  | RBRACE -> []
                  | IDENT field ->
                      advance state;
                      expect state COLONASSIGN "Expected ':=' after field name in struct update";
                      let value = parse_expr state in
                      let rest = 
                        match peek state with
                        | COMMA -> advance state; parse_updates ()
                        | _ -> []
                      in
                      (field, value) :: rest
                  | _ -> raise (ParseError "Expected field name in struct update")
                in
                let updates = parse_updates () in
                expect state RBRACE "Expected '}' after struct update";
                (* Convert { base with f1 := v1, f2 := v2 } into functional record update
                   We need runtime support or expand to constructor call.
                   For now, generate a function call: struct_update_<field>(base, value) 
                   This will need stdlib support.
                   Better approach: expand directly to constructor call with fields.
                   Since we don't know the type statically here, let's use a special update syntax
                   that the type-checker can resolve.
                   For now, let's use a simpler approach:
                   { s with x := v } becomes WithUpdate(s, "x", v)
                   But we don't have that in the AST. Let's use App form.
                   Actually, the simplest approach for a dependently-typed language:
                   Generate nested applications: set_field(base, value) for each update.
                   We can generate: S.mk(field1, field2, ...) with the updated values.
                   But we need type info for that.
                   
                   Let's use a special marker that type-checker can expand:
                   Create a special StructUpdate node or use App with a special name.
                   For MVP, let's just generate sequential updates:
                   { s with x := v1, y := v2 } => update_y(update_x(s, v1), v2)
                   where update_x is a function that must be defined.
                   
                   Actually simpler: generate Let bindings that shadow fields.
                   Let's just create a special App for now with mangled name.
                *)
                let base_term = mk_term (Var name) None None in
                List.fold_left (fun acc (field, value) ->
                  (* Generate: _struct_update(acc, "field", value) 
                     For now, let's use a simpler approach - call update_<field>(base, value)
                     But that requires defining update functions.
                     
                     Best simple approach: just use constructor with match/let:
                     let old = base in S.mk(v1, S.field2(old), S.field3(old), ...)
                     But we don't know S here without type info.
                     
                     Let's use a workaround: generate direct field setter application
                     set_<StructType>_<field>(base, value)
                     But again, needs type info.
                     
                     For MVP, let's just not support this and require explicit constructor calls.
                     Return an error-indicative term for now.
                  *)
                  (* Simple workaround: assume functions like GameState_with_score exist *)
                  let update_fn = "_update_" ^ field in
                  mk_term (App (mk_term (Var update_fn) None None, [acc; value])) None None
                ) base_term updates
            | _ ->
                (* It's an expression that starts with identifier, backtrack *)
                state.pos <- state.pos - 2;  (* Go back before LBRACE and IDENT *)
                raise (ParseError "Expected ':' or 'with' in brace expression"))
       | _ -> raise (ParseError "Expected identifier in brace expression"))
  | LPAREN ->
      let start_pos = state.pos in
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
              state.pos <- start_pos;
              parse_expr state
           )
       | _ -> 
           state.pos <- start_pos;
           parse_expr state)
  | _ -> parse_expr state

and parse_type_args state =
  match peek state with
  | RPAREN -> []
  | _ ->
      let first = parse_type state in
      match peek state with
      | COMMA -> advance state; first :: parse_type_args state
      | _ -> [first]

and parse_expr state =
  match peek state with
  | BACKSLASH ->
      (* \x -> body *)
      advance state;
      (match peek state with
       | IDENT name ->
           advance state;
           expect state ARROW "Expected '->' in lambda";
           let body =
             match peek state with
             | NEWLINE ->
                 advance state;
                 expect state INDENT "Expected indented block for lambda";
                 let stmts = parse_stmts state None in
                 expect state DEDENT "Expected dedent after lambda block";
                 fold_stmts stmts
             | _ -> parse_expr state
           in
           mk_term (Lambda { arg = { name; ty = mk_term (Var "_") None None; role = Runtime; b_loc = None }; body }) None None
       | _ -> raise (ParseError "Expected identifier in lambda"))
  | LAMBDA ->
      (* lambda x: body  OR  lambda x: T: body  -- Python style with optional type *)
      advance state;
      (match peek state with
       | IDENT name ->
           advance state;
           expect state COLON "Expected ':' after lambda parameter";
           (* Try to parse a type annotation followed by another colon, or just the body *)
           let ty_or_body = parse_expr state in
           (match peek state with
            | COLON ->
                (* We have lambda x: T: body - ty_or_body is actually the type *)
                advance state;
                let body = parse_expr state in
                mk_term (Lambda { arg = { name; ty = ty_or_body; role = Runtime; b_loc = None }; body }) None None
            | _ ->
                (* We have lambda x: body - no type annotation, ty_or_body is the body *)
                mk_term (Lambda { arg = { name; ty = mk_term (Var "_") None None; role = Runtime; b_loc = None }; body = ty_or_body }) None None)
       | _ -> raise (ParseError "Expected identifier after lambda"))
  | FUN ->
      (* fun x y => body *)
      advance state;
      let rec parse_fun_args () =
        match peek state with
        | IDENT name ->
            advance state;
            let ty =
              match peek state with
              | COLON -> advance state; parse_type state
              | _ -> mk_term (Var "_") None None
            in
            let arg = { name; ty; role = Runtime; b_loc = None } in
            (match peek state with
             | ARROW -> [arg]  (* => marks end of args *)
             | _ -> arg :: parse_fun_args ())
        | _ -> []
      in
      let args = parse_fun_args () in
      expect state ARROW "Expected '=>' or '->' after fun arguments";
      let body = parse_expr state in
      List.fold_right 
        (fun arg acc -> mk_term (Lambda { arg; body = acc }) None None) 
        args body
  | IF ->
      (* if cond then e1 else e2 *)
      advance state;
      let cond = parse_or_expr state in
      (match peek state with
       | THEN ->
           advance state;
           let then_branch = parse_expr state in
           expect state ELSE "Expected 'else' in if expression";
           let else_branch = parse_expr state in
           mk_term (If { cond; then_ = then_branch; else_ = else_branch }) None None
       | _ ->
           (* Fall back: this might be a standalone if statement misparse *)
           raise (ParseError "Expected 'then' after condition in if expression"))
  | _ ->
      let left = parse_or_expr state in
      match peek state with
      | IF ->
          (* x if cond else y - ternary form *)
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
  | PROPEQ -> 
      advance state; 
      let right = parse_add_expr state in 
      (* Check for optional type annotation: lhs === rhs : Type *)
      let ty = 
        match peek state with
        | COLON ->
            advance state;
            parse_add_expr state
        | _ ->
            (* Without explicit type, we use left as a placeholder - type checker will infer *)
            (* This is a hack - ideally we'd have proper type inference *)
            left
      in
      mk_term (Eq { ty; lhs = left; rhs = right }) None None
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
  let base =
    match peek state with
    | EXISTS ->
        (* exists x: T, body in expression context *)
        advance state;
        (match peek state with
         | IDENT name ->
             advance state;
             expect state COLON "Expected ':' after exists variable";
             let ty = parse_type state in
             expect state COMMA "Expected ',' after exists type";
             let body = parse_expr state in
             mk_term (Exists { arg = { name; ty; role = Runtime; b_loc = None }; body }) None None
         | LPAREN ->
             advance state;
             (match peek state with
              | IDENT name ->
                  advance state;
                  expect state COLON "Expected ':' in exists binding";
                  let ty = parse_type state in
                  expect state RPAREN "Expected ')' after exists binding";
                  expect state COMMA "Expected ',' after exists type";
                  let body = parse_expr state in
                  mk_term (Exists { arg = { name; ty; role = Runtime; b_loc = None }; body }) None None
              | _ -> raise (ParseError "Expected identifier in exists binding"))
         | _ -> raise (ParseError "Expected identifier or '(' after exists"))
    | FORALL ->
        (* forall x: T, body in expression context *)
        advance state;
        (match peek state with
         | IDENT name ->
             advance state;
             expect state COLON "Expected ':' after forall variable";
             let ty = parse_type state in
             expect state COMMA "Expected ',' after forall type";
             let result = parse_expr state in
             mk_term (Pi { arg = { name; ty; role = Runtime; b_loc = None }; result }) None None
         | LPAREN ->
             advance state;
             (match peek state with
              | IDENT name ->
                  advance state;
                  expect state COLON "Expected ':' in forall binding";
                  let ty = parse_type state in
                  expect state RPAREN "Expected ')' after forall binding";
                  expect state COMMA "Expected ',' after forall type";
                  let result = parse_expr state in
                  mk_term (Pi { arg = { name; ty; role = Runtime; b_loc = None }; result }) None None
              | _ -> raise (ParseError "Expected identifier in forall binding"))
         | _ -> raise (ParseError "Expected identifier or '(' after forall"))
    | REFL ->
        (* refl is a proof of reflexive equality. The type checker will infer the 
           type and value from context. We use placeholder terms here. *)
        advance state;
        (* Create a Refl with placeholders - type checker fills in from expected type *)
        mk_term (Refl { ty = mk_term (Var "_refl_type") None None; 
                        value = mk_term (Var "_refl_value") None None }) None None
    | IDENT name ->
        advance state;
        let rec parse_dotted acc =
          match peek state with
          | DOT ->
              advance state;
              (match peek state with
               | IDENT "value" -> state.pos <- state.pos - 1; acc
               | IDENT "proof" -> state.pos <- state.pos - 1; acc
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
         | "Type" -> mk_term (Universe Type) None None
         | "Prop" -> mk_term (Universe Prop) None None
         | _ -> mk_term (Var full_name) None None)
    | INT i -> advance state; mk_term (Literal (LitInt32 i)) None None
    | INT64 i -> advance state; mk_term (Literal (LitInt64 i)) None None
    | STRING s -> advance state; mk_term (Literal (LitString s)) None None
    | BOOL b -> advance state; mk_term (Literal (LitBool b)) None None
    | LBRACE -> parse_type state
    | LPAREN ->
        advance state;
        let e = parse_expr state in
        expect state RPAREN "Expected ')'";
        e
    | _ -> raise (ParseError ("Unexpected token in expression: " ^ (show_token (peek state))))
  in
  parse_postfix state base

and parse_postfix state term =
  match peek state with
  | DOT ->
      advance state;
      (match peek state with
       | IDENT "value" -> advance state; parse_postfix state (mk_term (SubsetElim term) None None)
       | IDENT "proof" -> advance state; parse_postfix state (mk_term (SubsetProof term) None None)
       | IDENT field_name -> 
           (* General struct field access: expr.field -> field(expr) *)
           advance state;
           parse_postfix state (mk_term (App (mk_term (Var field_name) None None, [term])) None None)
       | _ -> raise (ParseError "Expected field name after dot"))
  | LPAREN ->
      advance state;
      let args = parse_args state in
      expect state RPAREN "Expected ')'";
      parse_postfix state (mk_term (App (term, args)) None None)
  | _ -> term

and parse_args state =
  match peek state with
  | RPAREN -> []
  | _ ->
      let first = parse_expr state in
      match peek state with
      | COMMA -> advance state; first :: parse_args state
      | _ -> [first]

and parse_block state ret_ty =
  expect state INDENT "Expected indented block";
  let stmts = parse_stmts state ret_ty in
  expect state DEDENT "Expected dedent";
  stmts

and parse_cases state ret_ty =
  match peek state with
  | CASE ->
      advance state;
      let pat = parse_pattern state in
      expect state COLON "Expected ':' after case pattern";
      expect state NEWLINE "Expected newline after case";
      let stmts = parse_block state ret_ty in
      let body = fold_stmts stmts in
      { pattern = pat; body = body; case_loc = None } :: parse_cases state ret_ty
  | DEDENT -> []
  | NEWLINE -> advance state; parse_cases state ret_ty
  | _ -> raise (ParseError "Expected 'case' or dedent")

and parse_stmts state ret_ty =
  match peek state with
  | DEDENT | EOF -> []
  | _ ->
      let stmt = parse_stmt state ret_ty in
      stmt :: parse_stmts state ret_ty

and parse_stmt state ret_ty =
  match peek state with
  | LET ->
      (* let x: T = value in body  OR  let x: T = value (followed by more stmts) *)
      advance state;
      (match peek state with
       | IDENT name ->
           advance state;
           expect state COLON "Expected ':' after let variable";
           let ty = parse_type state in
           expect state ASSIGN "Expected '=' after let type";
           let value = parse_expr state in
           (* Check for optional 'in' keyword *)
           (match peek state with
            | IN ->
                advance state;
                let body = parse_expr state in
                expect state NEWLINE "Expected newline after let expression";
                (fun rest ->
                   let let_term = mk_term (Let { arg = { name; ty; role = Runtime; b_loc = None }; value; body }) None None in
                   match rest.desc with
                   | Var "tt" -> let_term
                   | _ ->
                       mk_term (App (mk_term (Lambda { arg = { name = "_"; ty = mk_term (Var "Unit") None None; role = Runtime; b_loc = None }; body = rest }) None None, [let_term])) None None)
            | NEWLINE ->
                (* let x: T = v followed by more statements - body is the rest *)
                advance state;
                (fun rest ->
                   mk_term (Let { arg = { name; ty; role = Runtime; b_loc = None }; value; body = rest }) None None)
            | _ -> raise (ParseError "Expected 'in' or newline after let value"))
       | _ -> raise (ParseError "Expected variable name after let"))
  | MATCH ->
      advance state;
      let scrutinee = parse_expr state in
      expect state COLON "Expected ':' after match scrutinee";
      expect state NEWLINE "Expected newline after match";
      expect state INDENT "Expected indented block for match cases";
      let cases = parse_cases state ret_ty in
      expect state DEDENT "Expected dedent after match cases";
      (fun rest ->
         let motive = match ret_ty with Some t -> t | None -> mk_term (Var "Unit") None None in
         let match_term = mk_term (Match { scrutinee; motive; as_name = None; cases; coverage_hint = Unknown }) None None in
         match rest.desc with
         | Var "tt" -> match_term
         | _ ->
             let b_ty = guess_io_type rest in
             mk_term (App (mk_term (Var "bind") None None, 
               [mk_term (Var "Unit") None None;
                b_ty;
                match_term;
                mk_term (Lambda { arg = { name = "_"; ty = mk_term (Var "Unit") None None; role = Runtime; b_loc = None }; body = rest }) None None])) None None)
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
      let then_stmts = parse_block state ret_ty in
      let then_body = fold_stmts then_stmts in
      let else_body =
        match peek state with
        | ELSE ->
            advance state;
            expect state COLON "Expected ':' after else";
            expect state NEWLINE "Expected newline after ':'";
            let else_stmts = parse_block state ret_ty in
            fold_stmts else_stmts
        | _ -> mk_term (Var "tt") None None
      in
      (fun rest -> 
         match rest.desc with
         | Var "tt" -> mk_term (If { cond; then_ = then_body; else_ = else_body }) None None
         | _ ->
             let b_ty = guess_io_type rest in
             mk_term (App (mk_term (Var "bind") None None, 
               [mk_term (Var "Unit") None None;
                b_ty;
                mk_term (If { cond; then_ = then_body; else_ = else_body }) None None;
                mk_term (Lambda { arg = { name = "_"; ty = mk_term (Var "Unit") None None; role = Runtime; b_loc = None }; body = rest }) None None])) None None)
  | WHILE ->
      advance state;
      let cond = parse_expr state in
      expect state COLON "Expected ':' after while condition";
      expect state NEWLINE "Expected newline after ':'";
      let body_stmts = parse_block state ret_ty in
      let body = fold_stmts body_stmts in
      (fun rest ->
         let while_term = mk_term (While { cond; body }) None None in
         match rest.desc with
         | Var "tt" -> while_term
         | _ ->
             mk_term (App (mk_term (Lambda { arg = { name = "_"; ty = mk_term (Var "Unit") None None; role = Runtime; b_loc = None }; body = rest }) None None, [while_term])) None None)
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
      | ASSIGN ->
          advance state;
          let value = parse_expr state in
          expect state NEWLINE "Expected newline after assignment";
          (fun rest ->
             let assign_term = mk_term (Assign { name; value }) None None in
             match rest.desc with
             | Var "tt" -> assign_term
             | _ ->
                 mk_term (App (mk_term (Lambda { arg = { name = "_"; ty = mk_term (Var "Unit") None None; role = Runtime; b_loc = None }; body = rest }) None None, [assign_term])) None None)
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
  | NEWLINE -> advance state; parse_stmt state ret_ty (* Skip empty lines *)
  | _ -> 
      (* Try to parse as expression statement *)
      let expr = parse_expr state in
      expect state NEWLINE "Expected newline after expression statement";
      (fun rest -> 
         match rest.desc with
         | Var "tt" -> expr
         | _ ->
             let b_ty = guess_io_type rest in
             mk_term (App (mk_term (Var "bind") None None, 
               [mk_term (Var "Unit") None None;
                b_ty;
                expr;
                mk_term (Lambda { arg = { name = "_"; ty = mk_term (Var "Unit") None None; role = Runtime; b_loc = None }; body = rest }) None None])) None None)

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

let rec parse_constructors state =
  match peek state with
  | DEDENT -> []
  | IDENT name ->
      advance state;
      (* Parse dotted constructor name like MyClass.ctor *)
      let rec parse_dotted_ctor acc =
        match peek state with
        | DOT ->
            advance state;
            (match peek state with
             | IDENT n -> advance state; parse_dotted_ctor (acc ^ "." ^ n)
             | _ -> acc)
        | _ -> acc
      in
      let full_name = parse_dotted_ctor name in
      let args =
        match peek state with
        | LPAREN ->
            advance state;
            let a = parse_arg_list state in
            expect state RPAREN "Expected ')' in constructor";
            a
        | _ -> []
      in
      expect state NEWLINE "Expected newline after constructor";
      { ctor_name = full_name; ctor_args = args; ctor_loc = None } :: parse_constructors state
  | NEWLINE -> advance state; parse_constructors state
  | _ -> raise (ParseError ("Unexpected token in class body: " ^ (show_token (peek state))))

let parse_inductive state =
  expect state CLASS "Expected 'class'";
  match peek state with
  | IDENT name ->
      advance state;
      let params =
        match peek state with
        | LPAREN ->
            advance state;
            let p = parse_arg_list state in
            expect state RPAREN "Expected ')' in class params";
            p
        | _ -> []
      in
      (* Check for optional "in Prop" or "in Type" universe specifier *)
      let universe =
        match peek state with
        | IN ->
            advance state;
            (match peek state with
             | PROP -> advance state; Syntax.Prop
             | IDENT "Type" -> advance state; Syntax.Type
             | _ -> raise (ParseError "Expected 'Prop' or 'Type' after 'in'"))
        | _ -> Syntax.Type (* Default to Type universe *)
      in
      expect state COLON "Expected ':' after class definition";
      expect state NEWLINE "Expected newline after class definition";
      expect state INDENT "Expected indented block for constructors";
      let ctors = parse_constructors state in
      expect state DEDENT "Expected dedent after class body";
      (* Prefix constructor names with class name if not already prefixed *)
      let qualified_ctors = List.map (fun ctor ->
        let qualified_name =
          if String.contains ctor.ctor_name '.' then ctor.ctor_name
          else name ^ "." ^ ctor.ctor_name
        in
        { ctor with ctor_name = qualified_name }
      ) ctors in
      {
        ind_name = name;
        params = params;
        ind_universe = universe;
        constructors = qualified_ctors;
        ind_loc = None;
      }
  | _ -> raise (ParseError "Expected class name")

(* Parse enum (alias for class/inductive type) - more Pythonic for ADTs *)
let parse_inductive_with_enum state =
  expect state ENUM "Expected 'enum'";
  match peek state with
  | IDENT name ->
      advance state;
      let params =
        match peek state with
        | LPAREN ->
            advance state;
            let p = parse_arg_list state in
            expect state RPAREN "Expected ')' in enum params";
            p
        | _ -> []
      in
      (* enums default to Type universe *)
      let universe = Syntax.Type in
      expect state COLON "Expected ':' after enum definition";
      expect state NEWLINE "Expected newline after enum definition";
      expect state INDENT "Expected indented block for constructors";
      let ctors = parse_constructors state in
      expect state DEDENT "Expected dedent after enum body";
      (* Prefix constructor names with enum name if not already prefixed *)
      let qualified_ctors = List.map (fun ctor ->
        let qualified_name =
          if String.contains ctor.ctor_name '.' then ctor.ctor_name
          else name ^ "." ^ ctor.ctor_name
        in
        { ctor with ctor_name = qualified_name }
      ) ctors in
      {
        ind_name = name;
        params = params;
        ind_universe = universe;
        constructors = qualified_ctors;
        ind_loc = None;
      }
  | _ -> raise (ParseError "Expected enum name")

(* Parse a theorem declaration *)
let parse_theorem state =
  expect state THEOREM "Expected 'theorem'";
  match peek state with
  | IDENT name ->
      advance state;
      expect state COLON "Expected ':'";
      expect state NEWLINE "Expected newline after theorem name";
      expect state INDENT "Expected indented block for theorem type";
      let ty = parse_type state in
      expect state NEWLINE "Expected newline after theorem type";
      expect state DEDENT "Expected dedent after theorem type";
      expect state PROOF "Expected 'proof:'";
      expect state COLON "Expected ':' after proof";
      expect state NEWLINE "Expected newline after proof:";
      let proof_stmts = parse_block state (Some ty) in
      let proof = fold_stmts proof_stmts in
      Theorem {
        thm_name = name;
        thm_type = ty;
        thm_proof = proof;
        thm_loc = None;
      }
  | _ -> raise (ParseError "Expected theorem name")

(* Parse struct field: name : type *)
let rec parse_struct_fields state =
  match peek state with
  | DEDENT -> []
  | IDENT name ->
      advance state;
      expect state COLON "Expected ':' after field name";
      let ty = parse_type state in
      expect state NEWLINE "Expected newline after field";
      { name; ty; role = Runtime; b_loc = None } :: parse_struct_fields state
  | NEWLINE -> advance state; parse_struct_fields state
  | _ -> raise (ParseError ("Unexpected token in struct body: " ^ (show_token (peek state))))

(* Parse a structure declaration - single constructor record type *)
(* Returns a list of declarations: the inductive + projection functions *)
let parse_struct state =
  expect state STRUCT "Expected 'struct'";
  match peek state with
  | IDENT name ->
      advance state;
      let params =
        match peek state with
        | LPAREN ->
            advance state;
            let p = parse_arg_list state in
            expect state RPAREN "Expected ')' in struct params";
            p
        | _ -> []
      in
      expect state COLON "Expected ':' after struct definition";
      expect state NEWLINE "Expected newline after struct definition";
      expect state INDENT "Expected indented block for struct fields";
      let fields = parse_struct_fields state in
      expect state DEDENT "Expected dedent after struct body";
      
      (* Create the inductive type with a single constructor named Name.mk *)
      let ind_decl = Inductive {
        ind_name = name;
        params = params;
        ind_universe = Type;
        constructors = [{
          ctor_name = name ^ ".mk";
          ctor_args = fields;
          ctor_loc = None;
        }];
        ind_loc = None;
      } in
      
      (* Generate projection functions for each field *)
      (* For struct S with params P1...Pn and field f : T, generate:
         def S.f (p1: P1) ... (pn: Pn) (s: S(p1,...,pn)) -> T :=
           match s with
           | S.mk(..., f, ...) => f
      *)
      let struct_ty = 
        if params = [] then mk_term (Var name) None None
        else mk_term (App (mk_term (Var name) None None, 
                           List.map (fun b -> mk_term (Var b.name) None None) params)) None None
      in
      
      let make_projection field_idx (field : binder) =
        (* Build the type: forall params, S(params) -> field.ty *)
        let struct_arg = { name = "s"; ty = struct_ty; role = Runtime; b_loc = None } in
        let full_type = 
          List.fold_right 
            (fun b acc -> mk_term (Pi { arg = b; result = acc }) None None)
            (params @ [struct_arg])
            field.ty
        in
        
        (* Build the body: match s with S.mk(f0, f1, ...) => field *)
        let pattern_args = List.mapi (fun i _f -> { arg_name = "f" ^ string_of_int i; arg_loc = None }) fields in
        let field_var = "f" ^ string_of_int field_idx in
        let match_expr = mk_term (Match {
          scrutinee = mk_term (Var "s") None None;
          motive = field.ty;
          as_name = None;
          cases = [{
            pattern = { ctor = name ^ ".mk"; args = pattern_args; pat_loc = None };
            body = mk_term (Var field_var) None None;
            case_loc = None;
          }];
          coverage_hint = Complete;
        }) None None in
        
        let full_body =
          List.fold_right
            (fun b acc -> mk_term (Lambda { arg = b; body = acc }) None None)
            (params @ [struct_arg])
            match_expr
        in
        
        Definition {
          def_name = name ^ "." ^ field.name;
          def_role = Runtime;
          def_type = full_type;
          def_body = full_body;
          rec_args = None;
          def_loc = None;
        }
      in
      
      (* Generate update functions for each field *)
      (* _update_<field>(s: S, newVal: T) -> S = match s with S.mk(...) => S.mk(..., newVal, ...) *)
      let make_updater field_idx (field : binder) =
        let struct_arg = { name = "s"; ty = struct_ty; role = Runtime; b_loc = None } in
        let new_val_arg = { name = "newVal"; ty = field.ty; role = Runtime; b_loc = None } in
        let full_type = 
          List.fold_right 
            (fun b acc -> mk_term (Pi { arg = b; result = acc }) None None)
            (params @ [struct_arg; new_val_arg])
            struct_ty
        in
        
        (* Build pattern args and constructor args *)
        let pattern_args = List.mapi (fun i _f -> { arg_name = "f" ^ string_of_int i; arg_loc = None }) fields in
        (* Constructor args: use newVal for the updated field, f_i for others *)
        let ctor_args = List.mapi (fun i _f ->
          if i = field_idx then mk_term (Var "newVal") None None
          else mk_term (Var ("f" ^ string_of_int i)) None None
        ) fields in
        
        let match_expr = mk_term (Match {
          scrutinee = mk_term (Var "s") None None;
          motive = struct_ty;
          as_name = None;
          cases = [{
            pattern = { ctor = name ^ ".mk"; args = pattern_args; pat_loc = None };
            body = mk_term (App (mk_term (Var (name ^ ".mk")) None None, ctor_args)) None None;
            case_loc = None;
          }];
          coverage_hint = Complete;
        }) None None in
        
        let full_body =
          List.fold_right
            (fun b acc -> mk_term (Lambda { arg = b; body = acc }) None None)
            (params @ [struct_arg; new_val_arg])
            match_expr
        in
        
        Definition {
          def_name = "_update_" ^ field.name;
          def_role = Runtime;
          def_type = full_type;
          def_body = full_body;
          rec_args = None;
          def_loc = None;
        }
      in
      
      let projections = List.mapi make_projection fields in
      let updaters = List.mapi make_updater fields in
      ind_decl :: projections @ updaters
      
  | _ -> raise (ParseError "Expected struct name")

(* Parse @dataclass decorated class as a struct - uses 'class' keyword instead of 'struct' *)
and parse_struct_as_class state =
  expect state CLASS "Expected 'class' after @dataclass";
  match peek state with
  | IDENT name ->
      advance state;
      let params =
        match peek state with
        | LPAREN ->
            advance state;
            let p = parse_arg_list state in
            expect state RPAREN "Expected ')' in dataclass params";
            p
        | _ -> []
      in
      expect state COLON "Expected ':' after dataclass definition";
      expect state NEWLINE "Expected newline after dataclass definition";
      expect state INDENT "Expected indented block for dataclass fields";
      let fields = parse_struct_fields state in
      expect state DEDENT "Expected dedent after dataclass body";
      
      (* Now reuse parse_struct's struct generation logic *)
      (* Create the inductive type with a single constructor named Name.mk *)
      let struct_ty = 
        if params = [] then mk_term (Var name) None None
        else mk_term (App (mk_term (Var name) None None, 
                           List.map (fun b -> mk_term (Var b.name) None None) params)) None None
      in
      
      let ind_decl = Inductive {
        ind_name = name;
        params = params;
        ind_universe = Type;
        constructors = [{
          ctor_name = name ^ ".mk";
          ctor_args = fields;
          ctor_loc = None;
        }];
        ind_loc = None;
      } in
      
      (* Generate projection functions for each field *)
      let make_projection field_idx (field : binder) =
        let struct_arg = { name = "s"; ty = struct_ty; role = Runtime; b_loc = None } in
        let full_type = 
          List.fold_right 
            (fun b acc -> mk_term (Pi { arg = b; result = acc }) None None)
            (params @ [struct_arg])
            field.ty
        in
        let pattern_args = List.mapi (fun i _f -> { arg_name = "f" ^ string_of_int i; arg_loc = None }) fields in
        let field_var = "f" ^ string_of_int field_idx in
        let match_expr = mk_term (Match {
          scrutinee = mk_term (Var "s") None None;
          motive = field.ty;
          as_name = None;
          cases = [{
            pattern = { ctor = name ^ ".mk"; args = pattern_args; pat_loc = None };
            body = mk_term (Var field_var) None None;
            case_loc = None;
          }];
          coverage_hint = Complete;
        }) None None in
        let full_body =
          List.fold_right
            (fun b acc -> mk_term (Lambda { arg = b; body = acc }) None None)
            (params @ [struct_arg])
            match_expr
        in
        Definition {
          def_name = name ^ "." ^ field.name;
          def_role = Runtime;
          def_type = full_type;
          def_body = full_body;
          rec_args = None;
          def_loc = None;
        }
      in
      
      (* Generate update functions for each field *)
      let make_updater field_idx (field : binder) =
        let struct_arg = { name = "s"; ty = struct_ty; role = Runtime; b_loc = None } in
        let new_val_arg = { name = "newVal"; ty = field.ty; role = Runtime; b_loc = None } in
        let full_type = 
          List.fold_right 
            (fun b acc -> mk_term (Pi { arg = b; result = acc }) None None)
            (params @ [struct_arg; new_val_arg])
            struct_ty
        in
        let pattern_args = List.mapi (fun i _f -> { arg_name = "f" ^ string_of_int i; arg_loc = None }) fields in
        let ctor_args = List.mapi (fun i _f ->
          if i = field_idx then mk_term (Var "newVal") None None
          else mk_term (Var ("f" ^ string_of_int i)) None None
        ) fields in
        let match_expr = mk_term (Match {
          scrutinee = mk_term (Var "s") None None;
          motive = struct_ty;
          as_name = None;
          cases = [{
            pattern = { ctor = name ^ ".mk"; args = pattern_args; pat_loc = None };
            body = mk_term (App (mk_term (Var (name ^ ".mk")) None None, ctor_args)) None None;
            case_loc = None;
          }];
          coverage_hint = Complete;
        }) None None in
        let full_body =
          List.fold_right
            (fun b acc -> mk_term (Lambda { arg = b; body = acc }) None None)
            (params @ [struct_arg; new_val_arg])
            match_expr
        in
        Definition {
          def_name = "_update_" ^ field.name;
          def_role = Runtime;
          def_type = full_type;
          def_body = full_body;
          rec_args = None;
          def_loc = None;
        }
      in
      
      let projections = List.mapi make_projection fields in
      let updaters = List.mapi make_updater fields in
      ind_decl :: projections @ updaters
      
  | _ -> raise (ParseError "Expected dataclass name")

(* Parse an abbreviation/type alias *)
let parse_abbrev state =
  expect state ABBREV "Expected 'abbrev'";
  match peek state with
  | IDENT name ->
      advance state;
      let params =
        match peek state with
        | LPAREN ->
            advance state;
            let p = parse_arg_list state in
            expect state RPAREN "Expected ')' in abbrev params";
            p
        | _ -> []
      in
      expect state ASSIGN "Expected '=' after abbrev name";
      let body = parse_type state in
      expect state NEWLINE "Expected newline after abbrev";
      (* Create a definition that returns a Type *)
      let full_type = List.fold_right 
        (fun b acc -> mk_term (Pi { arg = b; result = acc }) None None) 
        params 
        (mk_term (Universe Type) None None) in
      let full_body = List.fold_right 
        (fun b acc -> mk_term (Lambda { arg = b; body = acc }) None None) 
        params 
        body in
      Definition {
        def_name = name;
        def_role = Runtime;
        def_type = full_type;
        def_body = full_body;
        rec_args = None;
        def_loc = None;
      }
  | _ -> raise (ParseError "Expected abbrev name")

let parse_def state =
  expect state DEF "Expected 'def'";
  match peek state with
  | IDENT first_name ->
      advance state;
      (* Handle dotted names like Rot.cw *)
      let name = 
        match peek state with
        | DOT -> 
            advance state;
            (match peek state with
             | IDENT second_name -> advance state; first_name ^ "." ^ second_name
             | _ -> raise (ParseError "Expected method name after dot"))
        | _ -> first_name
      in
      (* Check if this is a value definition: def name : Type = body 
         or a function definition: def name(args) -> ret : body *)
      (match peek state with
       | COLON ->
           (* Value definition: def name : Type = body *)
           advance state;
           let ty = parse_type state in
           expect state ASSIGN "Expected '=' after type annotation";
           expect state NEWLINE "Expected newline after '='";
           let stmts = parse_block state (Some ty) in
           let body = fold_stmts stmts in
           Definition {
             def_name = name;
             def_role = Runtime;
             def_type = ty;
             def_body = body;
             rec_args = None;
             def_loc = None;
           }
       | LPAREN ->
           (* Function definition: def name(args) -> ret : body *)
           advance state;
           let args = parse_arg_list state in
           expect state RPAREN "Expected ')'";
           expect state ARROW "Expected '->'";
           let ret_ty = parse_type state in
           expect state COLON "Expected ':'";
           expect state NEWLINE "Expected newline after def";
           let stmts = parse_block state (Some ret_ty) in
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
       | _ -> raise (ParseError ("Expected '(' or ':' after definition name, got: " ^ (show_token (peek state)))))
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
  | AT ->
      (* @decorator - currently only @dataclass is supported *)
      advance state;
      (match peek state with
       | IDENT "dataclass" ->
           advance state;
           expect state NEWLINE "Expected newline after @dataclass";
           (* @dataclass class Name: is parsed as a struct *)
           (match peek state with
            | CLASS ->
                let struct_decls = parse_struct_as_class state in
                List.map (fun d -> Decl d) struct_decls @ parse_top_level_items state
            | _ -> raise (ParseError "Expected 'class' after @dataclass"))
       | IDENT name -> raise (ParseError ("Unknown decorator: @" ^ name))
       | _ -> raise (ParseError "Expected decorator name after @"))
  | CLASS ->
      let ind = parse_inductive state in
      Decl (Inductive ind) :: parse_top_level_items state
  | ENUM ->
      (* enum is an alias for class (inductive type) - more Pythonic for ADTs *)
      let ind = parse_inductive_with_enum state in
      Decl (Inductive ind) :: parse_top_level_items state
  | STRUCT ->
      let struct_decls = parse_struct state in
      List.map (fun d -> Decl d) struct_decls @ parse_top_level_items state
  | ABBREV ->
      let abbrev_decl = parse_abbrev state in
      Decl abbrev_decl :: parse_top_level_items state
  | DEF ->
      let def = parse_def state in
      Decl def :: parse_top_level_items state
  | THEOREM ->
      let thm = parse_theorem state in
      Decl thm :: parse_top_level_items state
  | _ -> raise (ParseError ("Unexpected token at top level: " ^ (show_token (peek state))))

let parse_program tokens =
  let state = init_parser tokens in
  let items = parse_top_level_items state in
  let imports = List.filter_map (function Import i -> Some i | _ -> None) items in
  let decls = List.filter_map (function Decl d -> Some d | _ -> None) items in
  { module_name = "Main"; imports; declarations = decls; module_loc = None }
