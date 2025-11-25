(** CertiJSON compiler command-line interface. *)

open Cmdliner

(** {1 Commands} *)

let check_cmd =
  let file =
    let doc = "The CertiJSON source file to check." in
    Arg.(required & pos 0 (some file) None & info [] ~docv:"FILE" ~doc)
  in
  let check file =
    match Certijson.Json_parser.parse_file file with
    | Error e ->
        Fmt.epr "Parse error: %s@." (Certijson.Json_parser.show_parse_error e);
        `Error (false, "parsing failed")
    | Ok mod_ ->
        Fmt.pr "Parsed module: %s@." mod_.module_name;
        Fmt.pr "Imports: %a@."
          Fmt.(list ~sep:comma string) mod_.imports;
        Fmt.pr "Declarations: %d@." (List.length mod_.declarations);
        match Certijson.Typing.check_module mod_ with
        | Error e ->
            Fmt.epr "Type error: %s@." (Certijson.Typing.show_typing_error e);
            `Error (false, "type checking failed")
        | Ok _sig ->
            Fmt.pr "✓ Module type-checked successfully@.";
            `Ok ()
  in
  let doc = "Type-check a CertiJSON source file." in
  let info = Cmd.info "check" ~doc in
  Cmd.v info Term.(ret (const check $ file))

let parse_cmd =
  let file =
    let doc = "The CertiJSON source file to parse." in
    Arg.(required & pos 0 (some file) None & info [] ~docv:"FILE" ~doc)
  in
  let parse file =
    match Certijson.Json_parser.parse_file file with
    | Error e ->
        Fmt.epr "Parse error: %s@." (Certijson.Json_parser.show_parse_error e);
        `Error (false, "parsing failed")
    | Ok mod_ ->
        Fmt.pr "%s@." (Certijson.Pretty.module_to_string mod_);
        `Ok ()
  in
  let doc = "Parse and pretty-print a CertiJSON source file." in
  let info = Cmd.info "parse" ~doc in
  Cmd.v info Term.(ret (const parse $ file))

let eval_cmd =
  let file =
    let doc = "The CertiJSON source file containing the term to evaluate." in
    Arg.(required & pos 0 (some file) None & info [] ~docv:"FILE" ~doc)
  in
  let def_name =
    let doc = "The name of the definition to evaluate." in
    Arg.(required & pos 1 (some string) None & info [] ~docv:"NAME" ~doc)
  in
  let do_eval file def_name =
    match Certijson.Json_parser.parse_file file with
    | Error e ->
        Fmt.epr "Parse error: %s@." (Certijson.Json_parser.show_parse_error e);
        `Error (false, "parsing failed")
    | Ok mod_ ->
        match Certijson.Typing.check_module mod_ with
        | Error e ->
            Fmt.epr "Type error: %s@." (Certijson.Typing.show_typing_error e);
            `Error (false, "type checking failed")
        | Ok sig_ ->
            let ctx = Certijson.Context.make_ctx sig_ in
            let term = Certijson.Syntax.Global def_name in
            let result = Certijson.Eval.normalize ctx term in
            Fmt.pr "%s@." (Certijson.Pretty.term_to_string result);
            `Ok ()
  in
  let doc = "Evaluate a definition from a CertiJSON source file." in
  let cmd_info = Cmd.info "eval" ~doc in
  Cmd.v cmd_info Term.(ret (const do_eval $ file $ def_name))

(** {1 Main} *)

let () =
  let doc = "A proof-based programming language for agentic LLMs" in
  let info = Cmd.info "certijson" ~version:"0.1.0" ~doc in
  let cmds = [check_cmd; parse_cmd; eval_cmd] in
  exit (Cmd.eval (Cmd.group info cmds))
