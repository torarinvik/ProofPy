(** Parser tests for CertiJSON. *)

open Alcotest
open Certijson

let test_minimal_module () =
  let json = {|
    {
      "module": "Test",
      "imports": [],
      "declarations": []
    }
  |} in
  match Json_parser.parse_string json with
  | Ok m ->
      check string "module name" "Test" m.Syntax.module_name;
      check (list string) "imports" [] m.imports;
      check int "declarations" 0 (List.length m.declarations)
  | Error e ->
      fail (Json_parser.show_parse_error e)

let test_variable () =
  let json = {|
    {
      "module": "Test",
      "imports": [],
      "declarations": [
        {
          "def": {
            "name": "id",
            "type": {
              "pi": {
                "arg": { "name": "A", "type": { "universe": "Type" } },
                "result": {
                  "pi": {
                    "arg": { "name": "x", "type": { "var": "A" } },
                    "result": { "var": "A" }
                  }
                }
              }
            },
            "body": {
              "lambda": {
                "arg": { "name": "A", "type": { "universe": "Type" } },
                "body": {
                  "lambda": {
                    "arg": { "name": "x", "type": { "var": "A" } },
                    "body": { "var": "x" }
                  }
                }
              }
            }
          }
        }
      ]
    }
  |} in
  match Json_parser.parse_string json with
  | Ok m ->
      check string "module name" "Test" m.Syntax.module_name;
      check int "declarations" 1 (List.length m.declarations)
  | Error e ->
      fail (Json_parser.show_parse_error e)

let test_inductive () =
  let json = {|
    {
      "module": "Test",
      "imports": [],
      "declarations": [
        {
          "inductive": {
            "name": "Nat",
            "params": [],
            "universe": "Type",
            "constructors": [
              { "name": "zero", "args": [] },
              { "name": "succ", "args": [{ "name": "n", "type": { "var": "Nat" } }] }
            ]
          }
        }
      ]
    }
  |} in
  match Json_parser.parse_string json with
  | Ok m ->
      check int "declarations" 1 (List.length m.declarations);
      (match List.hd m.declarations with
      | Syntax.Inductive ind ->
          check string "inductive name" "Nat" ind.ind_name;
          check int "constructors" 2 (List.length ind.constructors)
      | _ -> fail "expected inductive declaration")
  | Error e ->
      fail (Json_parser.show_parse_error e)

let test_literals () =
  let json = {|
    {
      "module": "Test",
      "imports": [],
      "declarations": [
        {
          "def": {
            "name": "forty_two",
            "type": { "var": "Int32" },
            "body": { "int32": 42 }
          }
        }
      ]
    }
  |} in
  match Json_parser.parse_string json with
  | Ok m ->
      check int "declarations" 1 (List.length m.declarations)
  | Error e ->
      fail (Json_parser.show_parse_error e)

let () =
  run "Parser" [
    "basic", [
      test_case "minimal module" `Quick test_minimal_module;
      test_case "variable and lambda" `Quick test_variable;
      test_case "inductive type" `Quick test_inductive;
      test_case "literals" `Quick test_literals;
    ]
  ]
