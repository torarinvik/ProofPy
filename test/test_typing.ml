(** Typing tests for CertiJSON. *)

open Alcotest
open Certijson

let test_identity_function () =
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
  | Error e -> fail (Json_parser.show_parse_error e)
  | Ok m ->
      match Typing.check_module m with
      | Error e -> fail (Typing.show_typing_error e)
      | Ok _ -> ()

let test_nat_definition () =
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
  | Error e -> fail (Json_parser.show_parse_error e)
  | Ok m ->
      match Typing.check_module m with
      | Error e -> fail (Typing.show_typing_error e)
      | Ok _ -> ()

let test_nat_plus_match () =
  let json = {|
    {
      "module": "Std.Nat",
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
        },
        {
          "def": {
            "name": "plus",
            "role": "runtime",
            "type": {
              "pi": {
                "arg": { "name": "n", "type": { "var": "Nat" } },
                "result": {
                  "pi": {
                    "arg": { "name": "m", "type": { "var": "Nat" } },
                    "result": { "var": "Nat" }
                  }
                }
              }
            },
            "body": {
              "lambda": {
                "arg": { "name": "n", "type": { "var": "Nat" } },
                "body": {
                  "lambda": {
                    "arg": { "name": "m", "type": { "var": "Nat" } },
                    "body": {
                      "match": {
                        "scrutinee": { "var": "n" },
                        "motive": { "var": "Nat" },
                        "as": "z",
                        "cases": [
                          {
                            "pattern": { "ctor": "zero", "args": [] },
                            "body": { "var": "m" }
                          },
                          {
                            "pattern": { "ctor": "succ", "args": [{ "name": "k" }] },
                            "body": {
                              "app": [
                                { "var": "succ" },
                                { "app": [{ "var": "plus" }, { "var": "k" }, { "var": "m" }] }
                              ]
                            }
                          }
                        ],
                        "coverage_hint": "complete"
                      }
                    }
                  }
                }
              }
            },
            "rec_args": [0]
          }
        }
      ]
    }
  |} in
  match Json_parser.parse_string json with
  | Error e -> fail (Json_parser.show_parse_error e)
  | Ok m -> (
      match Typing.check_module m with
      | Error e -> fail (Typing.show_typing_error e)
      | Ok _ -> ())

let () =
  run "Typing" [
    "basic", [
      test_case "identity function" `Quick test_identity_function;
      test_case "nat definition" `Quick test_nat_definition;
      test_case "nat plus match" `Quick test_nat_plus_match;
    ]
  ]
