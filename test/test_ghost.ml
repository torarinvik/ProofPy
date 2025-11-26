(** Ghost Parameter tests for CertiJSON. *)

open Alcotest
open Certijson

let check_module m = Typing.check_module m (Context.empty_sig ())

let test_ghost_param_usage_in_runtime () =
  let json = {|
    {
      "module": "TestGhost",
      "imports": [],
      "declarations": [
        {
          "def": {
            "name": "bad_ghost_usage",
            "role": "runtime",
            "type": {
              "pi": {
                "arg": { "name": "x", "type": { "universe": "Type" }, "role": "proof-only" },
                "result": { "universe": "Type" }
              }
            },
            "body": {
              "lambda": {
                "arg": { "name": "x", "type": { "universe": "Type" }, "role": "proof-only" },
                "body": { "var": "x" }
              }
            }
          }
        }
      ]
    }
  |} in
  match Json_parser.parse_string json with
  | Error e -> fail (Json_parser.show_parse_error e)
  | Ok m -> (
      match check_module m with
      | Ok _ -> fail "expected role mismatch error"
      | Error (Typing.RoleMismatch ("x", Syntax.Runtime, Syntax.ProofOnly)) -> ()
      | Error (Typing.InDeclaration ("bad_ghost_usage", _, Typing.RoleMismatch ("x", Syntax.Runtime, Syntax.ProofOnly))) -> ()
      | Error e -> fail (Typing.string_of_typing_error e))

let test_ghost_param_usage_in_proof () =
  let json = {|
    {
      "module": "TestGhost",
      "imports": [],
      "declarations": [
        {
          "def": {
            "name": "good_ghost_usage",
            "role": "proof-only",
            "type": {
              "pi": {
                "arg": { "name": "x", "type": { "universe": "Type" }, "role": "proof-only" },
                "result": { "universe": "Type" }
              }
            },
            "body": {
              "lambda": {
                "arg": { "name": "x", "type": { "universe": "Type" }, "role": "proof-only" },
                "body": { "var": "x" }
              }
            }
          }
        }
      ]
    }
  |} in
  match Json_parser.parse_string json with
  | Error e -> fail (Json_parser.show_parse_error e)
  | Ok m -> (
      match check_module m with
      | Error e -> fail (Typing.string_of_typing_error e)
      | Ok _ -> ())

let test_ghost_param_application () =
  let json = {|
    {
      "module": "TestGhost",
      "imports": [],
      "declarations": [
        {
          "def": {
            "name": "ghost_id",
            "role": "runtime",
            "type": {
              "pi": {
                "arg": { "name": "x", "type": { "universe": "Type" }, "role": "proof-only" },
                "result": { "universe": "Type" }
              }
            },
            "body": {
              "lambda": {
                "arg": { "name": "x", "type": { "universe": "Type" }, "role": "proof-only" },
                "body": { "universe": "Type" }
              }
            }
          }
        },
        {
          "def": {
            "name": "use_ghost",
            "role": "runtime",
            "type": { "universe": "Type" },
            "body": {
              "app": [
                { "var": "ghost_id" },
                { "universe": "Type" }
              ]
            }
          }
        }
      ]
    }
  |} in
  match Json_parser.parse_string json with
  | Error e -> fail (Json_parser.show_parse_error e)
  | Ok m -> (
      match check_module m with
      | Error e -> fail (Typing.string_of_typing_error e)
      | Ok _ -> ())

let () =
  run "Ghost Parameters" [
    "basic", [
      test_case "runtime usage of ghost param fails" `Quick test_ghost_param_usage_in_runtime;
      test_case "proof usage of ghost param succeeds" `Quick test_ghost_param_usage_in_proof;
      test_case "application with ghost param succeeds" `Quick test_ghost_param_application;
    ]
  ]
