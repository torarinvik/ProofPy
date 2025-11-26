open Alcotest
open Certijson

let check_module m = Typing.check_module m (Context.empty_sig ())

let test_refinement_valid () =
  let json = {|
    {
      "module": "TestRefinement",
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
            "name": "ZeroType",
            "type": { "universe": "Type" },
            "body": {
              "subset": {
                "arg": { "name": "x", "type": { "var": "Nat" } },
                "pred": {
                  "eq": {
                    "type": { "var": "Nat" },
                    "lhs": { "var": "x" },
                    "rhs": { "var": "zero" }
                  }
                }
              }
            }
          }
        },
        {
          "def": {
            "name": "z",
            "type": { "var": "ZeroType" },
            "body": {
              "subset_intro": {
                "value": { "var": "zero" },
                "proof": {
                  "refl": {
                    "eq": {
                      "type": { "var": "Nat" },
                      "lhs": { "var": "zero" }
                    }
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
  | Ok m -> (
      match check_module m with
      | Error e -> fail (Typing.string_of_typing_error e)
      | Ok _ -> ())

let test_refinement_invalid () =
  let json = {|
    {
      "module": "TestRefinementInvalid",
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
            "name": "ZeroType",
            "type": { "universe": "Type" },
            "body": {
              "subset": {
                "arg": { "name": "x", "type": { "var": "Nat" } },
                "pred": {
                  "eq": {
                    "type": { "var": "Nat" },
                    "lhs": { "var": "x" },
                    "rhs": { "var": "zero" }
                  }
                }
              }
            }
          }
        },
        {
          "def": {
            "name": "bad_z",
            "type": { "var": "ZeroType" },
            "body": {
              "subset_intro": {
                "value": { "app": [{ "var": "succ" }, { "var": "zero" }] },
                "proof": {
                  "refl": {
                    "eq": {
                      "type": { "var": "Nat" },
                      "lhs": { "var": "zero" }
                    }
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
  | Ok m -> (
      match check_module m with
      | Ok _ -> fail "expected type mismatch"
      | Error (Typing.TypeMismatch _) -> ()
      | Error (Typing.InDeclaration ("bad_z", _, Typing.TypeMismatch _)) -> ()
      | Error e -> fail (Typing.string_of_typing_error e))

let () =
  run "Refinement" [
    "basic", [
      test_case "valid refinement" `Quick test_refinement_valid;
      test_case "invalid refinement" `Quick test_refinement_invalid;
    ]
  ]
