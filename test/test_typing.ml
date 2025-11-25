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
      | Error e -> fail (Typing.string_of_typing_error e)
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
      | Error e -> fail (Typing.string_of_typing_error e)
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
      | Error e -> fail (Typing.string_of_typing_error e)
      | Ok _ -> ())

let test_recursion_without_rec_args () =
  let json = {|
    {
      "module": "Test",
      "imports": [],
      "declarations": [
        {
          "def": {
            "name": "bad",
            "type": {
              "pi": {
                "arg": { "name": "n", "type": { "universe": "Type" } },
                "result": { "universe": "Type" }
              }
            },
            "body": {
              "lambda": {
                "arg": { "name": "n", "type": { "universe": "Type" } },
                "body": { "app": [{ "var": "bad" }, { "var": "n" }] }
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
      match Typing.check_module m with
      | Ok _ -> fail "expected termination failure"
      | Error (Typing.TerminationCheckFailed "bad") -> ()
      | Error (Typing.InDeclaration ("bad", _, Typing.TerminationCheckFailed "bad")) -> ()
      | Error e -> fail (Typing.string_of_typing_error e))

let test_positivity_failure () =
  let json = {|
    {
      "module": "Test",
      "imports": [],
      "declarations": [
        {
          "inductive": {
            "name": "Bad",
            "params": [],
            "universe": "Type",
            "constructors": [
              {
                "name": "mk",
                "args": [
                  {
                    "name": "f",
                    "type": {
                      "pi": {
                        "arg": { "name": "_", "type": { "var": "Bad" } },
                        "result": { "universe": "Type" }
                      }
                    }
                  }
                ]
              }
            ]
          }
        }
      ]
    }
  |} in
  match Json_parser.parse_string json with
  | Error e -> fail (Json_parser.show_parse_error e)
  | Ok m -> (
      match Typing.check_module m with
      | Ok _ -> fail "expected positivity failure"
      | Error (Typing.PositivityCheckFailed ("Bad", "f")) -> ()
      | Error (Typing.InDeclaration ("Bad", _, Typing.PositivityCheckFailed ("Bad", "f"))) -> ()
      | Error e -> fail (Typing.string_of_typing_error e))

let test_rec_arg_not_inductive () =
  let json = {|
    {
      "module": "Test",
      "imports": [],
      "declarations": [
        {
          "def": {
            "name": "bad_rec",
            "rec_args": [0],
            "type": {
              "pi": {
                "arg": { "name": "x", "type": { "universe": "Type" } },
                "result": { "universe": "Type" }
              }
            },
            "body": {
              "lambda": {
                "arg": { "name": "x", "type": { "universe": "Type" } },
                "body": { "app": [{ "var": "bad_rec" }, { "var": "x" }] }
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
      match Typing.check_module m with
      | Ok _ -> fail "expected rec_args inductive failure"
      | Error (Typing.RecArgNotInductive ("bad_rec", 0)) -> ()
      | Error (Typing.InDeclaration ("bad_rec", _, Typing.RecArgNotInductive ("bad_rec", 0))) -> ()
      | Error e -> fail (Typing.string_of_typing_error e))

let test_simple_refl_theorem () =
  let json = {|
    {
      "module": "Test",
      "imports": [],
      "declarations": [
        {
          "inductive": {
            "name": "Bool",
            "params": [],
            "universe": "Type",
            "constructors": [
              { "name": "true", "args": [] },
              { "name": "false", "args": [] }
            ]
          }
        },
        {
          "theorem": {
            "name": "true_eq_true",
            "type": {
              "eq": {
                "type": { "var": "Bool" },
                "lhs": { "var": "true" },
                "rhs": { "var": "true" }
              }
            },
            "proof": {
              "refl": {
                "eq": {
                  "type": { "var": "Bool" },
                  "lhs": { "var": "true" }
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
      match Typing.check_module m with
      | Error e -> fail (Typing.string_of_typing_error e)
      | Ok _ -> ())

let test_computational_refl_theorem () =
  let json = {|
    {
      "module": "Test",
      "imports": [],
      "declarations": [
        {
          "inductive": {
            "name": "Bool",
            "params": [],
            "universe": "Type",
            "constructors": [
              { "name": "true", "args": [] },
              { "name": "false", "args": [] }
            ]
          }
        },
        {
          "def": {
            "name": "not",
            "role": "runtime",
            "type": {
              "pi": {
                "arg": { "name": "b", "type": { "var": "Bool" } },
                "result": { "var": "Bool" }
              }
            },
            "body": {
              "lambda": {
                "arg": { "name": "b", "type": { "var": "Bool" } },
                "body": {
                  "match": {
                    "scrutinee": { "var": "b" },
                    "motive": { "var": "Bool" },
                    "as": "z",
                    "cases": [
                      { "pattern": { "ctor": "true", "args": [] }, "body": { "var": "false" } },
                      { "pattern": { "ctor": "false", "args": [] }, "body": { "var": "true" } }
                    ],
                    "coverage_hint": "complete"
                  }
                }
              }
            }
          }
        },
        {
          "theorem": {
            "name": "not_not_true",
            "type": {
              "eq": {
                "type": { "var": "Bool" },
                "lhs": { "app": [{ "var": "not" }, { "app": [{ "var": "not" }, { "var": "true" }] }] },
                "rhs": { "var": "true" }
              }
            },
            "proof": {
              "refl": {
                "eq": {
                  "type": { "var": "Bool" },
                  "lhs": { "var": "true" }
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
      match Typing.check_module m with
      | Error e -> fail (Typing.string_of_typing_error e)
      | Ok _ -> ())

let test_refl_type_mismatch () =
  let json = {|
    {
      "module": "Test",
      "imports": [],
      "declarations": [
        {
          "inductive": {
            "name": "Bool",
            "params": [],
            "universe": "Type",
            "constructors": [
              { "name": "true", "args": [] },
              { "name": "false", "args": [] }
            ]
          }
        },
        {
          "theorem": {
            "name": "bad_theorem",
            "type": {
              "eq": {
                "type": { "var": "Bool" },
                "lhs": { "var": "true" },
                "rhs": { "var": "false" }
              }
            },
            "proof": {
              "refl": {
                "eq": {
                  "type": { "var": "Bool" },
                  "lhs": { "var": "true" }
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
      match Typing.check_module m with
      | Ok _ -> fail "expected type mismatch"
      | Error (Typing.TypeMismatch _) -> ()
      | Error (Typing.InDeclaration ("bad_theorem", _, Typing.TypeMismatch _)) -> ()
      | Error e -> fail (Typing.string_of_typing_error e))

let () =
  run "Typing" [
    "basic", [
      test_case "identity function" `Quick test_identity_function;
      test_case "nat definition" `Quick test_nat_definition;
      test_case "nat plus match" `Quick test_nat_plus_match;
      test_case "recursion without rec_args" `Quick test_recursion_without_rec_args;
      test_case "positivity failure" `Quick test_positivity_failure;
      test_case "rec_args not inductive" `Quick test_rec_arg_not_inductive;
    ];
    "theorems", [
      test_case "simple refl theorem" `Quick test_simple_refl_theorem;
      test_case "computational refl theorem" `Quick test_computational_refl_theorem;
      test_case "refl type mismatch" `Quick test_refl_type_mismatch;
    ]
  ]
