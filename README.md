# ProofPy

**A proof-based programming language for agentic LLMs**

[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSE)
[![Status: Alpha](https://img.shields.io/badge/Status-Alpha-orange.svg)]()

---

## What is ProofPy?

ProofPy is a pure, total, dependently typed programming language designed **exclusively for use by AI coding agents**. It solves a fundamental problem in AI-assisted software development:

> **LLMs can generate code, but they cannot guarantee its correctness.**

ProofPy shifts the burden of correctness from the code generator (the LLM) to the code verifier (the kernel). An LLM can propose any code it wants; if it's wrong, the kernel rejects it. If a ProofPy module compiles, its theorems are mathematically valid and its runtime code is guaranteed to terminate without undefined behavior.

ProofPy compiles to **CertiJSON**, a JSON-based Intermediate Representation (IR) that serves as the backend language.

## ProofPy Syntax

ProofPy features a Python-like frontend syntax designed to be familiar and easy for LLMs to write, while compiling down to the core CertiJSON IR.

### Features

- **Indentation-based blocks**: Just like Python.
- **Function Definitions**: `def name(arg: Type, ...) -> ReturnType:`
- **Dependent Types**: `(x: Int32) -> Int32` (Pi types)
- **Refinement Types**: `{v: Int32 | v != 0}` (Subset types)
- **Control Flow**: `if cond: ... else: ...`, `return expr`
- **Implicit Return**: The last expression in a block is returned if it's not a statement.

### Examples

#### Basic Function

```python
def add(x: Int32, y: Int32) -> Int32:
    return x + y
```

#### Refinement Types

```python
def safe_div(x: Int32, y: {v: Int32 | v != 0}) -> Int32:
    return x / y
```

#### Control Flow

```python
def max(x: Int32, y: Int32) -> Int32:
    if x > y:
        x
    else:
        y
```

## Key Features

| Feature | Description |
|---------|-------------|
| 🐍 **ProofPy Syntax** | Python-like syntax for easy agent interaction |
| 🔧 **JSON IR** | Core language is JSON—trivial parsing, no ambiguity for tools |
| 🔒 **Proof-Based** | Curry–Howard correspondence: types = propositions, terms = proofs |
| ⚡ **C Interop** | Compiles to a safe C subset for real-world deployment |
| ⏱️ **Total** | All programs terminate—no infinite loops, no crashes |
| 🎯 **Deterministic** | Same inputs always produce same outputs |

## JSON Intermediate Representation (IR)

While agents write in ProofPy, the compiler uses **CertiJSON**, a JSON-based Intermediate Representation. This IR is unambiguous and easy for tools to process.

### Example IR (Addition)

```json
{
  "module": "Example",
  "imports": ["Std.Nat"],
  "declarations": [
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
```

## Architecture

```
┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐
│ ProofPy  │───▶│   JSON   │───▶│   Core   │───▶│ Runtime  │───▶│    C     │
│ (.cj)    │    │   IR     │    │  Terms   │    │   Core   │    │  Source  │
└──────────┘    └──────────┘    └──────────┘    └──────────┘    └──────────┘
            Parse           Parse &         Type Check &      Erase &        Extract &
                            Elaborate       Verify            Optimize       Lower
```

### Compilation Pipeline

1. **Frontend** — ProofPy (.cj) → JSON IR
2. **Parse** — JSON → Raw AST
3. **Elaborate** — Raw AST → Core terms
4. **Type Check** — Verify types, termination, proofs
5. **Erase** — Remove proof-only terms
6. **Extract** — Core → Cmini (safe C subset)
7. **Lower** — Cmini → C source code

## Type System

ProofPy features a dependently typed core with:

- **Two universes**: `Type` (computational) and `Prop` (logical)
- **Dependent functions**: `Π(x : A). B`
- **Inductive types**: Natural numbers, lists, options, etc.
- **Propositional equality**: `Eq_A(x, y)` with `refl` and `rewrite`
- **Structural recursion**: Guaranteed termination

## C Interoperability

ProofPy provides safe FFI through explicit representation descriptors:

```json
{
  "repr": {
    "name": "Int32Repr",
    "kind": "primitive",
    "c_type": "int32_t",
    "size_bits": 32,
    "signed": true
  }
}
```

```json
{
  "extern_c": {
    "name": "c_sin",
    "c_name": "sin",
    "header": "<math.h>",
    "signature": {
      "return": { "repr": "Float64Repr" },
      "args": [{ "name": "x", "repr": "Float64Repr" }]
    },
    "type": { "pi": { "arg": { "name": "_", "type": { "var": "Float64" } }, "result": { "var": "Float64" } } },
    "safety": "pure"
  }
}
```

## Effects and Concurrency

- **World-passing IO**: Deterministic effects via `IO A = World → (A, World)`
- **Linear arrays**: Mutable arrays with ownership tracking
- **Structured concurrency**: `spawn`, `join`, `par` with deterministic semantics

## Documentation

- 📖 [Full Specification](formal_specs.md) — Complete language specification
- 🔧 [Standard Library](formal_specs.md#19-standard-library) — Bool, Nat, List, Option, Pair, Result
- 🤖 [Agent Profile](formal_specs.md#18-agent-profile) — Guidelines for LLM code generation

## Design Goals

| Goal | Description |
|------|-------------|
| **G1. Logical Soundness** | Types are propositions, terms are proofs |
| **G2. Totality** | All programs terminate |
| **G3. Separation** | Clear split between proofs (`Prop`) and code (`Type`) |
| **G4. Safe C Interop** | Explicit memory layouts, no undefined behavior |
| **G5. LLM-Optimized** | Python-like syntax for ease of use, JSON IR for tool reliability |

## Status

ProofPy is currently in **alpha** stage. The specification is stable, but the reference implementation is under development.

### Roadmap

- [x] Core type theory specification
- [x] JSON concrete syntax (IR)
- [x] ProofPy frontend syntax
- [x] C interop design (repr, extern_c)
- [x] Effects and IO model
- [x] Concurrency primitives
- [ ] Reference compiler implementation
- [ ] Standard library implementation
- [ ] IDE tooling
- [ ] Mechanized metatheory proofs

## Contributing

Contributions are welcome! Areas of interest:

- Reference compiler (OCaml)
- Standard library modules
- Example programs and proofs
- Documentation improvements
- Mechanized proofs (Coq/Agda)

## License

MIT License — see [LICENSE](LICENSE) for details.

## Acknowledgments

ProofPy draws inspiration from:

- [Coq](https://coq.inria.fr/) — Dependent types and proof assistants
- [Lean](https://leanprover.github.io/) — Modern proof assistant design
- [Idris](https://www.idris-lang.org/) — Dependently typed programming
- [CompCert](https://compcert.org/) — Verified C compilation

---

<p align="center">
  <em>Making LLM-generated code provably correct.</em>
</p>
