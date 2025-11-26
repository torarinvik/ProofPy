# CertiJSON Language Specification

**Version:** 1.0-alpha  
**Status:** Draft Specification  
**Last Updated:** November 2025

---

## Overview

**CertiJSON** is a pure, total, dependently typed programming language designed exclusively for use by agentic LLMs. It addresses a fundamental challenge in AI-assisted software development: **LLMs can generate code, but they cannot guarantee its correctness**.

CertiJSON solves this by requiring all code to carry machine-checkable proofs. If a CertiJSON module passes the kernel's type checker, its theorems are mathematically valid and its runtime code is guaranteed to terminate without undefined behavior.

### Key Features

| Feature | Description | Benefit |
|---------|-------------|----------|
| **JSON Syntax** | All programs are valid JSON | Trivial parsing, no ambiguity |
| **Proof-Based** | Curry–Howard: types = propositions | Mathematical correctness guarantees |
| **C Interop** | Compiles to safe C subset | Real-world deployment |
| **Total** | All programs terminate | No infinite loops, no crashes |
| **Deterministic** | Same inputs → same outputs | Reproducible, testable behavior |

### Why CertiJSON?

Traditional programming languages trust the programmer. When an LLM writes code, that trust is misplaced—LLMs make mistakes, hallucinate APIs, and produce subtle bugs. CertiJSON shifts the burden of correctness from the code generator (the LLM) to the code verifier (the kernel). An LLM can propose any code it wants; if it's wrong, the kernel rejects it.

> **Core Guarantee:** If a CertiJSON module compiles, its theorems are valid and its runtime code is safe.

---

## Quick Reference for LLM Agents

<details>
<summary><strong>Click to expand: Essential patterns for code generation</strong></summary>

### Minimal Valid Module
```json
{
  "module": "Example",
  "imports": [],
  "declarations": []
}
```

### Common Term Patterns
```json
// Variable reference
{ "var": "x" }

// Function type: A → B
{ "pi": { "arg": { "name": "_", "type": A }, "result": B } }

// Lambda: λx. body
{ "lambda": { "arg": { "name": "x", "type": T }, "body": BODY } }

// Application: f x y
{ "app": [{ "var": "f" }, { "var": "x" }, { "var": "y" }] }

// Pattern match (always exhaustive!)
{ "match": { "scrutinee": TERM, "motive": TYPE, "as": "z",
    "cases": [...], "coverage_hint": "complete" } }
```

### Declaration Checklist
- ✅ Every `def` needs `name`, `type`, `body`
- ✅ Recursive functions need `rec_args: [index]`
- ✅ Pattern matches must cover ALL constructors
- ✅ Proofs go in `theorem`, runtime code in `def`

</details>

---

## Table of Contents

### Part I: Core Language
1. [Design Goals](#1-design-goals)
2. [Abstract Syntax](#2-abstract-syntax)
3. [JSON Concrete Syntax](#3-json-concrete-syntax)
4. [Typing Rules](#4-typing-rules)
5. [Definitional Equality](#5-definitional-equality)
6. [Evaluation Semantics](#6-evaluation-semantics)
7. [Termination and Structural Recursion](#7-termination-and-structural-recursion)

### Part II: C Interoperability
8. [Representation Layer (repr)](#8-representation-layer)
9. [Foreign Function Interface (extern_c)](#9-foreign-function-interface)
10. [Erasure](#10-erasure)
11. [Target Language: Cmini](#11-target-language-cmini)
12. [Extraction](#12-extraction)

### Part III: Effects and Concurrency
13. [Effects and IO](#13-effects-and-io)
14. [Mutable Arrays](#14-mutable-arrays)
15. [Concurrency](#15-concurrency)

### Part IV: Implementation
16. [Compilation Pipeline](#16-compilation-pipeline)
17. [Trusted Computing Base](#17-trusted-computing-base)
18. [Agent Profile](#18-agent-profile)
19. [Standard Library](#19-standard-library)
20. [Meta-Theoretic Goals](#20-meta-theoretic-goals)
21. [Correctness Levels and Verification Modes](#21-correctness-levels-and-verification-modes)

### Part V: Advanced Verification
22. [Refinement Types](#22-refinement-types)
23. [Ghost Parameters](#23-ghost-parameters)
24. [Sized Arrays](#24-sized-arrays)

### Appendices
- [A: JSON Examples](#appendix-a-json-examples)
- [B: Version History](#appendix-b-version-history)
- [C: Future Directions](#appendix-c-future-directions)
- [D: Error Messages](#appendix-d-common-errors)
- [E: Glossary](#appendix-e-glossary)

---

## 1. Design Goals

CertiJSON is built around five core principles that ensure correctness, safety, and LLM-friendliness.

### G1. Logical Soundness 🔒

> **Principle:** Types are propositions, terms are proofs. If code compiles, proofs are valid.

| Concept | Meaning |
|---------|---------|
| **Curry–Howard** | Code and proofs are the same thing |
| **Prop** | Universe of propositions (proof-only, erased at runtime) |
| **Type** | Universe of computational types (values that exist at runtime) |

**Guarantee:** If a module is accepted by the kernel, every `theorem` is mathematically valid.

### G2. Total, Deterministic Core ⏱️

> **Principle:** All programs terminate. No infinite loops, no undefined behavior.

- No general recursion — only structurally terminating definitions
- Evaluation is deterministic and strongly normalizing
- Same inputs always produce same outputs

### G3. Clean Separation of Logic and Computation 🔀

> **Principle:** Proofs and runtime code are clearly separated.

| Item | Role |
|------|------|
| `Prop` | Proof-only (completely erased at runtime) |
| `Type` | Runtime data (compiled to C) |
| Extraction | Removes all `Prop` terms and `proof-only` definitions |

### G4. Safe and Deterministic C Interop 🔗

> **Principle:** Interact with C safely through explicit type layouts.

- **repr declarations** — Specify exact memory layout for C types
- **extern_c declarations** — Bind logical functions to C functions
- **Cmini target** — Extracted C is restricted to a small, UB-free subset

### G5. LLM-Optimized Syntax 🤖

> **Principle:** Make parsing trivial for language models.

- All programs are valid JSON
- No precedence or layout rules to memorize
- Small, fixed set of node kinds
- Canonical formatting (no stylistic choices)

---

## 2. Abstract Syntax

The type theory is defined at the level of **abstract syntax**. JSON is a serialization of these terms.

### 2.1 Universes

- **Type** — Universe of computational types
- **Prop** — Universe of propositions

### 2.2 Naming Conventions

- **Variables**: `x, y, z, f, g, ...`
- **Types**: `A, B, C, ...`
- **Terms**: `t, u, v, ...`
- **Inductive names**: `I, J, ...`
- **Constructors**: `c, d, ...`
- **Global constants**: `cst`

### 2.3 Primitive Types and Literals

Primitive types (all in `Type`):

| Type | Description |
|------|-------------|
| `Int32` | 32-bit signed integer |
| `Int64` | 64-bit signed integer |
| `Float64` | 64-bit IEEE floating point |
| `Bool` | Boolean |
| `Size` | Platform-sized unsigned integer |

Primitive literals:

| Literal | Type |
|---------|------|
| `int32(n)` | `Int32` |
| `int64(n)` | `Int64` |
| `float64(f)` | `Float64` |
| `bool(b)` | `Bool` |

### 2.4 Terms

Abstract term grammar:

```
t ::= x                                          (variable)
    | Type | Prop                                (universes)
    | Π(x : A). B                                (dependent function type)
    | λ(x : A). t                                (lambda abstraction)
    | t u                                        (application, left-associative)
    | Eq_A(u, v)                                 (equality type, in Prop)
    | refl_A(u)                                  (reflexivity proof)
    | rewrite e in t                             (equality elimination)
    | cst                                        (global constant/constructor)
    | match t₀ as z return P with cases          (pattern match)
    | int32(n) | int64(n) | float64(f) | bool(b) (primitive literals)
```

### 2.5 Derived Forms

- `forall (x : A). B` ≜ `Π(x : A). B`
- `A → B` ≜ `Π(_ : A). B`

---

## 3. JSON Concrete Syntax

### 3.1 Module Structure

A CertiJSON module is a JSON object:

```json
{
  "module": "ModuleName",
  "imports": ["OtherModule1", "OtherModule2"],
  "declarations": [...]
}
```

**Constraints:**
- `"module"`: Required, non-empty string, valid identifier
- `"imports"`: Optional array of module names (default: empty)
- `"declarations"`: Required array of declaration objects

### 3.2 Term JSON Nodes

#### Variable

```json
{ "var": "x" }
```

#### Universe

```json
{ "universe": "Type" }
{ "universe": "Prop" }
```

#### Π-type (Dependent Function Type)

```json
{
  "pi": {
    "arg": { "name": "x", "type": <type_term> },
    "result": <result_term>
  }
}
```

#### Forall (Sugar for Π)

```json
{
  "forall": {
    "arg": { "name": "x", "type": <type_term> },
    "result": <result_term>
  }
}
```

#### Lambda

```json
{
  "lambda": {
    "arg": { "name": "x", "type": <type_term> },
    "body": <body_term>
  }
}
```

#### Application

```json
{ "app": [<func>, <arg1>, <arg2>, ...] }
```

Array length ≥ 2. Left-associative: `[f, a, b]` = `((f a) b)`.

#### Equality Type

```json
{
  "eq": {
    "type": <A>,
    "lhs": <u>,
    "rhs": <v>
  }
}
```

#### Reflexivity

```json
{
  "refl": {
    "eq": {
      "type": <A>,
      "lhs": <u>,
      "rhs": <v>
    }
  }
}
```

Side condition: `lhs` and `rhs` must be definitionally equal.

#### Rewrite (Equality Elimination)

```json
{
  "rewrite": {
    "proof": <equality_proof>,
    "in": <body_term>
  }
}
```

#### Match (Pattern Matching)

```json
{
  "match": {
    "scrutinee": <term>,
    "motive": <motive_term>,
    "as": "z",
    "cases": [
      {
        "pattern": {
          "ctor": "ConstructorName",
          "args": [{ "name": "y1" }, { "name": "y2" }]
        },
        "body": <branch_term>
      }
    ],
    "coverage_hint": "complete"
  }
}
```

- `"as"`: Optional (fresh name generated if omitted)
- `"coverage_hint"`: Optional, `"complete"` or `"unknown"`

#### Literals

```json
{ "int32": 123 }
{ "int64": 1234567890 }
{ "float64": 3.14 }
{ "bool": true }
```

### 3.3 Declaration Types

#### Inductive Type

```json
{
  "inductive": {
    "name": "TypeName",
    "params": [
      { "name": "A", "type": { "universe": "Type" } }
    ],
    "universe": "Type",
    "constructors": [
      {
        "name": "ConstructorName",
        "args": [
          { "name": "x", "type": <type_term> }
        ]
      }
    ]
  }
}
```

#### Definition

```json
{
  "def": {
    "name": "functionName",
    "role": "runtime",
    "type": <type_term>,
    "body": <body_term>,
    "rec_args": [0]
  }
}
```

- `"role"`: `"runtime"` | `"proof-only"` | `"both"` (default: `"both"`)
- `"rec_args"`: Optional array of indices designating structurally recursive arguments

#### Theorem

```json
{
  "theorem": {
    "name": "theoremName",
    "type": <proposition_term>,
    "proof": <proof_term>
  }
}
```

Equivalent to `def` with `role = "proof-only"`.

#### Representation Descriptor

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
  "repr": {
    "name": "Point2DRepr",
    "kind": "struct",
    "c_struct_name": "Point2D",
    "size_bytes": 8,
    "align_bytes": 4,
    "fields": [
      { "name": "x", "repr": "Int32Repr", "offset_bytes": 0 },
      { "name": "y", "repr": "Int32Repr", "offset_bytes": 4 }
    ]
  }
}
```

#### External C Function

```json
{
  "extern_c": {
    "name": "c_sin",
    "c_name": "sin",
    "header": "<math.h>",
    "signature": {
      "return": { "repr": "Float64Repr" },
      "args": [
        { "name": "x", "repr": "Float64Repr" }
      ]
    },
    "type": <logical_type>,
    "safety": "pure",
    "axioms": []
  }
}
```

- `"safety"`: `"pure"` | `"impure"`

---

## 4. Typing Rules

### 4.1 Judgment Form

```
Σ; Γ ⊢ t : A
```

Where:
- `Σ` is the global signature (inductives, definitions, constants)
- `Γ` is the local context (variable bindings)
- `t` is a term
- `A` is a type

### 4.2 Context Formation

- `·` is a valid context (empty)
- If `Σ; Γ ⊢ A : Type_i`, then `Γ, x : A` is valid (with `x` fresh)

### 4.3 Core Typing Rules

#### Variable

```
(x : A) ∈ Γ
─────────────────
Σ; Γ ⊢ x : A
```

#### Universe

```
─────────────────────
Σ; Γ ⊢ Type : Type
```

```
─────────────────────
Σ; Γ ⊢ Prop : Type
```

#### Π-Type Formation

```
Σ; Γ ⊢ A : Type    Σ; Γ, x : A ⊢ B : Type
──────────────────────────────────────────
Σ; Γ ⊢ Π(x : A). B : Type
```

For Prop formation:
- If `A : Type` or `Prop`, and `B : Prop`, then `Π(x : A). B : Prop`

#### Lambda Introduction

```
Σ; Γ, x : A ⊢ t : B
───────────────────────────────────
Σ; Γ ⊢ λ(x : A). t : Π(x : A). B
```

#### Application

```
Σ; Γ ⊢ f : Π(x : A). B    Σ; Γ ⊢ u : A
─────────────────────────────────────────
Σ; Γ ⊢ f u : B[x := u]
```

#### Conversion

```
Σ; Γ ⊢ t : A    Σ; Γ ⊢ A ≡ B
────────────────────────────────
Σ; Γ ⊢ t : B
```

#### Equality Formation

```
Σ; Γ ⊢ A : Type    Σ; Γ ⊢ u : A    Σ; Γ ⊢ v : A
─────────────────────────────────────────────────
Σ; Γ ⊢ Eq_A(u, v) : Prop
```

#### Reflexivity Introduction

```
Σ; Γ ⊢ A : Type    Σ; Γ ⊢ u : A
─────────────────────────────────
Σ; Γ ⊢ refl_A(u) : Eq_A(u, u)
```

#### Rewrite (Equality Elimination)

Given:
1. `Σ; Γ ⊢ e : Eq_A(u, v)`
2. `Σ; Γ, x : A ⊢ P : U` where `U ∈ {Type, Prop}`
3. `Σ; Γ ⊢ t_body : P[x := u]`

Then:
```
Σ; Γ ⊢ rewrite e in t_body : P[x := v]
```

#### Inductive Types

If `Inductive I (x₁ : A₁)...(xₙ : Aₙ) : Type := c₁ : C₁ | ... | cₖ : Cₖ` is in `Σ`:

```
─────────────────────────────────
Σ; Γ ⊢ I : Π(x₁ : A₁)...(xₙ : Aₙ). Type
```

```
─────────────────────────────────
Σ; Γ ⊢ cⱼ : Cⱼ
```

#### Pattern Match

Let `I` be an inductive with constructors `c₁, ..., cₖ`. Given:
- `Σ; Γ ⊢ t₀ : I a⃗`
- `Σ; Γ, z : I a⃗ ⊢ P : Type`
- For each constructor `cⱼ` with type `Π(y₁ : B₁)...(yₘ : Bₘ). I a⃗`:
  - `Σ; Γ, y₁ : B₁, ..., yₘ : Bₘ ⊢ uⱼ : P[z := cⱼ y⃗]`

Then:
```
Σ; Γ ⊢ match t₀ as z return P with ... : P[z := t₀]
```

#### Literal Typing

```
Σ; Γ ⊢ int32(n) : Int32
Σ; Γ ⊢ int64(n) : Int64
Σ; Γ ⊢ float64(f) : Float64
Σ; Γ ⊢ bool(b) : Bool
```

---

## 5. Definitional Equality

The judgment `Σ; Γ ⊢ t ≡ u` defines definitional equality as the least congruence generated by:

### β-rule (Beta Reduction)

```
(λ(x : A). t) u ≡ t[x := u]
```

### δ-rule (Definition Unfolding)

If `def f : A := t ∈ Σ`:
```
f ≡ t
```

### ι-rule (Match Reduction)

```
match cⱼ(v⃗) as z return P with ... | cⱼ(y⃗) ⇒ uⱼ | ... ≡ uⱼ[y⃗ := v⃗]
```

### α-rule (Alpha Equivalence)

Terms differing only by bound variable names are equal.

### Congruence

If parts of a compound term are equal, the compound terms are equal.

### Optional η-rule

Controlled by kernel flag `eta = on | off`:
```
f ≡ λ(x : A). f x    (when x not free in f and f : Π(x : A). B)
```

---

## 6. Evaluation Semantics

Big-step evaluation relation: `t ⇓ v`

### Values

```
v ::= λ(x : A). t           (lambda)
    | c v₁ ... vₘ           (constructor application)
    | Type | Prop           (universes)
    | Π(x : A). B           (Π-types)
    | Eq_A(u, v)            (equality types)
    | int32(n) | ...        (primitive literals)
```

### Evaluation Rules

#### Beta Reduction

```
t₁ ⇓ λ(x : A). t    t₂ ⇓ v₂    t[x := v₂] ⇓ v
──────────────────────────────────────────────
t₁ t₂ ⇓ v
```

#### Match on Constructor

```
t₀ ⇓ cⱼ(v₁, ..., vₘ)    uⱼ[y⃗ := v⃗] ⇓ v
────────────────────────────────────────
match t₀ as z return P with ... ⇓ v
```

#### Definition Unfolding

```
f ≝ t ∈ Σ    t ⇓ v
──────────────────
f ⇓ v
```

#### Rewrite Evaluation

`rewrite` is computationally a no-op (erased at runtime):
```
rewrite e in t_body ⇓ t_body'    (where t_body ⇓ t_body')
```

---

## 7. Termination and Structural Recursion

CertiJSON requires totality for all accepted definitions.

### 7.1 Structural Recursion

For a definition:
```json
{
  "def": {
    "name": "f",
    "type": <type>,
    "body": <body>,
    "rec_args": [i₀, i₁, ...]
  }
}
```

Where `f : Π(a₀ : A₀)...(aₙ : Aₙ). R`:

1. Each index `iₖ` refers to a parameter `a_iₖ` of inductive type
2. Every recursive call `f u₀ ... uₙ` must:
   - Appear inside a `match` that deconstructs a `rec_args` parameter
   - Use arguments `u_iₖ` that are structurally smaller than the original `a_iₖ`

### 7.2 Structural Subterm Relation

- `t` is a structural subterm of itself (for pattern bindings)
- If `a` is of inductive type `I`, and `x` is bound in pattern `c(..., x, ...)`, then `x` is a structural subterm of `c(...)`

### 7.3 Termination Guarantee

> For all `def f : A := t` accepted by the kernel, and for every closed argument of appropriate type, evaluation of `f` terminates.

---

## 8. Representation Layer

### 8.1 Purpose

`repr` declarations describe how logical types are represented in memory for C interop and extraction.

### 8.2 Primitive Repr

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

### 8.3 Struct Repr

```json
{
  "repr": {
    "name": "Point2DRepr",
    "kind": "struct",
    "c_struct_name": "Point2D",
    "size_bytes": 8,
    "align_bytes": 4,
    "fields": [
      { "name": "x", "repr": "Int32Repr", "offset_bytes": 0 },
      { "name": "y", "repr": "Int32Repr", "offset_bytes": 4 }
    ]
  }
}
```

### 8.4 Well-formedness Constraints

- Primitive repr: Valid C type name, size, and signedness
- Struct repr: 
  - Fields do not overlap
  - Offsets within `[0, size_bytes)`
  - Field reprs are well-formed

### 8.5 Encode/Decode Functions

For type `T` with repr `R`:
```
encode_T : T → Bytes(size_bytes(R))
decode_T : Bytes(size_bytes(R)) → Option T
```

With roundtrip theorem:
```
theorem decode_encode_roundtrip :
  ∀(v : T), decode_T(encode_T(v)) = Some v
```

### 8.6 C-Safe Type Predicate

`CType(T)` holds if:
1. `T` is a primitive C-safe type, or
2. `T` is a struct-like type with a repr using only C-safe fields

---

## 9. Foreign Function Interface

### 9.1 extern_c Declaration

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
    "safety": "pure",
    "axioms": []
  }
}
```

### 9.2 Well-formedness

- All repr names must refer to valid representation descriptors
- Logical type must erase to C-level signature
- For `safety = "pure"`: function assumed side-effect free
- For `safety = "impure"`: function returns IO-like type
- Axioms must be well-typed theorems (assumed, not derived)

---

## 10. Erasure

Erasure transforms full core terms to runtime core, removing all proof-only content.

### 10.1 Runtime Core Language

Runtime terms `tr` are a subset:
- Variables: `x`
- Universes: `Type` (not `Prop`)
- Π-types: `Π(x : A). B` where `A, B : Type`
- Lambdas, applications
- Inductive types and constructors (in `Type`)
- Pattern match (where motive returns `Type`)
- Primitive literals

**Excluded:** `Prop`, `Eq`, `refl`, `rewrite`

### 10.2 Erasure Function

`erase : Term → RuntimeTerm` (partial):

| Source | Erased Form |
|--------|-------------|
| `x` | `x` |
| `Type` | `Type` |
| `Prop` | undefined |
| `Π(x : A). B : Type` | `Π(x : erase(A)). erase(B)` |
| `λ(x : A). t` | `λ(x : erase(A)). erase(t)` |
| `t u` | `erase(t) erase(u)` |
| `Eq_A(u, v)` | undefined |
| `refl_A(u)` | undefined |
| `rewrite e in t` | `erase(t)` |
| `cst` (runtime) | `cst` |
| `cst` (proof-only) | undefined |
| `match t ...` | `match erase(t) ...` |
| `int32(n)`, etc. | `int32(n)`, etc. |

### 10.3 Erasure Properties

For well-typed closed `t : A` with `A : Type` and `role` allowing runtime:
- `erase(t)` is well-typed in runtime core
- `t ⇓ v ⇒ erase(t) ⇓ erase(v)`

---

## 11. Target Language: Cmini

Cmini is a tiny, structured, C-like language used as extraction target.

### 11.1 Types

```
τ ::= int32 | int64 | double | u8 | size    (primitives)
    | struct S                               (structs)
```

### 11.2 Expressions

```
e ::= x                       (variable)
    | n32 | n64 | f64 | b     (literals)
    | e.f                     (field access)
    | e1 + e2 | ...           (binary operations)
    | f(e1, ..., en)          (function call)
```

### 11.3 Statements

```
s ::= skip
    | s1; s2                  (sequence)
    | τ x = e;                (local declaration)
    | x = e;                  (assignment)
    | return e;               (return)
    | if (e) { s1 } else { s2 }
    | while (e) { s }         (optional)
```

### 11.4 Functions and Programs

```
func f(τ1 x1, ..., τn xn) : τret { s }

Program ::= StructDecl* ExternDecl* FuncDecl*
```

### 11.5 Semantics

Small-step operational semantics with:
- Configuration: `⟨P, F, s, σ, ρ⟩`
- No undefined behavior by construction
- Deterministic evaluation

---

## 12. Extraction

### 12.1 Type Translation

```
T⟦Int32⟧   = int32
T⟦Int64⟧   = int64
T⟦Float64⟧ = double
T⟦Bool⟧    = u8
T⟦Size⟧    = size
T⟦struct T with repr R⟧ = struct <c_struct_name of R>
```

### 12.2 Term Extraction

For runtime function `f : Π(a₁ : A₁)...(aₙ : Aₙ). R`:

```c
func f(T⟦A₁⟧ a₁, ..., T⟦Aₙ⟧ aₙ) : T⟦R⟧ {
  <compiled body>
}
```

### 12.3 Value Correspondence

`V⟦T⟧(v, v_c)` means CertiJSON value `v` of type `T` corresponds to Cmini value `v_c` of type `T⟦T⟧`.

Defined via repr/encode/decode.

### 12.4 Extraction Correctness Theorem

For closed `t : T` with `CType(T)`:
```
t ⇓ v ⇒ E(t) ⇓ v_c ∧ V⟦T⟧(v, v_c)
```

---

## 13. Effects and IO

CertiJSON provides deterministic, total IO via world-passing semantics.

### 13.1 World Type

```
Inductive World : Type := world_token
```

- Abstract, opaque type
- Cannot be pattern-matched or inspected
- Enforces effect sequencing

### 13.2 IO Monad

```
IO A := World → Pair A World
```

### 13.3 Monad Operations

```
return : ∀(A : Type), A → IO A
return A a = λw. pair a w

bind : ∀(A B : Type), IO A → (A → IO B) → IO B
bind A B io f = λw. let (a, w') = io w in (f a) w'
```

### 13.4 IO Totality

IO definitions cannot introduce non-termination:
- Cannot recursively call on world elements
- IO recursion mediated through bounded iteration or external primitives

### 13.5 extern_io Declaration

```json
{
  "extern_io": {
    "name": "print_line",
    "c_name": "cj_print_line",
    "header": "<certijson_io.h>",
    "args": [{ "name": "input", "repr": "StringRepr" }],
    "result": null,
    "spec": {
      "pre": "...",
      "post": "..."
    }
  }
}
```

### 13.6 IO Standard Operations

```
print : String → IO Unit
println : String → IO Unit
read_line : IO String          (deterministic from script)
random_u64 : IO Nat64          (deterministic PRNG)
```

### 13.7 Runtime Semantics

```
Eval : RuntimeTerm × World → RuntimeValue × World
```

---

## 14. Mutable Arrays

### 14.1 Array Types

```
Array A : Type              -- reference type (non-linear, copyable)
ArrayHandle A : Type        -- linear capability for mutable access
```

### 14.2 Linear Discipline

`ArrayHandle` values are **linear**:
- Cannot be duplicated or discarded silently
- Must be consumed exactly once
- Can only appear in IO functions or bind

### 14.3 Array Operations

```
array_new : ∀(A : Type), Nat → IO (Array A × ArrayHandle A)
array_length : ∀(A), Array A → IO Nat
array_get : ∀(A), ArrayHandle A → Nat → IO (A × ArrayHandle A)
array_set : ∀(A), ArrayHandle A → Nat → A → IO (ArrayHandle A)
array_drop_handle : ∀(A), ArrayHandle A → IO Unit
```

### 14.4 World Segmentation

World contains:
```
World = {
  io_state   : IOState,
  file_state : FileState,
  heap_state : HeapState     -- array segments with unique IDs
}
```

### 14.5 Memory Safety Guarantees

- No out-of-bounds access
- No aliasing
- No double free
- No data races

---

## 15. Concurrency

### 15.1 Thread Handles

```
Thread A : Type     -- linear capability for concurrent computation
```

Linear: cannot be duplicated, must be joined exactly once.

### 15.2 Primitives

```
spawn : ∀(A : Type), IO A → IO (Thread A)
join : ∀(A : Type), Thread A → IO A
par : ∀(A B : Type), IO A → IO B → IO (Pair A B)
```

### 15.3 Deterministic Concurrency Model

- Concurrency is **logical parallelism**
- Sequential world-passing semantics remains canonical
- Implementation may execute in parallel but must preserve sequential semantics

### 15.4 World Partitioning

`spawn` partitions world:
1. `w₀` → `(w_parent, w_child)`
2. Child computation runs on `w_child`
3. `join` merges `w_child'` back into parent

**Key constraint:** No shared mutable segments between threads.

### 15.5 Linear Resource Passing

Resources used by spawned computation must:
- Be created inside the spawned block, or
- Be passed linearly and not used by parent afterward

### 15.6 par Semantics

```
par A B ioA ioB =
  bind (spawn A ioA) (λtA.
  bind (spawn B ioB) (λtB.
  bind (join A tA) (λa.
  bind (join B tB) (λb.
    return (pair A B a b)))))
```

### 15.7 Concurrency Guarantees

- Determinism: Concurrent evaluation has unique observable result
- Race freedom: No shared mutable state across threads
- Totality: All concurrent programs terminate

---

## 16. Compilation Pipeline

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        CertiJSON Compilation Pipeline                   │
└─────────────────────────────────────────────────────────────────────────┘

    ┌──────────┐      ┌──────────┐      ┌──────────┐      ┌──────────┐
    │   JSON   │      │   Raw    │      │Elaborated│      │ Checked  │
    │   File   │─────▶│   AST    │─────▶│   Core   │─────▶│    Σ     │
    └──────────┘      └──────────┘      └──────────┘      └──────────┘
                Phase 1           Phase 2           Phase 3
                Parse             Elaborate         Type Check
                                                    & Verify

    ┌──────────┐      ┌──────────┐      ┌──────────┐
    │ Runtime  │      │  Cmini   │      │    C     │
    │   Core   │─────▶│ Program  │─────▶│  Source  │
    └──────────┘      └──────────┘      └──────────┘
                Phase 4           Phase 5           Phase 6
                Erase             Extract           Lower
                Proofs            to Cmini          to C
```

### Phase 1: JSON Parsing & Structural Validation

**Input:** JSON file  
**Output:** Raw AST

**Checks:**
- Required fields present
- Valid node kinds
- Valid identifiers
- Valid role/coverage_hint values

### Phase 2: Elaboration to Core

**Input:** Raw AST  
**Output:** Elaborated Core AST

**Operations:**
- Bound variable resolution (α-normalization)
- Implicit motive inference
- Sugar expansion

### Phase 3: Declarative Typing & Well-formedness

**Input:** Elaborated Core AST  
**Output:** Checked signature Σ

**Checks:**
- Import resolution
- Inductive well-formedness (positivity, universes)
- Definition typing and termination
- Theorem proof checking
- Pattern exhaustiveness and non-overlap
- repr/extern_c well-formedness

### Phase 4: Erasure to Runtime Core

**Input:** Checked signature Σ  
**Output:** Runtime Core Program

**Operations:**
- Remove Prop terms
- Remove proof-only definitions
- Remove rewrite constructs

### Phase 5: Extraction to Cmini

**Input:** Runtime Core + repr/extern_c metadata  
**Output:** Cmini Program

**Operations:**
- Type translation
- Struct generation
- Function compilation

### Phase 6: Lowering to C

**Input:** Cmini Program  
**Output:** C source code

**Operations:**
- Direct mapping to safe C subset

---

## 17. Trusted Computing Base

### 17.1 Components in TCB

1. **Kernel type checker**
   - Typing rules
   - Definitional equality
   - Positivity checks
   - Termination checker
   - Pattern coverage checker

2. **Erasure implementation**
   - Correct removal of proofs

3. **Extraction to Cmini**
   - Type translation
   - Pattern match compilation

4. **repr/encode/decode correctness**
   - ABI correctness proofs

5. **Cmini semantics and lowering**
   - Behavioral preservation

### 17.2 Untrusted Components

These may be buggy without compromising soundness:
- LLM-based code generators
- IDE tooling
- Formatters
- Suggestion engines
- Higher-level DSL frontends

---

## 18. Agent Profile

Guidelines for LLM agents generating CertiJSON:

### 18.1 Well-Scoped Code

- No free variables
- All references in same module or imports
- No problematic shadowing

**❌ Wrong:**
```json
{ "app": [{ "var": "undefined_func" }, { "var": "x" }] }
```

**✅ Correct:**
```json
// Either import the module containing the function, or define it
```

### 18.2 First-Order Runtime Functions

- Runtime functions first-order at FFI/extraction boundary
- Higher-order allowed in proofs and internal logic

### 18.3 Structured Recursion

- Always specify `rec_args` for recursive functions
- Use one primary structural argument

**❌ Wrong:**
```json
{ "def": { "name": "length", "type": ..., "body": ... } }
```

**✅ Correct:**
```json
{ "def": { "name": "length", "type": ..., "body": ..., "rec_args": [1] } }
```

### 18.4 Exhaustive Patterns

- Always provide exhaustive, non-overlapping matches
- Use `"coverage_hint": "complete"`

**❌ Wrong (missing case):**
```json
{ "match": { "scrutinee": ..., "cases": [
    { "pattern": { "ctor": "zero" }, "body": ... }
    // Missing: succ case!
]}}
```

**✅ Correct:**
```json
{ "match": { "scrutinee": ..., "cases": [
    { "pattern": { "ctor": "zero", "args": [] }, "body": ... },
    { "pattern": { "ctor": "succ", "args": [{"name": "n"}] }, "body": ... }
], "coverage_hint": "complete" }}
```

### 18.5 Role Separation

- Mark theorems as `"role": "proof-only"`
- Keep runtime code separate from proofs

### 18.6 C-Boundary Discipline

- Only use extern_c with concrete C-safe types
- No List or Nat over FFI without repr

### 18.7 IO Discipline

- Thread worlds through IO
- Never inspect World
- No higher-order handles

### 18.8 Concurrency Discipline

- Use structured concurrency (par, spawn+join)
- No unstructured fire-and-forget
- Linear handle discipline
- No cross-thread sharing of linear resources

### 18.9 Standard Library Usage

- Prefer stdlib functions
- Use stdlib equality lemmas

### 18.10 Common Mistakes Checklist

Before submitting code, verify:

| Check | Question |
|-------|----------|
| ☐ Scope | Are all variables bound (in λ, pattern, or imports)? |
| ☐ Types | Does every term have the expected type? |
| ☐ Recursion | Is `rec_args` specified for recursive functions? |
| ☐ Coverage | Does every match cover ALL constructors? |
| ☐ Linearity | Are linear resources (ArrayHandle, Thread) used exactly once? |
| ☐ Roles | Are proofs marked `proof-only`, runtime code `runtime`? |
| ☐ FFI | Do extern_c types have repr declarations? |


---

## 19. Standard Library

The minimal standard library includes:

### 19.1 Std.Bool

```
Inductive Bool : Type := true | false

def if_then_else : ∀(A : Type), Bool → A → A → A
```

### 19.2 Std.Eq

```
theorem eq_sym : ∀(A : Type)(x y : A), Eq_A(x, y) → Eq_A(y, x)
theorem eq_trans : ∀(A : Type)(x y z : A), Eq_A(x, y) → Eq_A(y, z) → Eq_A(x, z)
theorem eq_congr1 : ∀(A B : Type)(f : A → B)(x y : A), Eq_A(x, y) → Eq_B(f x, f y)
```

### 19.3 Std.Nat

```
Inductive Nat : Type := zero | succ : Nat → Nat

def nat_rec : ∀(A : Type), A → (Nat → A → A) → Nat → A
def plus : Nat → Nat → Nat
def mult : Nat → Nat → Nat

Inductive le (n : Nat) : Nat → Prop := le_refl | le_succ

theorem plus_zero_right : ∀(n : Nat), Eq_Nat(plus n zero, n)
theorem plus_zero_left : ∀(n : Nat), Eq_Nat(plus zero n, n)
```

### 19.4 Std.List

```
Inductive List (A : Type) : Type := nil | cons : A → List A → List A

def length : ∀(A : Type), List A → Nat
def append : ∀(A : Type), List A → List A → List A
def map : ∀(A B : Type), (A → B) → List A → List B
def fold_right : ∀(A B : Type), (A → B → B) → B → List A → B
```

### 19.5 Std.Option

```
Inductive Option (A : Type) : Type := none | some : A → Option A

def option_map : ∀(A B : Type), (A → B) → Option A → Option B
def option_default : ∀(A : Type), A → Option A → A
```

### 19.6 Std.Pair

```
Inductive Pair (A B : Type) : Type := pair : A → B → Pair A B

def fst : ∀(A B : Type), Pair A B → A
def snd : ∀(A B : Type), Pair A B → B
```

### 19.7 Std.Result

```
Inductive Result (E A : Type) : Type := ok : A → Result E A | error : E → Result E A

def result_map : ∀(E A B : Type), (A → B) → Result E A → Result E B
def result_bind : ∀(E A B : Type), Result E A → (A → Result E B) → Result E B
```

---

## 20. Meta-Theoretic Goals

### 20.1 Type Soundness

If `Σ; · ⊢ t : A` and `t` is closed, then either `t` is a value or there exists `t'` such that `t → t'`, and if `t → t'` then `Σ; · ⊢ t' : A`.

### 20.2 Strong Normalization

For all closed, well-typed terms `t`, there exists a value `v` such that `t ⇓ v`.

### 20.3 Logical Soundness

If a theorem `p : P := t` is accepted in well-formed `Σ`, then `P` holds in the standard model.

### 20.4 Representation Soundness

Given well-formed repr and correct encode/decode proofs, runtime C representation is consistent with core logical semantics.

### 20.5 FFI ABI Safety

Given well-formed repr and extern_c, C calls respect the ABI described by repr.

### 20.6 Extraction Correctness

Extracted C code is observationally equivalent to CertiJSON evaluation for runtime terms, modulo assumed extern_c axioms.

### 20.7 Determinism

For any closed `main : IO A` and initial world `w₀`, the evaluation result `(a, w₁)` is unique, even with spawn, join, par.

### 20.8 Race Freedom

No data races: no shared mutable state across threads.

---

## 21. Correctness Levels and Verification Modes

CertiJSON supports **configurable correctness levels**, analogous to optimization levels in conventional compilers. These levels allow users and LLM agents to trade compile time against the *amount and depth of verification work performed*.

Crucially:

* **Logical soundness and core safety are never compromised** by correctness levels.
* Lower levels may:

  * Skip expensive *optional* analyses,
  * Use cheaper equality/normalization strategies,
  * Accept fewer proofs or provide weaker diagnostics.
* Higher levels:

  * Perform deeper normalization and proof checking,
  * Enforce stricter obligations,
  * Run additional static analyses (e.g. repr/FFI consistency).

Correctness levels thus control **how hard the kernel works**, not whether it is sound.

The compiler exposes this as a flag:

```text
--correctness-level=C0 | C1 | C2 | C3 | C4 | C5
```

Unless stated otherwise, the **default level is `C1`**.

### 21.1 Invariants Across All Levels

The following checks and properties are **always enforced at all levels** (`C0`–`C5`):

* Core typing rules (§4)
* Definitional equality as specified in §5 (at least β + δ + ι; depth may vary by level, but never in a way that makes an ill-typed term appear well-typed)
* Structural recursion and termination checks (§7)
* Positivity and well-formedness of inductives
* Linearity discipline for:

  * `ArrayHandle A` (§14),
  * `Thread A` (§15),
* World discipline for IO and concurrency (§13–§15)
* Basic repr well-formedness and FFI type sanity (§8–§9)
* Erasure correctness (§10) and extraction shape invariants (§11–§12)

These invariants ensure that:

> Any module accepted at any correctness level is well-typed, total, and free of undefined behavior **within the CertiJSON semantics**.
> Differences between levels are about *completeness of proofs, strength of guarantees about externals, and depth of analysis*, not about relaxing soundness.

### 21.2 Levels Overview

At a high level:

| Level | Goal                                               | Typical Use                          |
| ----- | -------------------------------------------------- | ------------------------------------ |
| `C0`  | Fastest feedback, minimal extra analysis           | Rapid prototyping, LLM iteration     |
| `C1`  | Baseline safe mode (default)                       | Normal development                   |
| `C2`  | Deeper normalization and definitional equality     | Debugging subtle type/proof issues   |
| `C3`  | Full proof obligation closure and invariants       | Verifying core libraries/components  |
| `C4`  | Global consistency and strong invariants           | System-level verification            |
| `C5`  | Maximum verification (research / heavy proof mode) | Deep formalization, critical kernels |

Raising the level never makes previously accepted programs *unsound*; it may:

* Reject programs that relied on incomplete or shallow reasoning at lower levels.
* Produce more precise error messages for FFI / repr / concurrency mistakes.
* Take substantially more time and memory.

### 21.3 Level C0 — Prototype Mode

**Intent:** Fastest possible feedback for LLMs and human developers while retaining core soundness.

**Characteristics:**

* Full core typing, linearity, world/IO discipline, termination: **enabled** (non-negotiable).
* Definitional equality:

  * Guaranteed β-reduction, basic δ (unfolding of non-recursive definitions), and ι (match on constructors).
  * Normalization is **shallow**: the kernel may stop short of full normalization if equivalence is already decided or obviously fails.
* Pattern coverage and non-overlap:

  * Structural checks run, but the kernel may rely more heavily on `"coverage_hint": "complete"` for diagnostics.
  * Coverage analysis may be less aggressive in suggesting missing cases.
* repr/extern checks:

  * Basic shape and ABI compatibility: **enabled**.
  * Expensive cross-module repr consistency checks: **may be skipped**.
* Additional global analyses: **disabled**.

**Use cases:**

* Rapid LLM-driven exploration.
* Quick compile–run cycles to test extracted C.
* "Turn it on, see if it even type-checks."

### 21.4 Level C1 — Baseline Safe Mode (Default)

**Intent:** Default mode balancing safety and performance.

Compared to `C0`:

* Definitional equality:

  * Full β + δ + ι as specified in §5, with a conservative normalization fuel budget sufficient for typical code.
* Pattern coverage:

  * Exhaustiveness and non-overlap checks run for all inductives.
  * `"coverage_hint": "complete"` is treated as a hint only; the kernel verifies coverage.
* repr/extern:

  * All local repr and extern_c declarations must satisfy well-formedness constraints (§8–§9).
  * Basic ABI and type erasure sanity is enforced.

**Not guaranteed at `C1`:**

* Closing all proof obligations about complex global invariants.
* Checking deep normalization of very large or proof-heavy terms if they exceed resource budgets (resulting in rejection rather than unsound acceptance).

This level is suitable for:

* Everyday development,
* LLM agents generating "normal" code with light to moderate proofs,
* Projects where compile time should remain practical.

### 21.5 Level C2 — Deep Normalization

**Intent:** Debug subtle type/equality/proof issues by enabling deeper definitional equality and normalization.

Compared to `C1`:

* Definitional equality:

  * Requires **full βδι normalization to weak-head normal form** for all typing and conversion checks.
  * Larger fuel budget for normalization; the kernel attempts to resolve all reasonable equality constraints.
* Rewriting and equality-heavy definitions:

  * Complex chains of rewrites and equalities are evaluated more thoroughly.
* Termination and recursion:

  * Same structural criteria as lower levels, but additional sanity checks and diagnostics are enabled to help pinpoint structural recursion mistakes.

**Use cases:**

* When a module fails in `C1` due to subtle type mismatches or unprovable equalities.
* When FFI or repr-level issues manifest as confusing type errors.
* As an intermediate step before enabling heavy invariant checking at higher levels.

### 21.6 Level C3 — Full Proof Closure and Invariants

**Intent:** Ensure that all declared proofs and core invariants are fully discharged.

At `C3`, in addition to `C2` behavior:

* All theorems and lemmas:

  * Must be **fully checked**, including large proof terms.
  * No "admitted" or "stub" proofs (unless explicitly marked and rejected for extraction).
* Global invariants:

  * Inductive invariants (e.g. for arrays, state machines, protocols) declared in the library must be validated.
* IO and world:

  * Additional static checks ensure that IO/world threading does not accidentally violate documented invariants (e.g. no "world leaks" outside intended scope).

**Use cases:**

* Verifying standard libraries (Nat/List/Array/Result/etc.).
* Security- or correctness-critical subsystems.
* Situations where an LLM repeatedly generates code that passes low levels but misbehaves semantically, and you want stronger assurances.

### 21.7 Level C4 — Global Consistency and Strong Invariants

**Intent:** Strengthen guarantees about the *overall theory and system*, not just individual modules.

Building on `C3`:

* Logical consistency checks:

  * Additional verification of universe levels and inductive definitions to guard against subtle inconsistencies.
  * More conservative treatment of axioms: extern_c axioms and unsafe assumptions are scrutinized more aggressively.
* World and concurrency invariants:

  * Stronger checks that world partitions for concurrency (§15) are non-overlapping and that merging maintains global invariants.
  * Enforcement of more stringent discipline on linear resources across module boundaries.
* Cross-module repr/FFI analysis:

  * Whole-program or whole-library passes that analyze repr usage, encode/decode roundtrips, and extern calls for consistency.

**Use cases:**

* System-level verification of libraries and executables.
* Long-term assurance of correctness in critical deployments.
* Debugging subtle bugs in the interaction between internal code and FFI.

### 21.8 Level C5 — Maximum Verification Mode

**Intent:** "Full proof assistant weight" for research-grade or critical proofs.

In addition to all prior guarantees:

* Definitional equality and normalization:

  * Proof terms may be fully normalized (up to a configurable bound) to canonical forms where feasible.
* Termination and well-foundedness:

  * Optional additional checks for advanced termination arguments (if the language later extends beyond strictly structural recursion).
* Ghost-state and refinement checking:

  * Future extensions may use `C5` to enable expensive checks about ghost variables, cost models, or refinement types.
* Meta-theoretic checks:

  * Stronger internal consistency checks for the kernel's own invariants (e.g., certain self-checks or reflection-based sanity tests).

**Use cases:**

* Mechanized formalization of important algorithms and data structures.
* Proofs intended to be exported to or cross-validated with external proof assistants (Coq/Agda/Lean).
* Verification of tiny, critical kernels where compile time is negligible compared to assurance needs.

### 21.9 Interaction with LLM Agents

Correctness levels are especially useful in an LLM-driven workflow:

* An agent can:

  * Start at `C0` or `C1` for fast iteration.
  * If extracted C misbehaves or fails external tests, recompile at `C2`–`C3` to obtain more precise diagnostics and stronger proof checking.
  * For core library code, default to `C3`–`C4`.
  * For critical kernels, enforce `C5`.

A typical strategy for an agent:

1. Generate code and compile at `C0`/`C1`.
2. If the kernel rejects the module:

   * Fix the structural/type issues and recompile.
3. If the kernel accepts but external tests fail or C crashes:

   * Re-run at `C2` or `C3` to trigger deeper analysis and more detailed error messages.
4. For components designated as "trusted library":

   * Always compile at `C3` or higher.

This design allows CertiJSON to be:

* **Fast enough** for interactive, LLM-driven development at low levels, and
* **As rigorous as a full proof assistant** for critical components at high levels,
  without compromising the soundness of the core type theory at any level.

---

## Part V: Advanced Verification

### 22. Refinement Types

Refinement types (also known as Subset types) allow restricting a type `A` by a predicate `P : A → Prop`. A value of type `{x : A | P x}` consists of a value `v : A` and a proof that `P v` holds.

#### 22.1 Abstract Syntax

```
t ::= ...
    | {x : A | P}                (subset type)
    | subset_intro(u, p)         (introduction)
    | subset_elim(t)             (elimination - value)
    | subset_proof(t)            (elimination - proof)
```

#### 22.2 JSON Syntax

**Subset Type:**
```json
{
  "subset": {
    "arg": { "name": "x", "type": <type_term> },
    "pred": <prop_term>
  }
}
```

**Introduction:**
```json
{
  "subset_intro": {
    "value": <term>,
    "proof": <proof_term>
  }
}
```

**Elimination (Value):**
```json
{ "subset_elim": <term> }
```
*Note: In runtime code, `subset_elim` is a no-op (erased).*

#### 22.3 Typing Rules

**Formation:**
```
Σ; Γ ⊢ A : Type    Σ; Γ, x : A ⊢ P : Prop
──────────────────────────────────────────
Σ; Γ ⊢ {x : A | P} : Type
```

**Introduction:**
```
Σ; Γ ⊢ u : A    Σ; Γ ⊢ p : P[x := u]
────────────────────────────────────
Σ; Γ ⊢ subset_intro(u, p) : {x : A | P}
```

**Elimination:**
```
Σ; Γ ⊢ t : {x : A | P}
──────────────────────
Σ; Γ ⊢ subset_elim(t) : A
```

#### 22.4 Erasure

Refinement types erase to their underlying type.
- `erase({x : A | P})` = `erase(A)`
- `erase(subset_intro(u, p))` = `erase(u)`
- `erase(subset_elim(t))` = `erase(t)`

---

### 23. Ghost Parameters

Ghost parameters are function arguments used solely for verification. They are marked as `proof-only` and are erased during compilation, incurring no runtime cost.

#### 23.1 Syntax

In `def` or `lambda`, an argument can have a `role`:

```json
{
  "lambda": {
    "arg": {
      "name": "h",
      "type": <type>,
      "role": "proof-only"
    },
    "body": ...
  }
}
```

#### 23.2 Usage

Ghost parameters can be used in:
- Types of subsequent arguments
- Proofs
- Other ghost arguments

They **cannot** be used in:
- Runtime computations (unless inside a `proof-only` block)

#### 23.3 Erasure

- Lambda abstractions with `proof-only` arguments are erased: `λ(x:A). t` → `t` (if x is ghost).
- Applications to ghost arguments are erased: `f x` → `f` (if x is ghost).

---

### 24. Sized Arrays

Sized arrays extend the mutable array primitives with type-level size information, enabling safe, bounds-checked access without runtime overhead (when proofs are static).

#### 24.1 Types

```
Array A n : Type        -- Array of type A with size n (n : Nat)
ArrayHandle A n : Type  -- Linear capability for Array A n
```

#### 24.2 Primitives

```
array_new : ∀(A : Type)(n : Nat), IO (Array A n × ArrayHandle A n)

array_get : ∀(A : Type)(n : Nat),
            ArrayHandle A n →
            ∀(i : Nat),
            (i < n) →           -- Proof that index is in bounds
            IO (A × ArrayHandle A n)

array_set : ∀(A : Type)(n : Nat),
            ArrayHandle A n →
            ∀(i : Nat),
            (i < n) →           -- Proof that index is in bounds
            A →
            IO (ArrayHandle A n)
```

#### 24.3 Doom Use Case

```json
// Framebuffer definition
{ "def": {
    "name": "put_pixel",
    "type": "forall (w h : Nat). ArrayHandle Color (w * h) -> forall (x y : Nat). (x < w) -> (y < h) -> Color -> IO ...",
    ...
}}
```

---

## Appendix A: JSON Examples

### A.1 Natural Numbers Module

```json
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
```

### A.2 List Module

```json
{
  "module": "Std.List",
  "imports": ["Std.Nat"],
  "declarations": [
    {
      "inductive": {
        "name": "List",
        "params": [{ "name": "A", "type": { "universe": "Type" } }],
        "universe": "Type",
        "constructors": [
          { "name": "nil", "args": [] },
          {
            "name": "cons",
            "args": [
              { "name": "x", "type": { "var": "A" } },
              { "name": "xs", "type": { "app": [{ "var": "List" }, { "var": "A" }] } }
            ]
          }
        ]
      }
    },
    {
      "def": {
        "name": "length",
        "role": "runtime",
        "type": {
          "pi": {
            "arg": { "name": "A", "type": { "universe": "Type" } },
            "result": {
              "pi": {
                "arg": { "name": "xs", "type": { "app": [{ "var": "List" }, { "var": "A" }] } },
                "result": { "var": "Nat" }
              }
            }
          }
        },
        "body": {
          "lambda": {
            "arg": { "name": "A", "type": { "universe": "Type" } },
            "body": {
              "lambda": {
                "arg": { "name": "xs", "type": { "app": [{ "var": "List" }, { "var": "A" }] } },
                "body": {
                  "match": {
                    "scrutinee": { "var": "xs" },
                    "motive": { "var": "Nat" },
                    "as": "z",
                    "cases": [
                      {
                        "pattern": { "ctor": "nil", "args": [] },
                        "body": { "var": "zero" }
                      },
                      {
                        "pattern": { "ctor": "cons", "args": [{ "name": "x" }, { "name": "rest" }] },
                        "body": {
                          "app": [
                            { "var": "succ" },
                            { "app": [{ "var": "length" }, { "var": "A" }, { "var": "rest" }] }
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
        "rec_args": [1]
      }
    },
    {
      "theorem": {
        "name": "length_nil",
        "type": {
          "forall": {
            "arg": { "name": "A", "type": { "universe": "Type" } },
            "result": {
              "eq": {
                "type": { "var": "Nat" },
                "lhs": {
                  "app": [
                    { "var": "length" },
                    { "var": "A" },
                    { "app": [{ "var": "nil" }, { "var": "A" }] }
                  ]
                },
                "rhs": { "var": "zero" }
              }
            }
          }
        },
        "proof": {
          "lambda": {
            "arg": { "name": "A", "type": { "universe": "Type" } },
            "body": {
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
```

---

## Appendix B: Version History

| Version | Key Changes |
|---------|-------------|
| 0.1 | Initial design goals and JSON syntax |
| 0.2 | Abstract syntax, typing rules |
| 0.3 | Prop/Type distinction, definition roles |
| 0.4 | Explicit rewrite, structural recursion, primitives |
| 0.5 | Erasure function, Cmini target, extraction |
| 0.6 | Pattern safety, name resolution, JSON schema |
| 0.7 | Compilation pipeline, TCB, profiles, stdlib |
| 0.8 | Deterministic effects, world-passing IO |
| 0.9 | Mutable arrays, linear handles |
| 1.0-alpha | Deterministic concurrency, structured parallelism |

---

## Appendix C: Future Directions

- **1.0-beta**: Standard concurrent library (parMap, parScan, parFold)
- **1.1**: Thread cancellation, algebraic effects
- **2.0**: Distributed systems, verified communication protocols
- Mechanized proofs in Coq/Agda
- JSON Schema for machine-checkable syntax validation

---

## Appendix D: Common Errors

This section documents typical error messages LLM agents encounter, with causes and fixes.

### D.1 Type Errors

| Error | Cause | Fix |
|-------|-------|-----|
| `Expected Type, got Prop` | Using a proposition where a computational type is needed | Use a type in `Type` universe, not `Prop` |
| `Type mismatch: expected A, got B` | Argument type doesn't match parameter | Check function signature, ensure argument has correct type |
| `Cannot apply non-function` | Applying something that isn't a function type | Verify `app` is applied to a Π-type |
| `Unbound variable: x` | Variable not in scope | Import the module, add parameter, or fix typo |

### D.2 Termination Errors

| Error | Cause | Fix |
|-------|-------|-----|
| `Recursive call not on smaller argument` | Recursive argument isn't structurally smaller | Ensure recursion is on pattern-bound subterms |
| `Missing rec_args for recursive function` | Recursive function without `rec_args` | Add `"rec_args": [i]` specifying the decreasing argument index |
| `rec_args index out of bounds` | Index exceeds number of arguments | Use 0-based index within argument count |

### D.3 Pattern Errors

| Error | Cause | Fix |
|-------|-------|-----|
| `Non-exhaustive pattern match` | Missing constructor cases | Add cases for ALL constructors |
| `Overlapping patterns` | Multiple cases match same constructor | Remove duplicate cases |
| `Unknown constructor: C` | Constructor doesn't exist | Check inductive definition spelling |

### D.4 Representation Errors

| Error | Cause | Fix |
|-------|-------|-----|
| `No repr for type T` | Using type at C boundary without repr | Add repr declaration for the type |
| `Field overlap in struct repr` | Field offsets overlap | Fix offset_bytes values |
| `Repr size mismatch` | Declared size doesn't match field layout | Verify size_bytes >= max(offset + field_size) |

### D.5 Linear Type Errors

| Error | Cause | Fix |
|-------|-------|-----|
| `Linear resource used twice` | ArrayHandle or Thread used multiple times | Restructure to use resource exactly once |
| `Linear resource dropped` | ArrayHandle not consumed | Call array_drop_handle or return the handle |
| `Thread not joined` | Thread handle discarded | Always join threads |

---

## Appendix E: Glossary

| Term | Definition |
|------|------------|
| **α-equivalence** | Two terms are α-equivalent if they differ only in the names of bound variables |
| **β-reduction** | Computational reduction: `(λx.t) u → t[x:=u]` |
| **Cmini** | Safe C subset used as compilation target |
| **Curry-Howard** | Correspondence between types and propositions, terms and proofs |
| **δ-reduction** | Unfolding a defined constant to its body |
| **Dependent type** | Type that can depend on values (e.g., `Vec A n` where `n : Nat`) |
| **Definitional equality** | Equality checked by the type checker (β, δ, ι, α rules) |
| **Elaboration** | Phase converting surface syntax to core type theory |
| **Erasure** | Removal of proof-only terms before code generation |
| **Extraction** | Translation from CertiJSON core to C code |
| **FFI** | Foreign Function Interface - mechanism for calling C functions |
| **IO Monad** | Type `IO A = World → (A, World)` modeling sequential effects |
| **ι-reduction** | Pattern match reduction when scrutinee is a constructor |
| **Kernel** | Trusted type checker that validates proofs |
| **Linear type** | Type whose values must be used exactly once |
| **Motive** | Return type of a pattern match, may depend on scrutinee |
| **Π-type** | Dependent function type: `Π(x:A).B` where `B` may mention `x` |
| **Positivity** | Restriction ensuring inductive types are well-founded |
| **Prop** | Universe of propositions (erased at runtime) |
| **Repr** | Representation descriptor specifying C memory layout |
| **Runtime core** | Subset of core language after erasure |
| **Scrutinee** | Term being matched in a pattern match expression |
| **Signature** | Collection of all global declarations (Σ) |
| **Structural recursion** | Recursion where arguments decrease structurally |
| **TCB** | Trusted Computing Base - components that must be correct for soundness |
| **Totality** | Property that all computations terminate |
| **Type** | Universe of computational types (preserved at runtime) |
| **Well-founded** | Order with no infinite descending chains (ensures termination) |
| **World** | Abstract token representing IO state; threaded through computations |

---

## Document End

*This specification is designed to be consumed by both humans and LLM agents. For implementation details, see the reference compiler source code.*
