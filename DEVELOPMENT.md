# CertiJSON Development

## Prerequisites

- OCaml 5.0+ 
- opam 2.0+
- dune 3.0+

## Setup

```bash
# Create a local opam switch (recommended)
opam switch create . 5.3.0 --deps-only

# Or install dependencies in your current switch
opam install . --deps-only --with-test --with-doc
```

## Building

```bash
# Build the project
dune build

# Build and watch for changes
dune build -w
```

## Testing

```bash
# Run all tests
dune runtest

# Run tests with verbose output
dune runtest --force --verbose
```

## Running

```bash
# Check a CertiJSON file
dune exec certijson -- check examples/nat.json

# Parse and pretty-print
dune exec certijson -- parse examples/nat.json

# Evaluate a definition
dune exec certijson -- eval examples/nat.json plus
```

## Documentation

```bash
# Generate documentation
dune build @doc

# Open documentation
open _build/default/_doc/_html/index.html
```

## Project Structure

```
CertiJSON/
├── lib/                    # Core library
│   ├── syntax.ml          # Abstract syntax
│   ├── json_parser.ml     # JSON → AST parser
│   ├── context.ml         # Typing contexts
│   ├── typing.ml          # Type checker
│   ├── eval.ml            # Evaluator
│   ├── pretty.ml          # Pretty printing
│   └── error.ml           # Error handling
├── bin/                   # CLI executable
│   └── main.ml
├── test/                  # Tests
│   ├── test_parser.ml
│   └── test_typing.ml
├── formal_specs.md        # Language specification
└── README.md
```

## Dependencies

| Package | Purpose |
|---------|---------|
| yojson | JSON parsing |
| ppx_deriving | Derive show, eq |
| ppx_deriving_yojson | JSON serialization |
| cmdliner | CLI argument parsing |
| fmt | Formatting |
| logs | Logging |
| alcotest | Testing |
