# CertiJSON Examples

This directory contains example CertiJSON programs demonstrating various features of the language and the Standard Library.

## Running Examples

You can run the examples using the `dune exec` command:

```bash
dune exec certijson -- run examples/<filename>.json
```

For examples that only demonstrate type checking (like FFI definitions), use `check`:

```bash
dune exec certijson -- check examples/<filename>.json
```

## Building Executables

For examples that require external libraries (like `pong.json` and `tetris.json` which use Raylib), or if you want to compile to a native executable, use the `build.py` script:

```bash
./build.py examples/pong.json --run
```

This script will:
1. Extract the CertiJSON code to C.
2. Compile it with the runtime library.
3. Automatically link against Raylib if detected (requires `pkg-config`).
4. Run the resulting executable (if `--run` is specified).

Options:
- `--run`: Run the executable after building.
- `--output <name>`: Specify the output executable name.
- `--libs <libs>`: Manually specify libraries to link (comma-separated).
- `--debug`: Enable debug symbols.

## List of Examples

### Basic
- `hello.json`: A simple "Hello World" program.
- `hello_std.json`: "Hello World" using the Standard Library.
- `my_bool.json`: Defines a custom Boolean type (renamed to avoid conflict with `Std.Bool`).
- `my_nat.json`: Defines a custom Natural number type (renamed to avoid conflict with `Std.Nat`).
- `my_list.json`: Defines a custom List type (renamed to avoid conflict with `Std.List`).

### Tests
- `test_bool_simple.json`: Tests for Boolean logic.
- `test_nat.json`: Tests for Natural numbers.
- `test_list.json`: Tests for List operations.
- `test_stdlib.json`: General tests for the Standard Library.
- `test_either_list_zip.json`: Tests for `Either` type and `List.zip`.
- `array_test.json`: Tests for array operations.

### Advanced Features
- `refinement_types.json`: Demonstrates refinement types (Subset types).
- `sized_arrays.json`: Demonstrates dependent array types.

### Applications
- `pong.json`: A Pong game using Raylib (requires Raylib bindings).
- `tetris.json`: A Tetris game using Raylib (requires Raylib bindings).

### FFI (Foreign Function Interface)
These examples demonstrate how to define C bindings. They are primarily for type checking.
- `ffi.json`: Basic FFI definitions.
- `ffi_math.json`: Bindings for C math library functions.
- `ffi_struct.json`: Bindings for C structs.
