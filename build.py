#!/usr/bin/env python3
import argparse
import subprocess
import os
import sys
import tempfile
import shutil

def run_command(cmd, cwd=None):
    print(f"Running: {' '.join(cmd)}")
    result = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    if result.returncode != 0:
        print(f"Error running command: {' '.join(cmd)}")
        print("STDOUT:", result.stdout)
        print("STDERR:", result.stderr)
        sys.exit(1)
    return result.stdout

def main():
    parser = argparse.ArgumentParser(description="Build CertiJSON programs")
    parser.add_argument("file", help="The CertiJSON file to build")
    parser.add_argument("-o", "--output", help="Output executable name")
    parser.add_argument("--run", action="store_true", help="Run the executable after building")
    parser.add_argument("--libs", help="Comma-separated list of libraries to link (e.g. raylib,m)")
    parser.add_argument("--cc", default="cc", help="C compiler to use (default: cc)")
    parser.add_argument("--cflags", default="-O2 -Wall", help="C compiler flags")
    parser.add_argument("--debug", action="store_true", help="Enable debug info")
    
    args = parser.parse_args()

    if not os.path.exists(args.file):
        print(f"Error: File '{args.file}' not found.")
        sys.exit(1)

    # Determine output name
    if args.output:
        output_exe = args.output
    else:
        base_name = os.path.splitext(os.path.basename(args.file))[0]
        output_exe = os.path.abspath(base_name)

    # Create a temporary directory for build artifacts
    with tempfile.TemporaryDirectory() as temp_dir:
        c_file = os.path.join(temp_dir, "main.c")
        
        # 1. Extract CertiJSON to C
        print(f"Extracting {args.file} to C...")
        # We use dune exec to run the extractor
        # Note: We need to run this from the project root
        project_root = os.getcwd()
        extract_cmd = ["dune", "exec", "certijson", "--", "extract", os.path.abspath(args.file)]
        
        c_code = run_command(extract_cmd, cwd=project_root)
        
        with open(c_file, "w") as f:
            f.write(c_code)
            
        # 2. Compile
        print("Compiling...")
        runtime_dir = os.path.join(project_root, "runtime")
        runtime_files = [
            os.path.join(runtime_dir, f) 
            for f in os.listdir(runtime_dir) 
            if f.endswith(".c")
        ]
        
        compile_cmd = [args.cc]
        if args.debug:
            compile_cmd.append("-g")
        else:
            compile_cmd.extend(args.cflags.split())
            
        compile_cmd.append(f"-I{runtime_dir}")
        compile_cmd.append(c_file)
        compile_cmd.extend(runtime_files)
        compile_cmd.append("-o")
        compile_cmd.append(output_exe)
        
        # Add libraries
        # Always link math library
        libs = ["m"]
        if args.libs:
            libs.extend(args.libs.split(","))
            
        # Auto-detect raylib if "Raylib" is in the source file content (heuristic)
        with open(args.file, "r") as f:
            content = f.read()
            if "Raylib" in content:
                if "raylib" not in libs:
                    libs.append("raylib")

        pkg_config_libs = []
        manual_libs = []

        for lib in libs:
            if lib == "m":
                manual_libs.append(lib)
                continue
                
            # Try pkg-config
            try:
                subprocess.run(["pkg-config", "--exists", lib], check=True, capture_output=True)
                pkg_config_libs.append(lib)
            except (subprocess.CalledProcessError, FileNotFoundError):
                manual_libs.append(lib)

        # Get flags from pkg-config
        if pkg_config_libs:
            try:
                flags = run_command(["pkg-config", "--cflags", "--libs"] + pkg_config_libs).strip()
                if flags:
                    compile_cmd.extend(flags.split())
            except Exception as e:
                print(f"Warning: pkg-config failed: {e}")
                # Fallback to manual linking
                manual_libs.extend(pkg_config_libs)

        for lib in manual_libs:
            compile_cmd.append(f"-l{lib}")
            
        run_command(compile_cmd)
        
        print(f"Build successful: {output_exe}")
        
        # 3. Run if requested
        if args.run:
            print(f"Running {output_exe}...")
            subprocess.run([output_exe])

if __name__ == "__main__":
    main()
