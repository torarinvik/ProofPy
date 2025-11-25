(lang dune 3.0)

(name certijson)

(version 0.1.0)

(generate_opam_files true)

(source
 (github yourusername/certijson))

(authors "Your Name")

(maintainers "Your Name")

(license MIT)

(documentation https://github.com/yourusername/certijson)

(package
 (name certijson)
 (synopsis "A proof-based programming language for agentic LLMs")
 (description
  "CertiJSON is a pure, total, dependently typed programming language designed exclusively for use by AI coding agents. Programs are written in JSON syntax and compile to safe C code.")
 (depends
  (ocaml (>= 5.0))
  (dune (>= 3.0))
  (yojson (>= 2.0))
  (ppx_deriving (>= 5.0))
  (ppx_deriving_yojson (>= 3.0))
  (menhir (>= 20220210))
  (cmdliner (>= 1.1))
  (fmt (>= 0.9))
  (logs (>= 0.7))
  (alcotest (and (>= 1.6) :with-test))
  (odoc :with-doc)))
