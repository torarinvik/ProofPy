(** CertiJSON - A proof-based programming language for agentic LLMs

    This is the main library module that re-exports all public interfaces. *)

(** {1 Syntax} *)

module Syntax = Syntax
module Json_parser = Json_parser
module Loc = Loc

(** {1 Type System} *)

module Context = Context
module Typing = Typing
module Loader = Loader

(** {1 Evaluation} *)

module Eval = Eval

(** {1 Extraction} *)

module Extraction = Extraction

(** {1 Utilities} *)

module Error = Error
module Pretty = Pretty
