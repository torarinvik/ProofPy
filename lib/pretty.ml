(** Pretty printing for CertiJSON terms. *)

open Syntax

(** {1 Pretty Printers} *)

let pp_name fmt name = Format.fprintf fmt "%s" name

let pp_universe fmt = function
  | Type -> Format.fprintf fmt "Type"
  | Prop -> Format.fprintf fmt "Prop"

let pp_prim_type fmt = function
  | Int32 -> Format.fprintf fmt "Int32"
  | Int64 -> Format.fprintf fmt "Int64"
  | Float64 -> Format.fprintf fmt "Float64"
  | Bool -> Format.fprintf fmt "Bool"
  | Size -> Format.fprintf fmt "Size"

let pp_literal fmt = function
  | LitInt32 n -> Format.fprintf fmt "%ld" n
  | LitInt64 n -> Format.fprintf fmt "%Ld" n
  | LitFloat64 f -> Format.fprintf fmt "%f" f
  | LitBool b -> Format.fprintf fmt "%b" b

let rec pp_term fmt = function
  | Var x -> Format.fprintf fmt "%s" x
  | Universe u -> pp_universe fmt u
  | PrimType p -> pp_prim_type fmt p
  | Literal l -> pp_literal fmt l
  | Global name -> Format.fprintf fmt "%s" name
  | Pi { arg; result } ->
      if String.equal arg.name "_" then
        Format.fprintf fmt "(%a → %a)" pp_term arg.ty pp_term result
      else
        Format.fprintf fmt "(Π(%s : %a). %a)" arg.name pp_term arg.ty pp_term result
  | Lambda { arg; body } ->
      Format.fprintf fmt "(λ(%s : %a). %a)" arg.name pp_term arg.ty pp_term body
  | App (f, args) ->
      Format.fprintf fmt "(%a %a)"
        pp_term f
        (Format.pp_print_list ~pp_sep:Format.pp_print_space pp_term) args
  | Eq { ty; lhs; rhs } ->
      Format.fprintf fmt "Eq_%a(%a, %a)" pp_term ty pp_term lhs pp_term rhs
  | Refl { ty; value } ->
      Format.fprintf fmt "refl_%a(%a)" pp_term ty pp_term value
  | Rewrite { proof; body } ->
      Format.fprintf fmt "(rewrite %a in %a)" pp_term proof pp_term body
  | Match { scrutinee; motive; cases; _ } ->
      Format.fprintf fmt "@[<v 2>(match %a return %a with@,%a)@]"
        pp_term scrutinee
        pp_term motive
        (Format.pp_print_list ~pp_sep:Format.pp_print_cut pp_case) cases

and pp_case fmt { pattern; body } =
  Format.fprintf fmt "| %s(%a) => %a"
    pattern.ctor
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ") pp_pattern_arg)
    pattern.args
    pp_term body

and pp_pattern_arg fmt { arg_name } =
  Format.fprintf fmt "%s" arg_name

let term_to_string t =
  Format.asprintf "%a" pp_term t

(** {1 Declaration Printers} *)

let pp_binder fmt { name; ty } =
  Format.fprintf fmt "(%s : %a)" name pp_term ty

let pp_constructor fmt { ctor_name; ctor_args } =
  if ctor_args = [] then
    Format.fprintf fmt "%s" ctor_name
  else
    Format.fprintf fmt "%s : %a"
      ctor_name
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt " → ") pp_binder)
      ctor_args

let pp_inductive fmt { ind_name; params; ind_universe; constructors } =
  Format.fprintf fmt "@[<v 2>Inductive %s%a : %a :=@,%a@]"
    ind_name
    (fun fmt ps ->
      if ps <> [] then
        Format.fprintf fmt " %a"
          (Format.pp_print_list ~pp_sep:Format.pp_print_space pp_binder) ps)
    params
    pp_universe ind_universe
    (Format.pp_print_list ~pp_sep:Format.pp_print_cut
       (fun fmt c -> Format.fprintf fmt "| %a" pp_constructor c))
    constructors

let pp_role fmt = function
  | Runtime -> Format.fprintf fmt "runtime"
  | ProofOnly -> Format.fprintf fmt "proof-only"
  | Both -> Format.fprintf fmt "both"

let pp_def fmt { def_name; def_role; def_type; def_body; rec_args } =
  Format.fprintf fmt "@[<v 2>def %s [%a]%a : %a :=@,%a@]"
    def_name
    pp_role def_role
    (fun fmt args ->
      match args with
      | Some is -> Format.fprintf fmt " [rec_args: %a]"
          (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
             Format.pp_print_int) is
      | None -> ())
    rec_args
    pp_term def_type
    pp_term def_body

let pp_theorem fmt { thm_name; thm_type; thm_proof } =
  Format.fprintf fmt "@[<v 2>theorem %s : %a :=@,%a@]"
    thm_name
    pp_term thm_type
    pp_term thm_proof

let pp_declaration fmt = function
  | Inductive ind -> pp_inductive fmt ind
  | Definition def -> pp_def fmt def
  | Theorem thm -> pp_theorem fmt thm
  | Repr repr ->
      Format.fprintf fmt "repr %s" repr.repr_name
  | ExternC ext ->
      Format.fprintf fmt "extern_c %s = \"%s\"" ext.extern_name ext.c_name

let pp_module fmt { module_name; imports; declarations } =
  Format.fprintf fmt "@[<v>module %s@,@,imports: %a@,@,@[<v>%a@]@]"
    module_name
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ") Format.pp_print_string)
    imports
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "@,@,") pp_declaration)
    declarations

let module_to_string m =
  Format.asprintf "%a" pp_module m
