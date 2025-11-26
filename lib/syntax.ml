(** Abstract syntax for CertiJSON core terms.
    
    This module defines the internal representation of CertiJSON programs
    after parsing from JSON. *)

module Loc = Loc

(** {1 Identifiers} *)

type name = string
[@@deriving show, eq]

type var = string
[@@deriving show, eq]

(** {1 Universes} *)

type universe =
  | Type  (** Computational types *)
  | Prop  (** Propositions (erased at runtime) *)
[@@deriving show, eq]

(** {1 Primitive Types} *)

type prim_type =
  | Int32
  | Int64
  | Float64
  | Bool
  | String
  | Size
[@@deriving show, eq]

(** {1 Literals} *)

type literal =
  | LitInt32 of int32
  | LitInt64 of int64
  | LitFloat64 of float
  | LitBool of bool
  | LitString of string
[@@deriving show, eq]

(** {1 Roles} *)

type role =
  | Runtime     (** Kept at runtime *)
  | ProofOnly   (** Erased at runtime *)
  | Both        (** Available in both contexts *)
[@@deriving show, eq]

(** {1 Terms with locations} *)

type term_desc =
  | Var of var
  | Universe of universe
  | PrimType of prim_type
  | Literal of literal
  | Pi of { arg : binder; result : term }
  | Lambda of { arg : binder; body : term }
  | App of term * term list
  | Eq of { ty : term; lhs : term; rhs : term }
  | Refl of { ty : term; value : term }
  | Rewrite of { proof : term; body : term }
  | If of { cond : term; then_ : term; else_ : term }
  | Match of {
      scrutinee : term;
      motive : term;
      as_name : name option;
      cases : case list;
      coverage_hint : coverage_hint;
    }
  | Global of name
  | Subset of { arg : binder; pred : term }
  | SubsetIntro of { value : term; proof : term }
  | SubsetElim of term
  | SubsetProof of term
  | Array of { elem_ty : term; size : term }
  | ArrayHandle of { elem_ty : term; size : term }

and term = {
  desc : term_desc;
  loc : Loc.t option;
}
[@@deriving show, eq]

(** {1 Binders} *)

and binder = {
  name : name;
  ty : term;
  role : role;
  b_loc : Loc.t option;
}
[@@deriving show, eq]

(** {1 Pattern Matching} *)

and pattern_arg = {
  arg_name : name;
  arg_loc : Loc.t option;
}
[@@deriving show, eq]

and pattern = {
  ctor : name;
  args : pattern_arg list;
  pat_loc : Loc.t option;
}
[@@deriving show, eq]

and case = {
  pattern : pattern;
  body : term;
  case_loc : Loc.t option;
}
[@@deriving show, eq]

and coverage_hint =
  | Complete
  | Unknown
[@@deriving show, eq]

(** {1 Representation Descriptors} *)

type repr_field = {
  field_name : name;
  field_repr : name;
  offset_bytes : int;
}
[@@deriving show, eq]

type repr_kind =
  | Primitive of {
      c_type : string;
      size_bits : int;
      signed : bool;
    }
  | Struct of {
      c_struct_name : string;
      size_bytes : int;
      align_bytes : int;
      fields : repr_field list;
    }
[@@deriving show, eq]

type repr_decl = {
  repr_name : name;
  kind : repr_kind;
  repr_loc : Loc.t option;
}
[@@deriving show, eq]

(** {1 Foreign Function Interface} *)

type extern_arg = {
  extern_arg_name : name;
  extern_arg_repr : name;
}
[@@deriving show, eq]

type safety =
  | Pure
  | Impure
[@@deriving show, eq]

type extern_c_decl = {
  extern_name : name;
  c_name : string;
  header : string;
  return_repr : name option;
  args : extern_arg list;
  logical_type : term;
  safety : safety;
  axioms : name list;
  extern_loc : Loc.t option;
}
[@@deriving show, eq]

type extern_io_decl = {
  extern_io_name : name;
  c_name : string;
  header : string;
  args : extern_arg list;
  result_repr : name option;
  logical_type : term;
  pre_cond : string option;
  post_cond : string option;
  extern_io_loc : Loc.t option;
}
[@@deriving show, eq]

(** {1 Inductive Definitions} *)

type constructor_decl = {
  ctor_name : name;
  ctor_args : binder list;
  ctor_loc : Loc.t option;
}
[@@deriving show, eq]

type inductive_decl = {
  ind_name : name;
  params : binder list;
  ind_universe : universe;
  constructors : constructor_decl list;
  ind_loc : Loc.t option;
}
[@@deriving show, eq]

(** {1 Definitions and Theorems} *)

type def_decl = {
  def_name : name;
  def_role : role;
  def_type : term;
  def_body : term;
  rec_args : int list option;
  def_loc : Loc.t option;
}
[@@deriving show, eq]

type theorem_decl = {
  thm_name : name;
  thm_type : term;
  thm_proof : term;
  thm_loc : Loc.t option;
}
[@@deriving show, eq]

(** {1 Declarations} *)

type declaration =
  | Inductive of inductive_decl
  | Definition of def_decl
  | Theorem of theorem_decl
  | Repr of repr_decl
  | ExternC of extern_c_decl
  | ExternIO of extern_io_decl
[@@deriving show, eq]

(** {1 Modules} *)

type module_decl = {
  module_name : name;
  imports : name list;
  declarations : declaration list;
  module_loc : Loc.t option;
}
[@@deriving show, eq]

(** {1 Utility Functions} *)

(** Helper to rebuild terms with preserved or overridden location. *)
let with_loc ?loc (t : term) desc =
  let loc = match loc with Some l -> Some l | None -> t.loc in
  { desc; loc }

let mk ?loc desc = { desc; loc }

(** [subst x s t] substitutes term [s] for variable [x] in term [t]. *)
let rec subst (x : var) (s : term) (t : term) : term =
  match t.desc with
  | Var y -> if String.equal x y then s else t
  | Universe _ | PrimType _ | Literal _ | Global _ -> t
  | Pi { arg; result } ->
      let arg' = { arg with ty = subst x s arg.ty } in
      if String.equal x arg.name then
        with_loc t (Pi { arg = arg'; result })
      else
        with_loc t (Pi { arg = arg'; result = subst x s result })
  | Lambda { arg; body } ->
      let arg' = { arg with ty = subst x s arg.ty } in
      if String.equal x arg.name then
        with_loc t (Lambda { arg = arg'; body })
      else
        with_loc t (Lambda { arg = arg'; body = subst x s body })
  | App (f, args) ->
      with_loc t (App (subst x s f, List.map (subst x s) args))
  | Eq { ty; lhs; rhs } ->
      with_loc t (Eq { ty = subst x s ty; lhs = subst x s lhs; rhs = subst x s rhs })
  | Refl { ty; value } ->
      with_loc t (Refl { ty = subst x s ty; value = subst x s value })
  | Rewrite { proof; body } ->
      with_loc t (Rewrite { proof = subst x s proof; body = subst x s body })
  | If { cond; then_; else_ } ->
      with_loc t (If { cond = subst x s cond; then_ = subst x s then_; else_ = subst x s else_ })
  | Match { scrutinee; motive; as_name; cases; coverage_hint } ->
      let scrutinee' = subst x s scrutinee in
      let motive' =
        match as_name with
        | Some n when String.equal x n -> motive
        | _ -> subst x s motive
      in
      let cases' =
        List.map
          (fun c ->
            let bound =
              List.map (fun a -> a.arg_name) c.pattern.args
            in
            if List.mem x bound then c
            else { c with body = subst x s c.body })
          cases
      in
      with_loc t
        (Match
           {
             scrutinee = scrutinee';
             motive = motive';
             as_name;
             cases = cases';
             coverage_hint;
           })
  | Subset { arg; pred } ->
      let arg' = { arg with ty = subst x s arg.ty } in
      if String.equal x arg.name then
        with_loc t (Subset { arg = arg'; pred })
      else
        with_loc t (Subset { arg = arg'; pred = subst x s pred })
  | SubsetIntro { value; proof } ->
      with_loc t (SubsetIntro { value = subst x s value; proof = subst x s proof })
  | SubsetElim tm ->
      with_loc t (SubsetElim (subst x s tm))
  | SubsetProof tm ->
      with_loc t (SubsetProof (subst x s tm))
  | Array { elem_ty; size } ->
      with_loc t (Array { elem_ty = subst x s elem_ty; size = subst x s size })
  | ArrayHandle { elem_ty; size } ->
      with_loc t (ArrayHandle { elem_ty = subst x s elem_ty; size = subst x s size })

(** [free_vars t] returns the set of free variables in term [t]. *)
let free_vars (t : term) : var list =
  let module S = Set.Make (String) in
  let rec go acc (t : term) =
    match t.desc with
    | Var x -> S.add x acc
    | Universe _ | PrimType _ | Literal _ | Global _ -> acc
    | Pi { arg; result } ->
        let acc = go acc arg.ty in
        S.remove arg.name (go acc result)
    | Lambda { arg; body } ->
        let acc = go acc arg.ty in
        S.remove arg.name (go acc body)
    | App (f, args) ->
        List.fold_left go (go acc f) args
    | Eq { ty; lhs; rhs } ->
        go (go (go acc ty) lhs) rhs
    | Refl { ty; value } ->
        go (go acc ty) value
  | Rewrite { proof; body } ->
        go (go acc proof) body
  | If { cond; then_; else_ } ->
        go (go (go acc cond) then_) else_
  | Match { scrutinee; motive; as_name; cases; _ } ->
        let acc = go acc scrutinee in
        let acc =
          match as_name with
          | Some n -> S.remove n (go acc motive)
          | None -> go acc motive
        in
        List.fold_left
          (fun acc c ->
            let bound =
              List.fold_left
                (fun s a -> S.add a.arg_name s)
                S.empty c.pattern.args
            in
            S.union acc (S.diff (go S.empty c.body) bound))
          acc cases
    | Subset { arg; pred } ->
        let acc = go acc arg.ty in
        S.remove arg.name (go acc pred)
    | SubsetIntro { value; proof } ->
        go (go acc value) proof
    | SubsetElim tm ->
        go acc tm
    | SubsetProof tm ->
        go acc tm
    | Array { elem_ty; size } ->
        go (go acc elem_ty) size
    | ArrayHandle { elem_ty; size } ->
        go (go acc elem_ty) size
  in
  S.elements (go S.empty t)
