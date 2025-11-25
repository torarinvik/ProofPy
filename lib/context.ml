(** Typing context for CertiJSON type checking.
    
    This module provides the typing context (Γ) and global signature (Σ)
    used during type checking. *)

open Syntax

(** {1 Local Context} *)

(** A local context entry binding a variable to its type. *)
type local_entry = {
  var_name : name;
  var_type : term;
}

(** Local typing context Γ. *)
type local_ctx = local_entry list

(** Empty local context. *)
let empty_local : local_ctx = []

(** Add a binding to the local context. *)
let extend_local (ctx : local_ctx) (x : name) (ty : term) : local_ctx =
  { var_name = x; var_type = ty } :: ctx

(** Lookup a variable in the local context. *)
let lookup_local (ctx : local_ctx) (x : name) : term option =
  match List.find_opt (fun e -> String.equal e.var_name x) ctx with
  | Some e -> Some e.var_type
  | None -> None

(** {1 Global Signature} *)

(** Entry kinds in the global signature. *)
type global_entry =
  | GInductive of inductive_decl
  | GConstructor of {
      parent : name;  (* Parent inductive type *)
      ctor : constructor_decl;
      index : int;    (* Constructor index *)
    }
  | GDefinition of def_decl
  | GTheorem of theorem_decl
  | GRepr of repr_decl
  | GExternC of extern_c_decl

(** Global signature Σ. *)
type signature = {
  entries : (name, global_entry) Hashtbl.t;
  order : name list;  (* Declaration order for serialization *)
}

(** Create an empty signature. *)
let empty_sig () : signature = {
  entries = Hashtbl.create 64;
  order = [];
}

(** Add an entry to the signature. *)
let add_entry (sig_ : signature) (name : name) (entry : global_entry) : unit =
  Hashtbl.add sig_.entries name entry

(** Lookup an entry in the signature. *)
let lookup_sig (sig_ : signature) (name : name) : global_entry option =
  Hashtbl.find_opt sig_.entries name

(** Check if a name is defined in the signature. *)
let mem_sig (sig_ : signature) (name : name) : bool =
  Hashtbl.mem sig_.entries name

(** {1 Combined Context} *)

(** Full typing context: local context + global signature. *)
type context = {
  local : local_ctx;
  global : signature;
}

(** Create a context with empty local and given signature. *)
let make_ctx (sig_ : signature) : context = {
  local = empty_local;
  global = sig_;
}

(** Extend the local context. *)
let extend (ctx : context) (x : name) (ty : term) : context =
  { ctx with local = extend_local ctx.local x ty }

(** Lookup a name (tries local first, then global). *)
let lookup (ctx : context) (x : name) : [`Local of term | `Global of global_entry] option =
  match lookup_local ctx.local x with
  | Some ty -> Some (`Local ty)
  | None ->
      match lookup_sig ctx.global x with
      | Some entry -> Some (`Global entry)
      | None -> None

(** {1 Signature Building} *)

(** Process a module's declarations to build the signature. *)
let build_signature (decls : declaration list) : signature =
  let sig_ = empty_sig () in
  List.iter
    (fun decl ->
      match decl with
      | Inductive ind ->
          add_entry sig_ ind.ind_name (GInductive ind);
          List.iteri
            (fun i ctor ->
              add_entry sig_ ctor.ctor_name
                (GConstructor { parent = ind.ind_name; ctor; index = i }))
            ind.constructors
      | Definition def ->
          add_entry sig_ def.def_name (GDefinition def)
      | Theorem thm ->
          add_entry sig_ thm.thm_name (GTheorem thm)
      | Repr repr ->
          add_entry sig_ repr.repr_name (GRepr repr)
      | ExternC ext ->
          add_entry sig_ ext.extern_name (GExternC ext))
    decls;
  sig_

(** {1 Inductive Type Utilities} *)

(** Get the type of an inductive type former. *)
let inductive_type (ind : inductive_decl) : term =
  let result = Universe ind.ind_universe in
  List.fold_right
    (fun p acc -> Pi { arg = p; result = acc })
    ind.params result

(** Get the type of a constructor. *)
let constructor_type (ind : inductive_decl) (ctor : constructor_decl) : term =
  (* Result type: I p₁ ... pₙ *)
  let result =
    match ind.params with
    | [] -> Global ind.ind_name
    | params ->
        App (Global ind.ind_name, List.map (fun p -> Var p.name) params)
  in
  (* Add constructor arguments *)
  let with_args =
    List.fold_right
      (fun arg acc -> Pi { arg; result = acc })
      ctor.ctor_args result
  in
  (* Add parameters *)
  List.fold_right
    (fun p acc -> Pi { arg = p; result = acc })
    ind.params with_args
