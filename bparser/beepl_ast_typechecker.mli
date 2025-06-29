open Beepl_ast

(** Raised when a type error is found during type checking. *)
exception TypeError of string

(** Type environment mapping variable names to types. *)
module Env : Map.S with type key = string
type tyenv = typ Env.t

val predefined_externals : (string * Beepl_ast.typ) list

val list_to_env : (string * typ) list -> tyenv

val string_of_ptype : ptype -> string

val string_of_typ : typ -> string

(** Check if two primitive types are equal. *)

(** Convert a type to a string representation. *)

(** Check that an expression is well-typed under the given environment.
    Returns the inferred type of the expression. Raises [TypeError] on failure. *)
val infer_expr : tyenv -> expr -> typ

(** Type check a function declaration. Raises [TypeError] if invalid. *)
val infer_fundecl : fundecl -> tyenv -> unit

(** Type check an entire program. Raises [TypeError] if any function is invalid. *)
val infer_program : program -> unit




