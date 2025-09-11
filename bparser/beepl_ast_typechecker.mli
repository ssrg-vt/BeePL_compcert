open Beepl_ast

(** Raised when a type error is found during type checking. *)
exception TypeError of string

(** Type environment mapping variable names to types. *)
module Env : Map.S with type key = string
type tyenv = typ Env.t

module Senv : sig
    type t
    val empty : t
    val add : string -> (string * typ) list -> t -> t
    val find : string -> t -> (string * typ) list
    val find_field : string -> string -> t -> typ
    val fields_of : string -> t -> (string * typ) list
  end

(** Build a struct environment from the program’s StructDecls. *)
val build_senv : program -> Senv.t

val predefined_externals : (string * typ) list

val list_to_env : (string * typ) list -> tyenv

val string_of_ptype : ptype -> string
val string_of_typ : typ -> string

(** Type inference for expressions (needs struct env + var env). *)
val infer_expr : Senv.t -> tyenv -> expr -> typ

(** Type check a function declaration. *)
val infer_fundecl : fundecl -> Senv.t -> tyenv -> unit

(** Type check an entire program. Builds Senv internally. *)
val infer_program : program -> unit
