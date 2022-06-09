(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                Xavier Leroy, INRIA Paris                            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Recognition of combined operations, addressing modes and conditions
  during the [CSE] phase. *)

Require Import Op.
Require Import CSEdomain.

(* Section COMBINE. *)

(* Variable get: valnum -> option rhs. *)

Function combine_cond (get: valnum -> option rhs) (cond: condition) (args: list valnum) : option(condition * list valnum) := None.

Function combine_addr (get: valnum -> option rhs) (addr: addressing) (args: list valnum) : option(addressing * list valnum) := None.

Function combine_op (get: valnum -> option rhs) (op: operation) (args: list valnum) : option(operation * list valnum) :=
  match op, args with
  | _, _ => None
  end.

(* End COMBINE. *)
