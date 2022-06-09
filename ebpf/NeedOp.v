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

Require Import Op.
Require Import NeedDomain.

Definition needs_of_condition (cond: condition): list nval := nil.

Definition needs_of_operation (op: operation) (nv: nval): list nval := nil.

Definition operation_is_redundant (op: operation) (nv: nval): bool := false.
