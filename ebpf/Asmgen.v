(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                  Xavier Leroy, INRIA Paris                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

Require Archi.
Require Import Coqlib Errors.
Require Import AST Integers Floats Memdata.
Require Import Op Locations Mach Asm.

Definition transf_program (p: Mach.program) : res Asm.program := Error (msg "TODO").
