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

Require Import Coqlib.
Require Import Decidableplus.
Require Import Maps.
Require Import AST.
Require Import Op.

(** ** eBPF registers *)

Inductive mreg: Type := R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10 | PC.

Lemma mreg_eq: forall (r1 r2: mreg), {r1 = r2} + {r1 <> r2}.
Proof.
  decide equality.
Defined.

Global Opaque mreg_eq.

Definition all_mregs :=
  R0 :: R1 :: R2 :: R3 :: R4 :: R5 :: R6 :: R7 :: R8 :: R9 :: R10 :: PC :: nil.

Lemma all_mregs_complete:
  forall (r: mreg), In r all_mregs.
Proof.
  assert (forall r, proj_sumbool (In_dec mreg_eq r all_mregs) = true) by (destruct r; reflexivity).
  intros. specialize (H r). InvBooleans. auto.
Qed.

Global Instance Decidable_eq_mreg : forall (x y: mreg), Decidable (eq x y) := Decidable_eq mreg_eq.

Global Instance Finite_mreg : Finite mreg := {
  Finite_elements := all_mregs;
  Finite_elements_spec := all_mregs_complete
}.

Definition mreg_type (r: mreg): typ := Tany32.

Local Open Scope positive_scope.

Module IndexedMreg <: INDEXED_TYPE.
  Definition t := mreg.
  Definition eq := mreg_eq.
  Definition index (r: mreg): positive :=
    match r with
    | R0 => 1 | R1 => 2 | R2 => 3 | R3 => 4 | R4 => 5 | R5 => 6
    | R6 => 7 | R7 => 8 | R8 => 9 | R9 => 10 | R10 => 11 | PC => 12
    end.

  Lemma index_inj:
    forall r1 r2, index r1 = index r2 -> r1 = r2.
  Proof.
    decide_goal.
  Qed.
End IndexedMreg.

Definition is_stack_reg (r: mreg) : bool := false.

Definition mregs_for_operation (op: operation): list (option mreg) * option mreg := (nil, None).

Definition mregs_for_builtin (ef: external_function): list (option mreg) * list(option mreg) := (nil, nil).

Definition temp_for_parent_frame: mreg := R0.

(** ** Destroyed registers, preferred registers *)

Definition destroyed_by_op (op: operation): list mreg := nil.

Definition destroyed_by_load (chunk: memory_chunk) (addr: addressing): list mreg := nil.

Definition destroyed_by_store (chunk: memory_chunk) (addr: addressing): list mreg := nil.

Definition destroyed_by_cond (cond: condition): list mreg := nil.

Definition destroyed_by_jumptable: list mreg := R5 :: nil.

Definition destroyed_by_builtin (ef: external_function): list mreg :=
  match ef with
  | EF_memcpy sz al => R5 :: R6 :: R7 :: nil (* TODO *)
  | _ => nil
  end.

Definition destroyed_at_indirect_call: list mreg := nil.

Definition destroyed_by_setstack (ty: typ): list mreg := nil.

Definition destroyed_at_function_entry: list mreg := nil.

(** ** Names of registers *)

Local Open Scope string_scope.

Definition register_names := ("R0", R0) :: ("R1", R1) :: ("R2", R2) :: nil.

Definition register_by_name (s: string) : option mreg :=
  let fix assoc (l: list (string * mreg)) : option mreg :=
    match l with
    | nil => None
    | (s1, r1) :: l' => if string_dec s s1 then Some r1 else assoc l'
    end
  in assoc register_names.

Global Opaque
    destroyed_by_op destroyed_by_load destroyed_by_store
    destroyed_by_cond destroyed_by_jumptable destroyed_by_builtin
    destroyed_by_setstack destroyed_at_function_entry temp_for_parent_frame
    mregs_for_operation mregs_for_builtin.

(** Two-address operations.  Return [true] if the first argument and
  the result must be in the same location *and* are unconstrained
  by [mregs_for_operation].  There are two: the pseudo [Ocast32signed],
  because it expands to a no-op owing to the representation of 32-bit
  integers as their 64-bit sign extension; and [Ocast32unsigned],
  because it builds on the same magic no-op. *)

Definition two_address_op (op: operation) : bool :=
  match op with
  | Ocast32signed | Ocast32unsigned => true
  | _ => false
  end.

(** Constraints on constant propagation for builtins *)

Definition builtin_constraints (ef: external_function) : list builtin_arg_constraint := nil.
