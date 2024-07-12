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

Require Import String.
Require Import Coqlib.
Require Import Decidableplus.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Op.

(** ** Machine registers *)

(** The following type defines the machine registers that can be referenced
  as locations.  These include Integer registers that can be allocated to
  RTL pseudo-registers ([Rxx]).

  The type [mreg] does not include reserved machine registers such as
  the the stack pointer (R10) and the global pointer.
*)

Inductive mreg: Type :=
  (** Allocatable integer regs *)
  | I0: mreg | I1: mreg | I2: mreg | I3: mreg | I4: mreg
  | I5: mreg | I6: mreg | I7: mreg | I8: mreg | I9: mreg
  (** Dummy double-precision float regs *)
  | D0: mreg | D1: mreg | D2: mreg.

Lemma mreg_eq: forall (r1 r2: mreg), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.
Global Opaque mreg_eq.

Definition all_mregs :=
  I0 :: I1 :: I2 :: I3 :: I4 :: I5 :: I6 :: I7 :: I8 :: I9 :: D0 :: D1 :: D2 :: nil.

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


Definition mreg_type (r: mreg): typ :=
  match r with
  | D0 | D1 | D2 => Tany64
  | _  => if Archi.ptr64 then Tany64 else Tany32
  end.

Open Scope positive_scope.

Module IndexedMreg <: INDEXED_TYPE.
  Definition t := mreg.
  Definition eq := mreg_eq.

  Definition index (r: mreg): positive :=
    match r with
    | I0 => 1 | I1 => 2 | I2 => 3 | I3 => 4 | I4 => 5
    | I5 => 6 | I6 => 7 | I7 => 8 | I8 => 9 |I9 => 10
    | D0  => 11 | D1 => 12 | D2 => 13
    end.

  Lemma index_inj:
    forall r1 r2, index r1 = index r2 -> r1 = r2.
  Proof.
    decide_goal.
  Qed.
End IndexedMreg.

Definition is_stack_reg (r: mreg) : bool := false.

(** ** Names of registers *)

Local Open Scope string_scope.

Definition register_names :=
  ("R0", I0) :: ("R1", I1) :: ("R2", I2) :: ("R3", I3) :: ("R4", I4) ::
  ("R5", I5) :: ("R6", I6) :: ("R7", I7) :: ("R8", I8) :: (*("R9", I9) ::*)
  ("D0", D0) :: ("D1", D1) :: ("D2", D2) :: nil.

Definition register_by_name (s: string) : option mreg :=
  let fix assoc (l: list (string * mreg)) : option mreg :=
    match l with
    | nil => None
    | (s1, r1) :: l' => if string_dec s s1 then Some r1 else assoc l'
    end
  in assoc register_names.

(** ** Destroyed registers, preferred registers *)

Definition destroyed_by_op (op: operation): list mreg :=
  match op with
  | Omulhu => I1::nil
  | Omove
  | _ => nil
  end.

Definition destroyed_by_load (chunk: memory_chunk) (addr: addressing): list mreg := nil.

Definition destroyed_by_store (chunk: memory_chunk) (addr: addressing): list mreg := nil.

Definition destroyed_by_cond (cond: condition): list mreg := nil.

Definition destroyed_by_jumptable: list mreg := nil.

Fixpoint destroyed_by_clobber (cl: list string): list mreg :=
  match cl with
  | nil => nil
  | c1 :: cl =>
      match register_by_name c1 with
      | Some r => r :: destroyed_by_clobber cl
      | None   => destroyed_by_clobber cl
      end
  end.

Definition destroyed_by_builtin (ef: external_function): list mreg :=
  match ef with
  | EF_inline_asm txt sg clob => destroyed_by_clobber clob
  | EF_memcpy sz al => I1 :: I2 :: I3 :: nil
  | EF_builtin name sg => nil
  | _ => nil
  end.

Definition destroyed_by_setstack (ty: typ): list mreg := nil.

Definition destroyed_at_function_entry: list mreg := I0 :: nil.

Definition temp_for_parent_frame: mreg := I0.

Definition destroyed_at_indirect_call: list mreg := nil.

Definition mregs_for_operation (op: operation): list (option mreg) * option mreg :=
  (nil,None).

Definition mregs_for_builtin (ef: external_function): list (option mreg) * list(option mreg) :=
  match ef with
  | _ => (nil, nil)
  end.

Global Opaque
    destroyed_by_op destroyed_by_load destroyed_by_store
    destroyed_by_cond destroyed_by_jumptable destroyed_by_builtin
    destroyed_by_setstack destroyed_at_function_entry temp_for_parent_frame
    mregs_for_operation mregs_for_builtin.

(** Two-address operations.  Return [true] if the first argument and
  the result must be in the same location *and* are unconstrained
  by [mregs_for_operation]. *)

Definition two_address_op (op: operation) : bool :=
  match op with
    (* 32 bits *)
  | Oadd | Oaddimm _ | Oneg | Osub | Osubimm _
  | Omul | Omulimm _ | Odivu | Omodu
  | Oand | Oandimm _ | Oor | Oorimm _
  | Oxor | Oxorimm _ | Oshl | Oshlimm _
  | Oshr | Oshrimm _ | Oshru | Oshruimm _
  | Ocmp (Ccomp _ | Ccompu _ | Ccompimm _ _ | Ccompuimm _ _)
  | Odivuimm _ | Omoduimm _
  (*| Omulhs*) | Omulhu |  Omod
  | Ocast8signed | Ocast16signed => true
    (* 64 bits *)
  | Ocast32unsigned | Ocast32signed | Olowlong
  | Ocmp (Ccompl _ | Ccomplu _ | Ccomplimm _ _ | Ccompluimm _ _)
  | Oaddl | Oaddlimm _ | Onegl | Osubl | Osublimm _
  | Omull | Omullimm _ | Odivlu | Omodlu
  | Oandl | Oandlimm _ | Oorl | Oorlimm _
  | Oxorl | Oxorlimm _ | Oshll | Oshllimm _
  | Oshrl | Oshrlimm _ | Oshrlu | Oshrluimm _ => true
  | _ => false
  end.

(** Constraints on constant propagation for builtins *)

Definition builtin_constraints (ef: external_function) :
                                       list builtin_arg_constraint :=
  match ef with
  | EF_builtin id sg => nil
  | EF_vload _ => OK_addressing :: nil
  | EF_vstore _ => OK_addressing :: OK_default :: nil
  | EF_memcpy _ _ => OK_addrstack :: OK_addrstack :: nil
  | EF_annot kind txt targs => map (fun _ => OK_all) targs
  | EF_debug kind txt targs => map (fun _ => OK_all) targs
  | _ => nil
  end.
