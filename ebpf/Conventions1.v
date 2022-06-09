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

(** Function calling conventions and other conventions regarding the use of
    machine registers and stack slots. *)

(* Require Import Coqlib. *)
(* Require Import AST Integers Locations. *)
Require Import Coqlib Decidableplus.
Require Import AST Machregs Locations.

(** ** Location of function arguments *)

Definition int_param_regs :=
  R1 :: R2 :: R3 :: R4 :: R5 :: nil.

Definition float_param_regs: list mreg := nil.
Definition float_extra_param_regs: list mreg := nil.


(** ** Location of function result *)

(** The result value of a function is passed back to the caller in
  registers [R10] or [F10] or [R10,R11], depending on the type of the
  returned value.  We treat a function without result as a function
  with one integer result. *)

Definition loc_result (s: signature) : rpair mreg :=
  match proj_sig_res s with
  | Tint | Tany32 => One R0
  | Tfloat | Tsingle | Tany64 => One R0
  | Tlong => if Archi.ptr64 then One R0 else Twolong R0 R1
  end.

Definition float_arg (va: bool) (ri rf ofs: Z) (ty: typ)
                     (rec: Z -> Z -> Z -> list (rpair loc)) :=
  match list_nth_z (if va then nil else float_param_regs) rf with
  | Some r =>
      One (R r) :: rec ri (rf + 1) ofs
  | None =>
      (* We are out of FP registers, or cannot use them because vararg,
         so try to put the argument in an extra FP register while
         reserving an integer register or register pair into which
         fixup code will move the extra FP register. *)
      let regpair := negb Archi.ptr64 && zeq (typesize ty) 2 in
      let ri' := if va && regpair then align ri 2 else ri in
      match list_nth_z float_extra_param_regs ri' with
      | Some r =>
          let ri'' := ri' + (if Archi.ptr64 then 1 else typesize ty) in
          let ofs'' := if regpair && zeq ri' 7 then ofs + 1 else ofs in
          One (R r) :: rec ri'' rf ofs''
      | None =>
          (* We are out of integer registers, pass argument on stack *)
            let ofs := align ofs (typesize ty) in
            One(S Outgoing ofs ty)
            :: rec ri' rf (ofs + (if Archi.ptr64 then 2 else typesize ty))
      end
  end.

Definition int_arg (ri rf ofs: Z) (ty: typ)
                   (rec: Z -> Z -> Z -> list (rpair loc)) :=
  match list_nth_z int_param_regs ri with
  | Some r =>
      One(R r) :: rec (ri + 1) rf ofs
  | None   =>
      let ofs := align ofs (typesize ty) in
      One(S Outgoing ofs ty)
      :: rec ri rf (ofs + (if Archi.ptr64 then 2 else typesize ty))
  end.

Definition split_long_arg (va: bool) (ri rf ofs: Z)
                          (rec: Z -> Z -> Z -> list (rpair loc)) :=
  let ri := if va then align ri 2 else ri in
  match list_nth_z int_param_regs ri, list_nth_z int_param_regs (ri + 1) with
  | Some r1, Some r2 =>
      Twolong (R r2) (R r1) :: rec (ri + 2) rf ofs
  | Some r1, None =>
      Twolong (S Outgoing ofs Tint) (R r1) :: rec (ri + 1) rf (ofs + 1)
  | None, _ =>
      let ofs := align ofs 2 in
      Twolong (S Outgoing (ofs + 1) Tint) (S Outgoing ofs Tint) ::
      rec ri rf (ofs + 2)
  end.

Definition is_callee_save (r: mreg) : bool :=
  match r with
  | R6 | R7 | R8 | R9 => true
  | _ => false
  end.

Definition int_caller_save_regs :=
  R0 :: R1 :: R2 :: R3 :: R4 :: R5 :: nil.

Definition float_caller_save_regs: list mreg := nil.

Definition int_callee_save_regs :=
  R6 :: R7 :: R8 :: R9 :: R10 :: nil.

Definition float_callee_save_regs: list mreg := nil.

Definition callee_save_type := mreg_type.

Definition is_float_reg (r: mreg) := false.

Definition dummy_int_reg   := R6.    (**r Used in [Coloring]. *)
Definition dummy_float_reg := R0.   (**r Used in [Coloring]. *)

Definition destroyed_at_call :=
  List.filter (fun r => negb (is_callee_save r)) all_mregs.

(** [loc_arguments s] returns the list of locations where to store arguments
  when calling a function with signature [s].  *)

Fixpoint loc_arguments_rec
    (tyl: list typ) (fixed ri rf ofs: Z) {struct tyl} : list (rpair loc) :=
  match tyl with
  | nil => nil
  | (Tint | Tany32) as ty :: tys =>
      (* pass in one integer register or on stack *)
      int_arg ri rf ofs ty (loc_arguments_rec tys (fixed - 1))
  | Tsingle as ty :: tys =>
      (* pass in one FP register or on stack.
         If vararg, reserve 1 integer register. *)
      float_arg (zle fixed 0) ri rf ofs ty (loc_arguments_rec tys (fixed - 1))
  | Tlong as ty :: tys =>
      if Archi.ptr64 then
        (* pass in one integer register or on stack *)
        int_arg ri rf ofs ty (loc_arguments_rec tys (fixed - 1))
      else
        (* pass in register pair or on stack; align register pair if vararg *)
        split_long_arg (zle fixed 0) ri rf ofs(loc_arguments_rec tys (fixed - 1))
  | (Tfloat | Tany64) as ty :: tys =>
      (* pass in one FP register or on stack.
         If vararg, reserve 1 or 2 integer registers. *)
      float_arg (zle fixed 0) ri rf ofs ty (loc_arguments_rec tys (fixed - 1))
  end.

(** Number of fixed arguments for a function with signature [s]. *)

Definition fixed_arguments (s: signature) : Z :=
  match s.(sig_cc).(cc_vararg) with
  | Some n => n
  | None => list_length_z s.(sig_args)
  end.

(** [loc_arguments s] returns the list of locations where to store arguments
  when calling a function with signature [s].  *)

Definition loc_arguments (s: signature) : list (rpair loc) :=
  loc_arguments_rec s.(sig_args) (fixed_arguments s) 0 0 0.

(** Argument locations are either non-temporary registers or [Outgoing]
  stack slots at nonnegative offsets. *)

Definition loc_argument_acceptable (l: loc) : Prop :=
  match l with
  | R r => is_callee_save r = false
  | S Outgoing ofs ty => ofs >= 0 /\ (typealign ty | ofs)
  | _ => False
  end.

Lemma loc_arguments_acceptable:
  forall (s: signature) (p: rpair loc),
  In p (loc_arguments s) -> forall_rpair loc_argument_acceptable p.
Proof.
Admitted.

(** The location of the result depends only on the result part of the signature *)

Lemma loc_result_exten:
  forall s1 s2, s1.(sig_res) = s2.(sig_res) -> loc_result s1 = loc_result s2.
Proof.
  intros. unfold loc_result, proj_sig_res. rewrite H; auto.
Qed.

Lemma loc_result_caller_save:
  forall (s: signature),
  forall_rpair (fun r => is_callee_save r = false) (loc_result s).
Proof.
  intros. unfold loc_result, is_callee_save;
  destruct (proj_sig_res s); simpl; auto; destruct Archi.ptr64; simpl; auto.
Qed.

Lemma loc_result_pair:
  forall sg,
  match loc_result sg with
  | One _ => True
  | Twolong r1 r2 =>
       r1 <> r2 /\ proj_sig_res sg = Tlong
    /\ subtype Tint (mreg_type r1) = true /\ subtype Tint (mreg_type r2) = true
    /\ Archi.ptr64 = false
  end.
Proof.
  intros.
  unfold loc_result; destruct (proj_sig_res sg); auto.
  unfold mreg_type; destruct Archi.ptr64; auto.
  split; auto. congruence.
Qed.

Lemma loc_result_type:
  forall sig,
  subtype (proj_sig_res sig) (typ_rpair mreg_type (loc_result sig)) = true.
Proof.
Admitted.

(** ** Normalization of function results and parameters *)

(** No normalization needed. *)

Definition return_value_needs_normalization (t: rettype) := false.
Definition parameter_needs_normalization (t: rettype) := false.
