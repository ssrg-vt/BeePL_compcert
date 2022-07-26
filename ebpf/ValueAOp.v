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

Require Import Coqlib Compopts.
Require Import AST Integers Floats Values Globalenvs.
Require Import Op RTL ValueDomain.

Definition eval_static_condition (cond: condition) (vl: list aval): abool :=
  match cond, vl with
  | Ccomp c, v1 :: v2 :: nil => cmp_bool c v1 v2
  | Ccompu c, v1 :: v2 :: nil => cmpu_bool c v1 v2
  | Ccompimm c n, v1 :: nil => cmp_bool c v1 (I n)
  | Ccompuimm c n, v1 :: nil => cmpu_bool c v1 (I n)
  | Ccompf c, v1 :: v2 :: nil => cmpf_bool c v1 v2
  | Cnotcompf c, v1 :: v2 :: nil => cnot (cmpf_bool c v1 v2)
  | Ccompfs c, v1 :: v2 :: nil => cmpfs_bool c v1 v2
  | Cnotcompfs c, v1 :: v2 :: nil => cnot (cmpfs_bool c v1 v2)
  | _, _ => Bnone
  end.

Definition eval_static_addressing (addr: addressing) (vl: list aval): aval :=
  match addr, vl with
  | Aindexed n, v1::nil => offset_ptr v1 n
  | Ainstack ofs, nil => Ptr (Stk ofs)
  | _, _ => Vbot
  end.

Definition eval_static_operation (op: operation) (vl: list aval): aval :=
  match op, vl with
  | Omove, v1::nil => v1
  | Ointconst n, nil => I n
  | Oaddrstack ofs, nil => Ptr (Stk ofs)
  | Oadd, v1::v2::nil => add v1 v2
  | Oaddimm n, v1::nil => add v1 (I n)
  | Oneg, v1::nil => neg v1
  | Osub, v1::v2::nil => sub v1 v2
  | Osubimm n, v1::nil => sub v1 (I n)
  | Omul, v1::v2::nil => mul v1 v2
  | Omulimm n, v1::nil => mul v1 (I n)
  | Odivu, v1::v2::nil => divu v1 v2
  | Odivuimm n, v1::nil => divu v1 (I n)
  | Omodu, v1::v2::nil => modu v1 v2
  | Omoduimm n, v1::nil => modu v1 (I n)
  | Oand, v1::v2::nil => and v1 v2
  | Oandimm n, v1::nil => and v1 (I n)
  | Oor, v1::v2::nil => or v1 v2
  | Oorimm n, v1::nil => or v1 (I n)
  | Oxor, v1::v2::nil => xor v1 v2
  | Oxorimm n, v1::nil => xor v1 (I n)
  | Oshl, v1::v2::nil => shl v1 v2
  | Oshlimm n, v1::nil => shl v1 (I n)
  | Oshr, v1::v2::nil => shr v1 v2
  | Oshrimm n, v1::nil => shr v1 (I n)
  | Oshru, v1::v2::nil => shru v1 v2
  | Oshruimm n, v1::nil => shru v1 (I n)
  | Ocmp c, _ => of_optbool (eval_static_condition c vl)

  | Ofloatconst n, nil => if propagate_float_constants tt then F n else ntop
  | Osingleconst n, nil => if propagate_float_constants tt then FS n else ntop
  | Oaddrsymbol id ofs, nil => Ptr (Gl id ofs)
  | Ocast8signed, v1 :: nil => sign_ext 8 v1
  | Ocast16signed, v1 :: nil => sign_ext 16 v1
  | Omulhs, v1::v2::nil => mulhs v1 v2
  | Omulhu, v1::v2::nil => mulhu v1 v2
  | Odiv, v1::v2::nil => divs v1 v2
  | Omod, v1::v2::nil => mods v1 v2
  | Oshrximm n, v1::nil => shrx v1 (I n)
  | Omakelong, v1::v2::nil => longofwords v1 v2
  | Olowlong, v1::nil => loword v1
  | Ohighlong, v1::nil => hiword v1
  | Onegf, v1::nil => negf v1
  | Oabsf, v1::nil => absf v1
  | Oaddf, v1::v2::nil => addf v1 v2
  | Osubf, v1::v2::nil => subf v1 v2
  | Omulf, v1::v2::nil => mulf v1 v2
  | Odivf, v1::v2::nil => divf v1 v2
  | Onegfs, v1::nil => negfs v1
  | Oabsfs, v1::nil => absfs v1
  | Oaddfs, v1::v2::nil => addfs v1 v2
  | Osubfs, v1::v2::nil => subfs v1 v2
  | Omulfs, v1::v2::nil => mulfs v1 v2
  | Odivfs, v1::v2::nil => divfs v1 v2
  | Osingleoffloat, v1::nil => singleoffloat v1
  | Ofloatofsingle, v1::nil => floatofsingle v1
  | Ointoffloat, v1::nil => intoffloat v1
  | Ointuoffloat, v1::nil => intuoffloat v1
  | Ofloatofint, v1::nil => floatofint v1
  | Ofloatofintu, v1::nil => floatofintu v1
  | Ointofsingle, v1::nil => intofsingle v1
  | Ointuofsingle, v1::nil => intuofsingle v1
  | Osingleofint, v1::nil => singleofint v1
  | Osingleofintu, v1::nil => singleofintu v1
  | Olongoffloat, v1::nil => longoffloat v1
  | Olonguoffloat, v1::nil => longuoffloat v1
  | Ofloatoflong, v1::nil => floatoflong v1
  | Ofloatoflongu, v1::nil => floatoflongu v1
  | Olongofsingle, v1::nil => longofsingle v1
  | Olonguofsingle, v1::nil => longuofsingle v1
  | Osingleoflong, v1::nil => singleoflong v1
  | Osingleoflongu, v1::nil => singleoflongu v1
  | _, _ => Vbot
  end.

Section SOUNDNESS.

Variable bc: block_classification.
Variable ge: genv.
Hypothesis GENV: genv_match bc ge.
Variable sp: block.
Hypothesis STACK: bc sp = BCstack.

Theorem eval_static_condition_sound:
  forall cond vargs m aargs,
  list_forall2 (vmatch bc) vargs aargs ->
  cmatch (eval_condition cond vargs m) (eval_static_condition cond aargs).
Proof.
  intros until aargs; intros VM. inv VM.
  destruct cond; auto with va.
  inv H0.
  destruct cond; simpl; eauto with va.
  inv H2.
  destruct cond; simpl; eauto with va.
  destruct cond; auto with va.
Qed.

Lemma symbol_address_sound:
  forall id ofs,
  vmatch bc (Genv.symbol_address ge id ofs) (Ptr (Gl id ofs)).
Proof.
  intros; apply symbol_address_sound; apply GENV.
Qed.

Lemma symbol_address_sound_2:
  forall id ofs,
  vmatch bc (Genv.symbol_address ge id ofs) (Ifptr (Gl id ofs)).
Proof.
  intros. unfold Genv.symbol_address. destruct (Genv.find_symbol ge id) as [b|] eqn:F.
  constructor. constructor. apply GENV; auto.
  constructor.
Qed.

Hint Resolve symbol_address_sound symbol_address_sound_2: va.

Ltac InvHyps :=
  match goal with
  | [H: None = Some _ |- _ ] => discriminate
  | [H: Some _ = Some _ |- _] => inv H
  | [H1: match ?vl with nil => _ | _ :: _ => _ end = Some _ ,
     H2: list_forall2 _ ?vl _ |- _ ] => inv H2; InvHyps
  | [H: (if Archi.ptr64 then _ else _) = Some _ |- _] => destruct Archi.ptr64 eqn:?; InvHyps
  | _ => idtac
  end.

Theorem eval_static_addressing_sound:
  forall addr vargs vres aargs,
  eval_addressing ge (Vptr sp Ptrofs.zero) addr vargs = Some vres ->
  list_forall2 (vmatch bc) vargs aargs ->
  vmatch bc vres (eval_static_addressing addr aargs).
Proof.
  unfold eval_addressing, eval_static_addressing; intros;
  destruct addr; InvHyps; eauto with va.
  rewrite Ptrofs.add_zero_l; eauto with va.
Qed.

Theorem eval_static_operation_sound:
  forall op vargs m vres aargs,
  eval_operation ge (Vptr sp Ptrofs.zero) op vargs m = Some vres ->
  list_forall2 (vmatch bc) vargs aargs ->
  vmatch bc vres (eval_static_operation op aargs).
Proof.
  unfold eval_operation, eval_static_operation; intros;
  destruct op; InvHyps; eauto with va.
  rewrite Ptrofs.add_zero_l; eauto with va.
  apply of_optbool_sound. eapply eval_static_condition_sound; eauto.
  destruct (propagate_float_constants tt); constructor.
  destruct (propagate_float_constants tt); constructor.
Qed.

End SOUNDNESS.
