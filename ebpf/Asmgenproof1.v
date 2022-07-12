(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib Errors Maps.
Require Import AST Zbits Integers Floats Values Memory Globalenvs.
Require Import Op Locations Mach Conventions.
Require Import Asm Asmgen Asmgenproof0.

(** Properties of registers *)

Lemma ireg_of_not_R10:
  forall m r, ireg_of m = OK r -> IR r <> IR R10.
Proof.
  intros. erewrite <- ireg_of_eq; eauto with asmgen.
Qed.

Lemma ireg_of_not_R10':
  forall m r, ireg_of m = OK r -> r <> R10.
Proof.
  intros. apply ireg_of_not_R10 in H. congruence.
Qed.

Global Hint Resolve ireg_of_not_R10 ireg_of_not_R10': asmgen.

(** Useful simplification tactic *)

Ltac Simplif :=
  ((rewrite nextinstr_inv by eauto with asmgen)
  || (rewrite nextinstr_inv1 by eauto with asmgen)
  || (rewrite Pregmap.gss)
  || (rewrite nextinstr_pc)
  || (rewrite Pregmap.gso by eauto with asmgen)); auto with asmgen.

Ltac Simpl := repeat Simplif.

(** * Correctness of eBPF constructor functions *)

Section CONSTRUCTORS.

Variable ge: genv.
Variable fn: function.

(** Add offset to pointer *)

Lemma addptrofs_correct:
  forall rd r1 n k rs m,
  exists rs',
     exec_straight ge fn (addptrofs rd r1 n k) rs m k rs' m
  /\ Val.lessdef (Val.offset_ptr rs#r1 n) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold addptrofs; intros.
  destruct (Ptrofs.eq_dec n Ptrofs.zero).
  - subst n. econstructor; split.
    apply exec_straight_one. simpl; constructor. auto.
    split. Simpl. simpl. destruct (rs r1); simpl; auto. rewrite Ptrofs.add_zero; auto.
    intros; Simpl.
  - eexists; split.
    eapply exec_straight_two; reflexivity.
    split; intros; Simpl.
    simpl.
    unfold Val.add, Val.offset_ptr.
    destruct (rs r1); try constructor.
    change Archi.ptr64 with false; simpl.
    apply Val.lessdef_same; f_equal; f_equal.
    rewrite Ptrofs.of_int_to_int by auto.
    reflexivity.
Qed.

(** Translation of conditional branches *)

Lemma transl_cbranch_signed_correct:
  forall cmp r1 r2 lbl (rs: regset) m b,
  Val.cmp_bool cmp rs#(IR r1) (eval_reg_imm rs r2) = Some b ->
  exec_instr ge fn (transl_cbranch_signed cmp r1 r2 lbl) rs m =
  exec_branch fn lbl rs m (Some b).
Proof.
  intros. destruct cmp; simpl; rewrite ? H; try reflexivity.
  - destruct rs#r1; simpl in H; try discriminate.
    destruct (eval_reg_imm rs r2); simpl in H; try discriminate.
    inv H; simpl.
    reflexivity.
  - destruct rs#r1; simpl in H; try discriminate.
    destruct (eval_reg_imm rs r2); simpl in H; try discriminate.
    inv H; simpl.
    reflexivity.
Qed.

Lemma transl_cbranch_unsigned_correct:
  forall cmp r1 r2 lbl (rs: regset) m b,
  Val.cmpu_bool (Mem.valid_pointer m) cmp rs#(IR r1) (eval_reg_imm rs r2) = Some b ->
  exec_instr ge fn (transl_cbranch_unsigned cmp r1 r2 lbl) rs m =
  exec_branch fn lbl rs m (Some b).
Proof.
  intros. destruct cmp; simpl; rewrite ? H; reflexivity.
Qed.

Ltac ArgsInv :=
  repeat (match goal with
  | [ H: Error _ = OK _ |- _ ] => discriminate
  | [ H: match ?args with nil => _ | _ :: _ => _ end = OK _ |- _ ] => destruct args
  | [ H: bind _ _ = OK _ |- _ ] => monadInv H
  | [ H: match _ with left _ => _ | right _ => assertion_failed end = OK _ |- _ ] => monadInv H; ArgsInv
  | [ H: match _ with true => _ | false => assertion_failed end = OK _ |- _ ] => monadInv H; ArgsInv
  end);
  subst;
  repeat (match goal with
  | [ H: ireg_of _ = OK _ |- _ ] => simpl in *; rewrite (ireg_of_eq _ _ H) in *
  | [ H: freg_of _ = OK _ |- _ ] => simpl in *; rewrite (freg_of_eq _ _ H) in *
  end).

Lemma transl_cbranch_correct_1:
  forall cond args lbl k c m ms b sp rs m',
  transl_cbranch cond args lbl k = OK c ->
  eval_condition cond (List.map ms args) m = Some b ->
  agree ms sp rs ->
  Mem.extends m m' ->
  exists rs', exists insn,
     exec_straight_opt ge fn c rs m' (insn :: k) rs' m'
  /\ exec_instr ge fn insn rs' m' = exec_branch fn lbl rs' m' (Some b)
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros until m'; intros TRANSL EVAL AG MEXT.
  set (vl' := map rs (map preg_of args)).
  assert (EVAL': eval_condition cond vl' m' = Some b).
  { apply eval_condition_lessdef with (map ms args) m; auto. eapply preg_vals; eauto. }
  clear EVAL MEXT AG.
  destruct cond; simpl in TRANSL; ArgsInv.
  - exists rs, (transl_cbranch_signed c0 x (inl x0) lbl).
    intuition auto. constructor. apply transl_cbranch_signed_correct; auto.
  - exists rs, (transl_cbranch_unsigned c0 x (inl x0) lbl).
    intuition auto. constructor. apply transl_cbranch_unsigned_correct; auto.
  - exists rs, (transl_cbranch_signed c0 x (inr n) lbl).
    intuition auto. constructor. apply transl_cbranch_signed_correct; auto.
  - exists rs, (transl_cbranch_unsigned c0 x (inr n) lbl).
    intuition auto. constructor. apply transl_cbranch_unsigned_correct; auto.
Qed.

Lemma transl_cbranch_correct_true:
  forall cond args lbl k c m ms sp rs m',
  transl_cbranch cond args lbl k = OK c ->
  eval_condition cond (List.map ms args) m = Some true ->
  agree ms sp rs ->
  Mem.extends m m' ->
  exists rs', exists insn,
     exec_straight_opt ge fn c rs m' (insn :: k) rs' m'
  /\ exec_instr ge fn insn rs' m' = goto_label fn lbl rs' m'
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros. eapply transl_cbranch_correct_1 with (b := true); eauto.
Qed.

Lemma transl_cbranch_correct_false:
  forall cond args lbl k c m ms sp rs m',
  transl_cbranch cond args lbl k = OK c ->
  eval_condition cond (List.map ms args) m = Some false ->
  agree ms sp rs ->
  Mem.extends m m' ->
  exists rs',
     exec_straight ge fn c rs m' k rs' m'
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros. exploit transl_cbranch_correct_1; eauto. simpl.
  intros (rs' & insn & A & B & C).
  exists (nextinstr rs').
  split. eapply exec_straight_opt_right; eauto. apply exec_straight_one; auto.
  intros; Simpl.
Qed.


(** Translation of condition operators *)

Ltac TranslCondSimpl :=
  econstructor; split;
  [ apply exec_straight_one; [ simpl; eauto; try reflexivity | reflexivity ]
  | split; intros; Simpl ].

Lemma transl_cond_signed_correct:
  forall cmp r1 r2 k rs m,
  exists rs',
     exec_straight ge fn (transl_cond_signed cmp r1 r2 :: k) rs m k rs' m
  /\ Val.lessdef (Val.cmp cmp rs#r1 (eval_reg_imm rs r2)) rs'#r1
  /\ forall r, r <> PC -> r <> r1 -> rs'#r = rs#r.
Proof.
  intros. destruct cmp; simpl; TranslCondSimpl.
  unfold eval_cmp; destruct (rs#r1); auto; destruct (eval_reg_imm rs r2); auto.
  unfold eval_cmp; destruct (rs#r1); auto; destruct (eval_reg_imm rs r2); auto.
Qed.

Lemma transl_cond_unsigned_correct:
  forall cmp r1 r2 k rs m,
  exists rs',
     exec_straight ge fn (transl_cond_unsigned cmp r1 r2 :: k) rs m k rs' m
  /\ Val.lessdef (Val.cmpu (Mem.valid_pointer m) cmp rs#r1 (eval_reg_imm rs r2)) rs'#r1
  /\ forall r, r <> PC -> r <> r1 -> rs'#r = rs#r.
Proof.
  intros. destruct cmp; simpl; TranslCondSimpl.
Qed.

Lemma transl_cond_op_correct:
  forall cond rd args k c rs m,
  transl_cond_op cond rd args k = OK c ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef (Val.of_optbool (eval_condition cond (map rs (map preg_of args)) m)) rs'#(preg_of rd)
  /\ forall r, r <> PC -> r <> (preg_of rd) -> rs'#r = rs#r.
Proof.
  assert (MKTOT: forall ob, Val.of_optbool ob = Val.maketotal (option_map Val.of_bool ob)).
  { destruct ob as [[]|]; reflexivity. }
  intros until m; intros TR.
  destruct cond; simpl in TR; ArgsInv.
  - (* cmp *)
    exploit transl_cond_signed_correct; eauto.
    intros (rs' & A & B & C). exists rs'; eauto.
  - (* cmpu *)
    exploit transl_cond_unsigned_correct; eauto.
    intros (rs' & A & B & C). exists rs'; eauto.
  - (* cmpimm *)
    exploit transl_cond_signed_correct; eauto.
    intros (rs' & A & B & C). exists rs'; eauto.
  - (* cmpuimm *)
    exploit transl_cond_unsigned_correct; eauto.
    intros (rs' & A & B & C). exists rs'; eauto.
Qed.


(* Translation of arithmetic operations *)

Ltac SimplEval H :=
  match type of H with
  | Some _ = None _ => discriminate
  | Some _ = Some _ => inv H
  | ?a = Some ?b => let A := fresh in assert (A: Val.maketotal a = b) by (rewrite H; reflexivity)
end.

Ltac TranslOpSimpl :=
  econstructor; split;
  [ apply exec_straight_one; [ simpl; eauto; try reflexivity | reflexivity ]
  | split; [ apply Val.lessdef_same; Simpl; fail | intros; Simpl; fail ] ].

Ltac TranslALUOpSimpl EV :=
  econstructor; split;
  [ apply exec_straight_one; [ unfold exec_instr, exec_alu; simpl; rewrite EV; try reflexivity | reflexivity]
  | split; [ apply Val.lessdef_same; Simpl; fail | intros; Simpl; fail ] ].


Lemma transl_op_correct:
  forall op args res k (rs: regset) m v c,
  transl_op op args res k = OK c ->
  eval_operation ge (rs#SP) op (map rs (map preg_of args)) m = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef v rs'#(preg_of res)
  /\ forall r, data_preg r = true -> r <> preg_of res -> preg_notin r (destroyed_by_op op) -> rs' r = rs r.
Proof.
  assert (SAME: forall v1 v2, v1 = v2 -> Val.lessdef v2 v1). { intros; subst; auto. }
Opaque Int.eq.
  intros until c; intros TR EV.
  unfold transl_op in TR; destruct op; ArgsInv; simpl in EV; SimplEval EV; try TranslOpSimpl.

- (* addrstack *)
  exploit addptrofs_correct; intros (rs' & A & B & C).
  exists rs'; split; [ exact A | auto with asmgen ].

- (* neg *)
  econstructor; split.
  apply exec_straight_one; reflexivity.
  split.
  + apply Val.lessdef_same; Simpl.
    unfold Val.neg, Val.mul, eval_reg_imm.
    destruct (rs x); try reflexivity.
    f_equal; symmetry; apply Int.mul_mone.
  + intros; Simpl.

  (* divu, divuimm, modu, moduimm *)
- TranslALUOpSimpl EV.
- TranslALUOpSimpl EV.
- TranslALUOpSimpl EV.
- TranslALUOpSimpl EV.

- (* cond *)
  exploit transl_cond_op_correct; eauto. intros (rs' & A & B & C).
  exists rs'; split. eexact A. eauto with asmgen.
Qed.

Lemma stack_load_correct:
  forall ofs ty dst k c (rs: regset) m v,
  stack_load ofs ty dst k = OK c ->
  Mem.loadv (chunk_of_type ty) m (Val.offset_ptr rs#SP ofs) = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, r <> PC -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  intros until v. intros LOAD TR.
  unfold stack_load in LOAD; ArgsInv.
  econstructor. split.
  - apply exec_straight_one. simpl; unfold exec_load.
    + assert (H: Mem.loadv (size_to_memory_chunk x0) m (Val.offset_ptr (rs R10) ofs) = Some v). {
        unfold chunk_of_type in TR.
        unfold size_to_memory_chunk.
        destruct ty, x0; try discriminate; auto.
      }
      rewrite H.
      reflexivity.
    + Simpl.
  - split; intros; Simpl.
Qed.

Lemma stack_store_correct:
  forall ofs ty src k c (rs: regset) m m',
  stack_store ofs ty src k = OK c ->
  Mem.storev (chunk_of_type ty) m (Val.offset_ptr rs#SP ofs) rs#(preg_of src) = Some m' ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros until m'. intros STORE TR.
  unfold stack_store in STORE; ArgsInv.
  econstructor. split.
  - apply exec_straight_one. simpl; unfold exec_store.
    + assert (H: Mem.storev (size_to_memory_chunk x0) m (Val.offset_ptr (rs R10) ofs) (rs x) = Some m'). {
        unfold chunk_of_type in TR.
        unfold size_to_memory_chunk.
        destruct ty, x0; try discriminate; auto.
      }
      simpl.
      rewrite H.
      reflexivity.
    + Simpl.
  - intros; Simpl.
Qed.

Lemma transl_load_common_correct:
  forall chunk k i op (x x0: ireg) (rs: regset) m a v,
  Val.offset_ptr (rs x0) i = a ->
  Mem.loadv chunk m a = Some v ->
  transl_memory_access chunk = OK op ->
  exists rs',
     exec_straight ge fn (Pload op x x0 i :: k) rs m k rs' m
  /\ rs'#x = v
  /\ forall r, r <> PC -> r <> x -> rs'#r = rs#r.
Proof.
  intros until v. intros EV LOAD TR.
  econstructor. split.
  - apply exec_straight_one; simpl; unfold exec_load.
    + assert (H: Mem.loadv (size_to_memory_chunk op) m a = Some v). {
        unfold transl_memory_access in TR.
        destruct chunk, op; try discriminate; auto.
      }
      rewrite EV, H.
      reflexivity.
    + Simpl.
  - split; intros; Simpl.
Qed.

Lemma transl_load_correct:
  forall chunk addr args dst k c (rs: regset) m a v,
  transl_load chunk addr args dst k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some a ->
  Mem.loadv chunk m a = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, r <> PC -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  intros until v; intros TR EV LOAD.
  destruct addr, args; simpl in TR; ArgsInv.
  - unfold transl_memory_access in EQ0.
    inversion EV.
    destruct chunk; try discriminate; eapply transl_load_common_correct; eauto.

  - unfold transl_memory_access in EQ1.
    inversion EV.
    destruct chunk; try discriminate; eapply transl_load_common_correct; eauto.
Qed.

Lemma transl_store_common_correct:
  forall chunk k i op (x x0: ireg) (rs: regset) m m' a,
  Val.offset_ptr (rs x0) i = a ->
  Mem.storev chunk m a (rs x) = Some m' ->
  transl_memory_access chunk = OK op ->
  exists rs',
     exec_straight ge fn (Pstore op x0 (inl x) i :: k) rs m k rs' m'
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros until a. intros EV STORE TR.
  econstructor. split.
  - apply exec_straight_one; simpl; unfold exec_store.
    + assert (H: Mem.storev (size_to_memory_chunk op) m a (rs x) = Some m'). {
        unfold transl_memory_access in TR.
        destruct chunk, op; try discriminate; auto.
      }
      simpl.
      rewrite EV, H.
      reflexivity.
    + Simpl.
  - intros; Simpl.
Qed.

Lemma transl_store_correct:
  forall chunk addr args src k c (rs: regset) m a m',
  transl_store chunk addr args src k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some a ->
  Mem.storev chunk m a rs#(preg_of src) = Some m' ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros until m'; intros TR EV STORE.
  destruct addr, args; simpl in TR; ArgsInv.
  - unfold transl_memory_access in EQ0.
    inversion EV.
    destruct chunk; try discriminate; eapply transl_store_common_correct; eauto.

  - unfold transl_memory_access in EQ1.
    inversion EV.
    destruct chunk; try discriminate; eapply transl_store_common_correct; eauto.
Qed.

End CONSTRUCTORS.
