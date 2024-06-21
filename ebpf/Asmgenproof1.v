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
Require Import Events Smallstep.
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
  forall rd r1 n k k' rs m,
    addptrofs rd r1 n k = OK k' ->
  exists rs',
     exec_straight ge fn k' rs m k rs' m
  /\ Val.lessdef (Val.offset_ptr rs#r1 n) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold addptrofs; intros.
  destruct Archi.ptr64 eqn:A; try discriminate.
  - (* Archi.ptr64 = false *)
    inv H.
    destruct (Ptrofs.eq_dec n Ptrofs.zero).
    + subst n. econstructor; split.
      apply exec_straight_one. simpl; constructor. auto.
      split. Simpl. simpl. destruct (rs r1); simpl; auto. rewrite Ptrofs.add_zero; auto.
      intros; Simpl.
    + eexists; split.
      eapply exec_straight_two; reflexivity.
      split; intros; Simpl.
      simpl.
      unfold Val.add, Val.offset_ptr.
      destruct (rs r1); try constructor.
      rewrite A.
      apply Val.lessdef_same; f_equal; f_equal.
      rewrite Ptrofs.of_int_to_int by auto.
      reflexivity.
Qed.

(** Translation of conditional branches *)

Lemma cmp_cmpu_Ceq : forall v1 v2 f b,
    Val.cmp_bool Ceq v1 v2  = Some b ->
    Val.cmpu_bool f Ceq v1 v2 = Some b.
Proof.
  intros.
  unfold Val.cmp_bool in H.
  destruct v1 ; try discriminate H.
  destruct v2 ; try discriminate H.
  apply H.
Qed.

Lemma cmp_cmpu_Cne : forall v1 v2 f b,
    Val.cmp_bool Cne v1 v2  = Some b ->
    Val.cmpu_bool f Cne v1 v2 = Some b.
Proof.
  intros.
  unfold Val.cmp_bool in H.
  destruct v1 ; try discriminate H.
  destruct v2 ; try discriminate H.
  apply H.
Qed.


Lemma transl_comparison_signed_correct:
  forall cmp w r1 r2  (rs: regset) m b,
  Val.cmp_bool cmp rs#(IR r1) (eval_reg_immw w rs r2) = Some b ->
  eval_cmp (transl_comparison cmp Ctypes.Signed) w rs m r1 r2 = Some b.
Proof.
  intros.
  unfold transl_comparison.
  destruct cmp ; simpl; auto.
  - apply cmp_cmpu_Ceq; auto.
  - apply cmp_cmpu_Cne; auto.
Qed.

Lemma transl_comparison_unsigned_correct:
  forall cmp w r1 r2  (rs: regset) m b,
  Val.cmpu_bool (Mem.valid_pointer m) cmp rs#(IR r1) (eval_reg_immw w rs r2) = Some b ->
  eval_cmp (transl_comparison cmp Ctypes.Unsigned) w rs m r1 r2 = Some b.
Proof.
  intros.
  unfold transl_comparison.
  destruct cmp ; simpl; auto.
Qed.

Lemma transl_cbranch_signed_correct:
  forall cmp w r1 r2 lbl (rs: regset) m b,
  Val.cmp_bool cmp rs#(IR r1) (eval_reg_immw w rs r2) = Some b ->
  exec_instr ge fn (transl_cbranch_signed cmp w r1 r2 lbl) rs m =
  exec_branch fn lbl rs m (Some b).
Proof.
  intros.
  unfold transl_cbranch_signed.
  simpl.
  apply transl_comparison_signed_correct with (m:=m) in H.
  rewrite H. reflexivity.
Qed.

Lemma transl_cbranch_unsigned_correct:
  forall cmp w r1 r2 lbl (rs: regset) m b,
  Val.cmpu_bool (Mem.valid_pointer m) cmp rs#(IR r1) (eval_reg_immw w rs r2) = Some b ->
  exec_instr ge fn (transl_cbranch_unsigned cmp w r1 r2 lbl) rs m =
  exec_branch fn lbl rs m (Some b).
Proof.
  intros.
  unfold transl_cbranch_unsigned.
  simpl.
  apply transl_comparison_unsigned_correct with (m:=m) in H.
  rewrite H. reflexivity.
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
  - exists rs, (transl_cbranch_signed c0 W32 x (inl x0) lbl).
    intuition auto. constructor. apply transl_cbranch_signed_correct; auto.
  - exists rs, (transl_cbranch_unsigned c0 W32 x (inl x0) lbl).
    intuition auto. constructor. apply transl_cbranch_unsigned_correct; auto.
  - exists rs, (transl_cbranch_signed c0 W32 x (inr (Imm32 n)) lbl).
    intuition auto. constructor. apply transl_cbranch_signed_correct; auto.
  - exists rs, (transl_cbranch_unsigned c0 W32 x (inr (Imm32 n)) lbl).
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
  forall cmp w r1 r2 k rs m,
  exists rs',
     exec_straight ge fn (transl_cond_as_Pcmp cmp w Ctypes.Signed r1 r2  k) rs m k rs' m
  /\ Val.lessdef (Val.cmp cmp rs#r1 (eval_reg_immw w rs r2)) rs'#r1
  /\ forall r, r <> PC -> r <> r1 -> rs'#r = rs#r.
Proof.
  intros.
  unfold transl_cond_as_Pcmp.
  destruct cmp; simpl; TranslCondSimpl.
  unfold eval_cmp; destruct (rs#r1); auto; destruct (eval_reg_immw w rs r2); auto.
  unfold eval_cmp; destruct (rs#r1); auto; destruct (eval_reg_immw w rs r2); auto.
Qed.

Lemma transl_cond_unsigned_correct:
  forall cmp w r1 r2 k rs m,
  exists rs',
     exec_straight ge fn (transl_cond_as_Pcmp cmp w Ctypes.Unsigned r1 r2 k) rs m k rs' m
  /\ Val.lessdef (Val.cmpu (Mem.valid_pointer m) cmp rs#r1 (eval_reg_immw w rs r2)) rs'#r1
  /\ forall r, r <> PC -> r <> r1 -> rs'#r = rs#r.
Proof.
  intros. destruct cmp; simpl; TranslCondSimpl.
Qed.

Lemma transl_cond_as_jump_correct:
  forall cmp w r1 r2 k rs m,
  exists rs',
     exec_straight ge fn (transl_cond_as_Pcmp cmp w Ctypes.Signed r1 r2 k) rs m k rs' m
  /\ Val.lessdef (Val.cmp cmp rs#r1 (eval_reg_immw w rs r2)) rs'#r1
  /\ forall r, r <> PC -> r <> r1 -> rs'#r = rs#r.
Proof.
  intros.
  unfold transl_cond_as_Pcmp.
  destruct cmp; simpl; TranslCondSimpl.
  unfold eval_cmp; destruct (rs#r1); auto; destruct (eval_reg_immw w rs r2); auto.
  unfold eval_cmp; destruct (rs#r1); auto; destruct (eval_reg_immw w rs r2); auto.
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

Lemma sign_ext_8 : forall x rs k  m,
  exists rs' : regset,
    exec_straight ge fn (Palu LSH W32 x (inr (Imm32 (Int.repr 24))) :: Palu ARSH W32 x (inr (Imm32 (Int.repr 24))) :: k) rs m k rs' m /\
      Val.sign_ext 8 (rs x) = (rs' x) /\
      (forall r : preg, r <> PC -> r <> x  -> rs' r = rs r).
Proof.
  intros.
  eexists.  split;[|split].
  - eapply exec_straight_two; reflexivity.
  - Simpl.
    unfold eval_reg_immw.
    destruct (rs x) ; simpl; auto.
    change (Int.ltu (Int.repr 24) Int.iwordsize) with true.
    simpl. change (Int.ltu (Int.repr 24) Int.iwordsize) with true.
    simpl. rewrite Int.sign_ext_shr_shl. reflexivity.
    change Int.zwordsize with 32. lia.
  - intros. Simpl.
Qed.

Lemma sign_ext_16 : forall x rs k  m,
  exists rs' : regset,
    exec_straight ge fn (Palu LSH W32 x (inr (Imm32 (Int.repr 16))) :: Palu ARSH W32 x (inr (Imm32 (Int.repr 16))) :: k) rs m k rs' m /\
      (Val.sign_ext 16 (rs x)) =  (rs' x) /\
      (forall r : preg, r <> PC -> r <> x  -> rs' r = rs r).
Proof.
  intros.
  eexists.  split;[|split].
  - eapply exec_straight_two; reflexivity.
  - Simpl.
    unfold eval_reg_immw.
    destruct (rs x) ; simpl; auto.
    change (Int.ltu (Int.repr 16) Int.iwordsize) with true.
    simpl. change (Int.ltu (Int.repr 16) Int.iwordsize) with true.
    simpl. rewrite Int.sign_ext_shr_shl. reflexivity.
    change Int.zwordsize with 32. lia.
  - intros. Simpl.
Qed.


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
  - (* Olongconst *)
    destruct (negb (Int64.ltu (Int64.repr Int.max_unsigned) n)); try discriminate.
    inv EQ0.
    econstructor; split.
    apply exec_straight_one; reflexivity.
    split.
    + apply Val.lessdef_same; Simpl.
    + intros.
      Simpl.
  - (* addrstack *)
    exploit addptrofs_correct; eauto.
    intros (rs' & A & B & C).
    exists rs'; split; [ exact A | auto with asmgen ].
- (* neg *)
  econstructor; split.
  apply exec_straight_one; reflexivity.
  split.
  + apply Val.lessdef_same; Simpl.
    unfold Val.neg, Val.mul, eval_reg_immw.
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
- (* sign_ext 8 *)
  exploit sign_ext_8.
  intros (rs' & EXEC & LD & RS).
  eexists. split;[eauto|split]; eauto.
  intros. apply RS; auto. intro. subst. discriminate.
- (* sign_ext 16 *)
  exploit sign_ext_16.
  intros (rs' & EXEC & LD & RS).
  eexists. split;[eauto|split]; eauto.
  intros. apply RS; auto. intro. subst. discriminate.
Qed.

Lemma loadind_correct:
  forall base ofs ty dst k c (rs: regset) m v,
    loadind base ofs ty dst k = OK c ->
  Mem.loadv (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, r <> PC -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  intros until v. intros LOAD TR.
  unfold loadind in LOAD; ArgsInv.
  econstructor. split.
  - apply exec_straight_one. simpl; unfold exec_load.
    +
      unfold load, transl_typ in *.
      destruct Archi.ptr64 eqn:A.
      *
        destruct ty; simpl in *; inv EQ1;
        rewrite TR; reflexivity.
      *  destruct ty; simpl in *; inv EQ1;
        rewrite TR; reflexivity.
    + Simpl.
  - split; intros; Simpl.
Qed.

Lemma storeind_correct:
  forall (base: ireg) ofs ty src k c (rs: regset) m m',
  storeind base ofs ty src k = OK c ->
  Mem.storev (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) rs#(preg_of src) = Some m' ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros until m'; intros TR STORE.
  unfold storeind in TR. ArgsInv.
  econstructor.
  split.
  - apply exec_straight_one. simpl; unfold exec_store.
    + unfold store, transl_typ in *.
      destruct Archi.ptr64 eqn:A.
      *
        destruct ty; simpl in *; inv EQ1;
        rewrite STORE; reflexivity.
      *  destruct ty; simpl in *; inv EQ1;
        rewrite STORE; reflexivity.
    + Simpl.
  - intros; Simpl.
Qed.

Lemma loadind_ptr_correct:
  forall (base: ireg) ofs (dst: ireg) k (rs: regset) m v,
  Mem.loadv Mptr m (Val.offset_ptr rs#base ofs) = Some v ->
  exists rs',
     exec_straight ge fn (loadind_ptr base ofs dst k) rs m k rs' m
  /\ rs'#dst = v
  /\ forall r, r <> PC -> r <> dst -> rs'#r = rs#r.
Proof.
  intros until v. intros LOAD.
  unfold loadind_ptr, Mptr in *.
  econstructor. split.
  apply exec_straight_one. simpl. unfold exec_load,load.
  destruct Archi.ptr64; rewrite LOAD;reflexivity.
  Simpl.
  split; intros; Simpl.
Qed.



Lemma stack_store_correct:
  forall base ofs ty src k c (rs: regset) m m',
  storeind base ofs ty src k = OK c ->
  Mem.storev (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) rs#(preg_of src) = Some m' ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros until m'. intros STORE TR.
  unfold storeind in STORE; ArgsInv.
  econstructor. split.
  - apply exec_straight_one. simpl; unfold exec_store.
    + unfold store, transl_typ in *.
      destruct Archi.ptr64 eqn:A.
      *
        destruct ty; simpl in *; inv EQ1;
        rewrite TR; reflexivity.
      *  destruct ty; simpl in *; inv EQ1;
        rewrite TR; reflexivity.
    + Simpl.
  - intros; Simpl.
Qed.

Lemma transl_load_indexed_correct:
  forall chunk k i  (x x0: ireg) (rs: regset) m a v kl,
  Val.offset_ptr (rs x0) i = a ->
  Mem.loadv chunk m a = Some v ->
  transl_load_indexed chunk x x0 i k = OK kl ->
  exists rs',
     exec_straight ge fn kl rs m k rs' m
  /\ Val.lessdef v (rs'#x)
  /\ forall r, r <> PC -> r <> x -> rs'#r = rs#r.
Proof.
  intros until v. intros KL EV LOAD TR.
  unfold transl_load_indexed in TR.
  destruct a; try discriminate.
  unfold Mem.loadv in LOAD.
  destruct chunk.
  + (* Mbool *)
    inv TR.
    rewrite Mem.load_bool_int8_unsigned in LOAD.
    destruct (Mem.load Mint8unsigned m b (Ptrofs.unsigned i0))eqn:ML; try discriminate.
    simpl in LOAD. inv LOAD.
    eexists ; split ; eauto.
    eapply exec_straight_one; simpl; unfold exec_load,load; try reflexivity.
    unfold Mem.loadv. rewrite EV. rewrite ML.
    reflexivity.
    reflexivity.
    split. Simpl.
    apply Val.norm_bool_is_lessdef.
    intros. Simpl.
  + (* Mint8signed *)
    inv TR.
    rewrite Mem.load_int8_signed_unsigned in LOAD.
    destruct (Mem.load Mint8unsigned m b (Ptrofs.unsigned i0))eqn:ML; try discriminate.
    simpl in LOAD. inv LOAD.
    exploit sign_ext_8. intros (rs' & EXEC & LD & RS).
    eexists ; split ; eauto.
    eapply exec_straight_step; simpl; unfold exec_load,load; try reflexivity.
    unfold Mem.loadv. rewrite EV. rewrite ML.
    reflexivity.
    reflexivity. eauto.
    split. rewrite <- LD. Simpl.
    intros. rewrite RS by auto. Simpl.
  + (* Mint8unsigned *)
    inv TR.
    econstructor. split.
    eapply exec_straight_one; simpl; unfold exec_load,load; try reflexivity.
    unfold Mem.loadv. rewrite EV. rewrite LOAD.
    reflexivity.
    reflexivity.
    split.
    * Simpl.
    * intros.
      Simpl.
  + (* Mint16signed *)
    inv TR.
    rewrite Mem.load_int16_signed_unsigned in LOAD.
    destruct (Mem.load Mint16unsigned m b (Ptrofs.unsigned i0))eqn:ML; try discriminate.
    simpl in LOAD. inv LOAD.
    exploit sign_ext_16. intros (rs' & EXEC & LD & RS).
    eexists ; split ; eauto.
    eapply exec_straight_step; simpl; unfold exec_load,load; try reflexivity.
    unfold Mem.loadv. rewrite EV. rewrite ML.
    reflexivity.
    reflexivity. eauto.
    split. rewrite <- LD. Simpl.
    intros. rewrite RS by auto. Simpl.
  + (* Mint16unsigned *)
    inv TR.
    econstructor. split.
    eapply exec_straight_one; simpl; unfold exec_load,load; try reflexivity.
    unfold Mem.loadv. rewrite EV. rewrite LOAD.
    reflexivity.
    reflexivity.
    split.
    * Simpl.
    * intros.
      Simpl.
  + (* Mint32 *)
    inv TR.
    econstructor. split.
    eapply exec_straight_one; simpl; unfold exec_load,load; try reflexivity.
    unfold Mem.loadv. rewrite EV. rewrite LOAD.
    reflexivity.
    reflexivity.
    split.
    * Simpl.
    * intros.
      Simpl.
  + destruct Archi.ptr64 eqn:A;[| discriminate].
    (* Mint64 *)
    inv TR.
    econstructor. split.
    eapply exec_straight_one; simpl; unfold exec_load,load; try reflexivity.
    unfold Mem.loadv. rewrite EV. rewrite LOAD. rewrite A.
    reflexivity.
    reflexivity.
    split.
    * Simpl.
    * intros.
      Simpl.
  + (* Mfloat32 *) discriminate.
  + (* Mfloat64 *) discriminate.
  + (* Many32 *)
    inv TR.
    econstructor. split.
    eapply exec_straight_one; simpl; unfold exec_load,load; try reflexivity.
    unfold Mem.loadv. rewrite EV. rewrite LOAD.
    reflexivity.
    reflexivity.
    split.
    * Simpl.
    * intros.
      Simpl.
  + (* Many64 *)
    destruct Archi.ptr64 eqn:A;[|discriminate].
    inv TR.
    econstructor. split.
    eapply exec_straight_one; simpl; unfold exec_load,load; try reflexivity.
    unfold Mem.loadv. rewrite EV. rewrite A.  rewrite LOAD.
    reflexivity.
    reflexivity.
    split.
    * Simpl.
    * intros.
      Simpl.
Qed.

Lemma transl_load_correct:
  forall chunk addr args dst k c (rs: regset) m a v,
  transl_load chunk addr args dst k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some a ->
  Mem.loadv chunk m a = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef v (rs'#(preg_of dst))
  /\ forall r, r <> PC -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  intros until v; intros TR EV LOAD.
  destruct addr, args; simpl in TR; ArgsInv.
  - exploit transl_load_indexed_correct; eauto.
    congruence.
  - exploit transl_load_indexed_correct; eauto.
    congruence.
Qed.

Lemma transl_store_common_correct:
  forall chunk k i k' (x x0: ireg) (rs: regset) m m' a,
  Val.offset_ptr (rs x0) i = a ->
  Mem.storev chunk m a (rs x) = Some m' ->
  transl_store_indexed chunk x0 i x k = OK k' ->
  exists rs',
     exec_straight ge fn k' rs m k rs' m'
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros until a. intros EV STORE TR.
  destruct chunk; simpl in TR.
  - (* Mbool *)
  inv TR.
    econstructor. split.
    apply exec_straight_one; simpl; unfold exec_store,store.
    destruct (Val.offset_ptr (rs x0) i); try discriminate.
    simpl in STORE.
    rewrite Mem.store_bool_unsigned_8 in STORE.
    simpl.
    rewrite STORE. reflexivity.
    reflexivity.
    intros. Simplif.
  - (* Mint8signed *)
    inv TR.
    econstructor. split.
    apply exec_straight_one; simpl; unfold exec_store,store.
    destruct (Val.offset_ptr (rs x0) i); try discriminate.
    simpl in STORE.
    rewrite Mem.store_signed_unsigned_8 in STORE.
    simpl.
    rewrite STORE. reflexivity.
    reflexivity.
    intros. Simplif.
  - (* Mint8unsigned *)
    inv TR.
    econstructor. split.
    apply exec_straight_one; simpl; unfold exec_store,store,eval_reg_immw.
    rewrite STORE. reflexivity.
    reflexivity.
    intros. Simplif.
  - (* Mint16signed *)
    inv TR.
    econstructor. split.
    apply exec_straight_one; simpl; unfold exec_store,store.
    destruct (Val.offset_ptr (rs x0) i); try discriminate.
    simpl in STORE.
    rewrite Mem.store_signed_unsigned_16 in STORE.
    simpl.
    rewrite STORE. reflexivity.
    reflexivity.
    intros. Simplif.
  -
    inv TR.
    econstructor. split.
    apply exec_straight_one; simpl; unfold exec_store,store,eval_reg_immw.
    rewrite STORE. reflexivity.
    reflexivity.
    intros. Simplif.
  -     inv TR.
    econstructor. split.
    apply exec_straight_one; simpl; unfold exec_store,store,eval_reg_immw.
    rewrite STORE. reflexivity.
    reflexivity.
    intros. Simplif.
  -
    destruct Archi.ptr64 eqn:ARCHI;[|discriminate].
    inv TR.
    econstructor. split.
    apply exec_straight_one; simpl; unfold exec_store,store,eval_reg_immw.
    rewrite ARCHI.
    rewrite STORE. reflexivity.
    reflexivity.
    intros. Simplif.
  - discriminate.
  - discriminate.
  -
    inv TR.
    econstructor. split.
    apply exec_straight_one; simpl; unfold exec_store,store,eval_reg_immw.
    rewrite STORE. reflexivity.
    reflexivity.
    intros. Simplif.
  -
    destruct Archi.ptr64 eqn:ARCHI; [|discriminate].
    inv TR.
    econstructor. split.
    apply exec_straight_one; simpl; unfold exec_store,store,eval_reg_immw.
    rewrite STORE. rewrite ARCHI. reflexivity.
    reflexivity.
    intros. Simplif.
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
  - exploit transl_store_common_correct;eauto.
    congruence.
  - exploit transl_store_common_correct;eauto.
    congruence.
Qed.

End CONSTRUCTORS.
