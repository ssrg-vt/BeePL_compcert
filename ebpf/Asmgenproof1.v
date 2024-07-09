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

Lemma get_int_inv : forall n x, get_int n = OK x -> (Int.repr (Int64.unsigned n)) =  x /\ Int.unsigned x = Int64.unsigned n.
Proof.
  unfold get_int. intros.
  destruct (Int64.unsigned n <=? Int.max_unsigned) eqn:LE; try discriminate.
  inv H. split; auto.
  rewrite Int.unsigned_repr; auto.
  apply Zle_bool_imp_le in LE.
  generalize (Int64.unsigned_range_2 n). lia.
Qed.

Global Hint Resolve ireg_of_not_R10 ireg_of_not_R10': asmgen.

(** Useful simplification tactic *)

Ltac get_int_inv :=
  match goal with
  | H : get_int ?N = ?X |- _ => apply get_int_inv in H ; destruct H;subst
  end.

Ltac Simplif :=
  ((rewrite nextinstr_inv by eauto with asmgen)
  || (rewrite nextinstr_inv1 by eauto with asmgen)
  || (rewrite Pregmap.gss)
  || (rewrite nextinstr_pc)
  ||  get_int_inv
  || (rewrite Pregmap.gso by eauto with asmgen)); auto with asmgen.

Ltac Simpl := repeat Simplif.

(** * Correctness of eBPF constructor functions *)

Section CONSTRUCTORS.

Variable ge: genv.
Variable fn: function.

(** Add offset to pointer *)

Lemma lessdef_offset_ptr_add :
  forall v n
         (ARCH : Archi.ptr64 = false),
    Val.lessdef (Val.offset_ptr v n)
      (Val.add v (Vint (Ptrofs.to_int n))).
Proof.
  unfold Val.offset_ptr.
  destruct v; auto.
  simpl. intros. rewrite ARCH.
  replace (Ptrofs.of_int (Ptrofs.to_int n)) with n;auto.
  unfold Ptrofs.of_int,Ptrofs.to_int.
  rewrite Int.unsigned_repr.
  rewrite Ptrofs.repr_unsigned;auto.
  generalize (Ptrofs.unsigned_range_2 n).
  unfold Ptrofs.max_unsigned.
  rewrite Ptrofs.modulus_eq32 by auto.
  unfold Int.max_unsigned. lia.
Qed.

Lemma lessdef_offset_ptr_addl :
  forall v n
         (BND: ptrofs_is_int n = true)
         (ARCH : Archi.ptr64 = true),
    Val.lessdef (Val.offset_ptr v n)
      (Val.addl v (Vlong (int64_of_intu (Ptrofs.to_int n)))).
Proof.
  unfold Val.offset_ptr.
  destruct v; auto.
  simpl. intros. rewrite ARCH.
  replace ((Ptrofs.of_int64 (int64_of_intu (Ptrofs.to_int n)))) with n;auto.
  unfold ptrofs_is_int in BND.
  rewrite ARCH in BND. simpl in BND.
  apply  Zle_bool_imp_le in BND.
  unfold int64_of_intu,Ptrofs.of_int,Ptrofs.to_int.
  pose proof (Ptrofs.unsigned_range_2 n) as R.
  rewrite Int.unsigned_repr by lia.
  unfold Ptrofs.of_int64.
  apply Ptrofs.agree64_repr with (i:=(Ptrofs.unsigned n)) in ARCH.
  unfold Ptrofs.agree64 in ARCH. rewrite <- ARCH.
  rewrite! Ptrofs.repr_unsigned;auto.
Qed.



Lemma addptrofs_correct:
  forall rd r1 n k k' rs m,
    addptrofs rd r1 n k = OK k' ->
  exists rs',
     exec_straight ge fn k' rs m k rs' m
  /\ Val.lessdef (Val.offset_ptr rs#r1 n) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold addptrofs; intros.
  destruct (Ptrofs.eq_dec n Ptrofs.zero).
  + subst n. inv H. econstructor; split.
    apply exec_straight_one. simpl; constructor. auto.
    split. Simpl. simpl. destruct (rs r1); simpl; auto. rewrite Ptrofs.add_zero; auto.
    intros; Simpl.
  +
    destruct (ptrofs_is_int n) eqn:C; try discriminate.
    inv H.
    eexists; split.
    eapply exec_straight_two; reflexivity.
    split.
    * Simpl.
      destruct warchi eqn:WARCH.
      { simpl.
        unfold ptrofs_is_int in C.
        unfold warchi in WARCH. destruct Archi.ptr64 eqn:ARCH ; try discriminate.
        simpl in WARCH.
        apply lessdef_offset_ptr_add; auto.
      }
      { simpl.
        apply lessdef_offset_ptr_addl; auto.
        unfold warchi in WARCH.
        destruct Archi.ptr64 eqn:A;try discriminate. auto.
      }
    * intros; Simpl.
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


Lemma cmp_cmplu_Ceq : forall v1 v2 f b,
    Val.cmpl_bool Ceq v1 v2  = Some b ->
    Val.cmplu_bool f Ceq v1 v2 = Some b.
Proof.
  intros.
  unfold Val.cmpl_bool in H.
  destruct v1 ; try discriminate H.
  destruct v2 ; try discriminate H.
  apply H.
Qed.


Lemma cmp_cmplu_Cne : forall v1 v2 f b,
    Val.cmpl_bool Cne v1 v2  = Some b ->
    Val.cmplu_bool f Cne v1 v2 = Some b.
Proof.
  intros.
  unfold Val.cmpl_bool in H.
  destruct v1 ; try discriminate H.
  destruct v2 ; try discriminate H.
  apply H.
Qed.

Lemma transl_comparison_signed_correct:
  forall c (w:width)  r1 r2  (rs: regset) m b,
    (cmp w)  c rs#(IR r1) (eval_reg_immw w rs r2) = Some b ->
  eval_cmp (transl_comparison c Ctypes.Signed) w rs m r1 r2 = Some b.
Proof.
  intros.
  unfold transl_comparison.
  unfold cmp in H.
  destruct w; destruct c;simpl;auto.
  - apply cmp_cmpu_Ceq; auto.
  - apply cmp_cmpu_Cne; auto.
  - apply cmp_cmplu_Ceq; auto.
  - apply cmp_cmplu_Cne; auto.
Qed.

Lemma transl_comparison_unsigned_correct:
  forall c w r1 r2  (rs: regset) m b,
    (cmpu w) (Mem.valid_pointer m) c rs#(IR r1) (eval_reg_immw w rs r2) = Some b ->
  eval_cmp (transl_comparison c Ctypes.Unsigned) w rs m r1 r2 = Some b.
Proof.
  intros.
  unfold transl_comparison.
  unfold cmpu in H.
  destruct c ; simpl; auto.
Qed.

Lemma transl_cbranch_signed_correct:
  forall c (w:width) r1 r2 lbl (rs: regset) m b,
    (cmp w) c rs#(IR r1) (eval_reg_immw w rs r2) = Some b ->
  exec_instr ge fn (transl_cbranch_signed c w r1 r2 lbl) rs m =
  exec_branch fn lbl rs m (Some b).
Proof.
  intros.
  unfold transl_cbranch_signed.
  simpl.
  apply transl_comparison_signed_correct with (m:=m) in H.
  rewrite H. reflexivity.
Qed.

Lemma transl_cbranch_unsigned_correct:
  forall c w r1 r2 lbl (rs: regset) m b,
    (cmpu w) (Mem.valid_pointer m) c rs#(IR r1) (eval_reg_immw w rs r2) = Some b ->
  exec_instr ge fn (transl_cbranch_unsigned c w r1 r2 lbl) rs m =
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
          | [ H: match _ with left _ => _ | right _ => assertion_failed end = OK _ |- _ ] => monadInv H; ArgsInv
          | [ H: match _ with true => _ | false => assertion_failed end = OK _ |- _ ] => monadInv H; ArgsInv
          | [ H: match _ with left _ => _ | right _ => failwith _ end = OK _ |- _ ] => monadInv H; ArgsInv
          | [ H: match _ with left _ => _ | right _ => failwith _ end = OK _ |- _ ] => monadInv H; ArgsInv
          | [ H: match _ with true => _ | false => failwith _ end = OK _ |- _ ] => monadInv H; ArgsInv

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
  (* 32 bits *)
  - exists rs, (transl_cbranch_signed c0 W32 x (inl x0) lbl).
    intuition auto. constructor. apply transl_cbranch_signed_correct; auto.
  - exists rs, (transl_cbranch_unsigned c0 W32 x (inl x0) lbl).
    intuition auto. constructor. apply transl_cbranch_unsigned_correct; auto.
  - exists rs, (transl_cbranch_signed c0 W32 x (inr  n) lbl).
    intuition auto. constructor. apply transl_cbranch_signed_correct; auto.
  - exists rs, (transl_cbranch_unsigned c0 W32 x (inr n) lbl).
    intuition auto. constructor. apply transl_cbranch_unsigned_correct; auto.
  (* 64 bits *)
  - exists rs, (transl_cbranch_signed c0 W64 x (inl x0) lbl).
    intuition auto. constructor. apply transl_cbranch_signed_correct; auto.
  - exists rs, (transl_cbranch_unsigned c0 W64 x (inl x0) lbl).
    intuition auto. constructor. apply transl_cbranch_unsigned_correct; auto.
  - exists rs, (transl_cbranch_signed c0 W64 x (inr  x0) lbl).
    get_int_inv.
    intuition auto. constructor.
    apply transl_cbranch_signed_correct; auto. simpl.
    unfold int64_of_intu. rewrite H0. rewrite Int64.repr_unsigned. auto.
  - exists rs, (transl_cbranch_unsigned c0 W64 x (inr x0) lbl).
    get_int_inv.
    intuition auto. constructor. apply transl_cbranch_unsigned_correct; auto.
    simpl. unfold int64_of_intu. rewrite H0. rewrite Int64.repr_unsigned. auto.
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

Definition cmp (w:width) (c:comparison) (v1 v2:val) : val :=
  if w then Val.cmp c v1 v2
  else Val.of_optbool (Val.cmpl_bool c v1 v2).

Lemma transl_cond_signed_correct:
  forall c (w:width) r1 r2 k rs m,
  exists rs',
     exec_straight ge fn (transl_cond_as_Pcmp c w Ctypes.Signed r1 r2  k) rs m k rs' m
  /\ Val.lessdef (cmp w  c rs#r1 (eval_reg_immw w rs r2)) rs'#r1
  /\ forall r, r <> PC -> r <> r1 -> rs'#r = rs#r.
Proof.
  intros.
  unfold transl_cond_as_Pcmp.
  destruct w.
  - destruct c; simpl; TranslCondSimpl.
    unfold eval_cmp; destruct (rs#r1); auto; destruct (eval_reg_immw W32 rs r2); auto.
  unfold eval_cmp; destruct (rs#r1); auto; destruct (eval_reg_immw W32 rs r2); auto.
  - destruct c; simpl; TranslCondSimpl.
    + destruct ((Val.cmpl_bool Ceq (rs r1) (eval_reg_immw W64 rs r2))) eqn:E.
      eapply cmp_cmplu_Ceq in E. rewrite E. constructor.
      constructor.
    + destruct ((Val.cmpl_bool Cne (rs r1) (eval_reg_immw W64 rs r2))) eqn:E.
      eapply cmp_cmplu_Cne in E. rewrite E. constructor.
      constructor.
Qed.

Definition cmpu (w:width) f  (c:comparison) (v1 v2:val) : val :=
  if w then Val.cmpu f c v1 v2
  else Val.of_optbool (Val.cmplu_bool f c v1 v2).


Lemma transl_cond_unsigned_correct:
  forall c w r1 r2 k rs m,
  exists rs',
     exec_straight ge fn (transl_cond_as_Pcmp c w Ctypes.Unsigned r1 r2 k) rs m k rs' m
  /\ Val.lessdef (cmpu w (Mem.valid_pointer m) c rs#r1 (eval_reg_immw w rs r2)) rs'#r1
  /\ forall r, r <> PC -> r <> r1 -> rs'#r = rs#r.
Proof.
  intros. destruct  w.
  - destruct c; simpl; TranslCondSimpl.
  - destruct c; simpl; TranslCondSimpl.
Qed.

Lemma transl_cond_as_jump_correct:
  forall c w r1 r2 k rs m,
  exists rs',
     exec_straight ge fn (transl_cond_as_Pcmp c w Ctypes.Signed r1 r2 k) rs m k rs' m
  /\ Val.lessdef (cmp w c rs#r1 (eval_reg_immw w rs r2)) rs'#r1
  /\ forall r, r <> PC -> r <> r1 -> rs'#r = rs#r.
Proof.
  intros.
  unfold transl_cond_as_Pcmp.
  destruct w.
  - destruct c; simpl; TranslCondSimpl.
    unfold eval_cmp; destruct (rs#r1); auto; destruct (eval_reg_immw W32 rs r2); auto.
    unfold eval_cmp; destruct (rs#r1); auto; destruct (eval_reg_immw W32 rs r2); auto.
  - destruct c; simpl; TranslCondSimpl.
    + destruct ((Val.cmpl_bool Ceq (rs r1) (eval_reg_immw W64 rs r2))) eqn:E.
      eapply cmp_cmplu_Ceq in E. rewrite E. constructor.
      constructor.
    + destruct ((Val.cmpl_bool Cne (rs r1) (eval_reg_immw W64 rs r2))) eqn:E.
      eapply cmp_cmplu_Cne in E. rewrite E. constructor.
      constructor.
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
  - exploit transl_cond_signed_correct; eauto.
    intros (rs' & A & B & C). exists rs'; eauto.
  - exploit transl_cond_unsigned_correct; eauto.
    intros (rs' & A & B & C). exists rs'; eauto.
  -
    get_int_inv.
    exploit transl_cond_signed_correct; eauto.
    intros (rs' & A & B & C). exists rs'.
    split. apply A.
    split;auto. simpl in B.
    unfold int64_of_intu in B. rewrite H0 in B.
    rewrite Int64.repr_unsigned in B;auto.
  - get_int_inv.
    exploit transl_cond_unsigned_correct; eauto.
    intros (rs' & A & B & C). exists rs'.
    split. apply A.
    split;auto. simpl in B.
    unfold int64_of_intu in B. rewrite H0 in B.
    rewrite Int64.repr_unsigned in B;auto.
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
  [ apply exec_straight_one; [ unfold exec_instr, exec_alu, int64_of_intu;simpl; rewrite EV; try reflexivity | reflexivity]
  | split; [ apply Val.lessdef_same; Simpl; fail | intros; Simpl; fail ] ].

Ltac TranslALU64OpSimpl EV :=
  econstructor; split;
  [ apply exec_straight_one; [ unfold exec_instr, exec_alu;simpl; unfold int64_of_intu; try rewrite EV ; try reflexivity | reflexivity]
  | split; [ apply Val.lessdef_same; Simpl | intros; Simpl ] ].



Lemma sign_ext_8 : forall x rs k  m,
  exists rs' : regset,
    exec_straight ge fn (Palu LSH W32 x (inr (Int.repr 24)) :: Palu ARSH W32 x (inr (Int.repr 24)) :: k) rs m k rs' m /\
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
    exec_straight ge fn (Palu LSH W32 x (inr (Int.repr 16)) :: Palu ARSH W32 x (inr (Int.repr 16)) :: k) rs m k rs' m /\
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

Lemma sign_ext_32 : forall x rs k  m,
  exists rs' : regset,
    exec_straight ge fn (Palu (CONV DWOFW) W64 x (inr Int.zero)
      :: Palu LSH W64 x (inr (Int.repr 32)) :: Palu ARSH W64 x (inr (Int.repr 32)) :: k) rs m k rs' m /\
      (Val.longofint (rs x)) =  (rs' x) /\
      (forall r : preg, r <> PC -> r <> x  -> rs' r = rs r).
Proof.
  intros.
  eexists.  split;[|split].
  - eapply exec_straight_three; reflexivity.
  - Simpl.
    unfold map_sum_left. unfold eval_val_int.
    unfold Val.longofint,Val.longofintu.
    destruct (rs x) ; auto.
    unfold Val.shll.
    change (Int.ltu (Int.repr 32) Int64.iwordsize') with true.
    cbv iota.
    unfold Val.shrl.
    change (Int.ltu (Int.repr 32) Int64.iwordsize') with true.
    cbv iota.
    f_equal.
    rewrite Int64.shr'_shl' by reflexivity.
    change (Int.ltu (Int.repr 32) (Int.repr 32)) with false.
    cbv iota.
    change ((Int64.zwordsize - Int.unsigned (Int.repr 32))) with 32.
    change ((Int.sub (Int.repr 32) (Int.repr 32))) with Int.zero.
    rewrite Int64.shr'_zero.
    apply Int64.same_bits_eq.
    intros.
    rewrite Int64.bits_sign_ext; auto.
    rewrite Int64.testbit_repr by auto.
    rewrite Int.bits_signed by lia.
    rewrite Int64.testbit_repr.
    change (Int.zwordsize) with 32.
    destruct (zlt i0 32).
    unfold Int.testbit.
    reflexivity.
    reflexivity.
    change (Int64.zwordsize) with 64.
    destruct (zlt i0 32);lia.
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
  - (* addrstack *)
    exploit addptrofs_correct; eauto.
    intros (rs' & A & B & C).
    exists rs'; split; [ exact A | auto with asmgen ].
  (* divu, divuimm, modu, moduimm *)
- TranslALUOpSimpl EV.
- TranslALUOpSimpl EV.
- TranslALUOpSimpl EV.
- TranslALUOpSimpl EV.
- TranslALU64OpSimpl EQ.
  rewrite H0. rewrite Int64.repr_unsigned. reflexivity.
- TranslALU64OpSimpl EQ.
  rewrite H0. rewrite Int64.repr_unsigned. reflexivity.
- TranslALU64OpSimpl EQ.
  rewrite H0. rewrite Int64.repr_unsigned. reflexivity.
- TranslALU64OpSimpl EV.
- clear H.
  get_int_inv.
  econstructor; split.
  + apply exec_straight_one; unfold exec_instr, exec_alu;simpl; unfold int64_of_intu.
    rewrite H0. rewrite Int64.repr_unsigned. rewrite EV. reflexivity.
    Simpl.
  + split; [ apply Val.lessdef_same; Simpl | intros; Simpl ].
- TranslALU64OpSimpl EV.
- clear H.
  get_int_inv.
  econstructor; split.
  + apply exec_straight_one; unfold exec_instr, exec_alu;simpl; unfold int64_of_intu.
    rewrite H0. rewrite Int64.repr_unsigned. rewrite EV. reflexivity.
    Simpl.
  + split; [ apply Val.lessdef_same; Simpl | intros; Simpl ].
- TranslALU64OpSimpl EQ1.
  rewrite H0. rewrite Int64.repr_unsigned. reflexivity.
- TranslALU64OpSimpl EQ1.
  rewrite H0. rewrite Int64.repr_unsigned. reflexivity.
- TranslALU64OpSimpl EQ1.
  rewrite H0. rewrite Int64.repr_unsigned. reflexivity.
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
- (* sign_ext 32 *)
  exploit sign_ext_32.
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
