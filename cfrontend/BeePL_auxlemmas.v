Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import BeePL BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import compcert.common.Errors Initializersproof Cstrategy lib.Coqlib Errors.

From mathcomp Require Import all_ssreflect. 

Lemma access_mode_preserved : forall ty cty md g g' i, 
access_mode ty = md ->
transBeePL_type ty g =  Res cty g' i ->
Ctypes.access_mode cty = md.
Proof.
  intros ty cty md HACCESS HTRANS.
  destruct ty eqn:Ety; simpl in HACCESS.
  (* Case: Ptype *)
  - destruct p eqn:Ep; simpl in *.
    (* Tunit *)
    + admit.
    (* Tint *)
    + destruct i; destruct s; monadInv HTRANS; eauto.
    (* Tlong *)
    + destruct s; monadInv HTRANS; eauto.
  (* Case: Reftype *)
  - destruct b; simpl in *;
    destruct p; simpl in *;
    monadInv HTRANS;
    eauto.
  (* Case: Ftype *)
  - monadInv HTRANS.
    destruct (transBeePL_types transBeePL_type l) eqn:?;
    try discriminate.
    destruct (transBeePL_type t) eqn:?; try discriminate.
    reflexivity.
Admitted.

Lemma non_volatile_type_preserved : forall ty cty g g' i',
type_is_volatile ty = false ->
transBeePL_type ty g = Res cty g' i' ->
Ctypes.type_is_volatile cty = false.
Proof.
  intros ty cty HNVOL HTRANS.
  destruct ty eqn:Ety; simpl in *.
  (* Case: Ptype *)
  - destruct p; simpl in *; monadInv HTRANS; eauto.
  (* Case: Reftype *)
  - destruct b; destruct p; simpl in *;
    monadInv HTRANS; eauto.
  (* Case: Ftype *)
  - monadInv HTRANS.
    destruct (transBeePL_types transBeePL_type l) eqn:?;
    try discriminate.
    destruct (transBeePL_type t) eqn:?; try discriminate.
    eauto.
Qed.


Lemma typec_expr : forall e ct ce g g' g'' i i',
transBeePL_type (typeof_expr e) g = Res ct g' i ->
transBeePL_expr_expr e  g' = Res ce g'' i' ->
ct = Csyntax.typeof ce.
Proof.
  induction e; simpl; intros.
  (* Case: Val *)
  - monadInv H0.
    rewrite EQ in H. inv H.
    reflexivity.
  (* Case: Valof *)
  - monadInv H0.
    rewrite EQ in H. inv H.
    reflexivity.
  (* Case: Var *)
  - monadInv H0.
    rewrite EQ in H. inv H.
    reflexivity.
  (* Case: Const *)
  - destruct c; monadInv H0;
    rewrite EQ in H; inv H;
    reflexivity.
  (* Case: App *)
  - monadInv H0.
    rewrite EQ0 in H. inv H.
    reflexivity.
  (* Case: Prim *)
  - destruct b eqn:Eb; monadInv H0; try discriminate;
    try (rewrite EQ1 in H; inv H; reflexivity).
    (* Want to double check the case for Run*)
    admit.
  (* Case: Bind *)
  - monadInv H0.
    rewrite EQ2 in H. inv H.
    reflexivity.
  (* Case: Cond *)
  - monadInv H0.
    rewrite EQ2 in H. inv H.
    reflexivity.
  (* Case: Unit *)
  - monadInv H0.
    rewrite EQ in H. inv H.
    reflexivity.
  (* Case: Addr *)
  - monadInv H0.
    rewrite EQ in H. inv H.
    reflexivity.
  (* Case: Hexpr *)
  - admit.
Admitted.


Lemma bv_cv_reflex : forall v' v,
transC_val_bplvalue v' = OK v ->
transBeePL_value_cvalue v = v'.
Proof.
  intros v' v H.
  destruct v' eqn:?; simpl in *; try discriminate;
  inv H; reflexivity.
Qed.
