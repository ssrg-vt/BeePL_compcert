Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import BeePL BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import compcert.common.Errors Initializersproof Cstrategy compcert.lib.Coqlib Errors.

From mathcomp Require Import all_ssreflect. 

Lemma access_mode_preserved : forall ty cty md g g' i, 
access_mode ty = md ->
transBeePL_type ty g =  Res cty g' i ->
Ctypes.access_mode cty = md.
Proof.
  intros ty cty md g g' i HACCESS HTRANS.
  destruct ty eqn:Ety; simpl in HACCESS.
  (* Case: Ptype *)
  - destruct p eqn:Ep; simpl in *.
    (* Tunit *)
    + admit.
    (* Tint *)
    + destruct i0; destruct s;
      injection HTRANS as EQ; subst;
      eauto.
    (* Tlong *)
    + destruct s;
      injection HTRANS as EQ; subst;
      eauto.
  (* Case: Reftype *)
  - destruct b; simpl in *;
    destruct p; simpl in *;
    injection HTRANS as EQ; subst.
    eauto.
  (* Case: Ftype *)
  - admit.
Admitted.

Lemma non_volatile_type_preserved : forall ty cty g g' i' b,
type_is_volatile ty = b ->
transBeePL_type ty g = Res cty g' i' ->
Ctypes.type_is_volatile cty = b.
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

(* Since translation of types does not depend on the generator, it 
   should produce the same result irrespective of them *)
(* Coqlib.v has lot of lemmas related to Ple *)
Lemma type_preserved_generator : forall t r r' g1 g2 g3 g4 i1 i2,
Ple (gen_next g1) (gen_next g2) ->
Ple (gen_next g3) (gen_next g4) ->
transBeePL_type t g1 = Res r g2 i1 ->
transBeePL_type t g3 = Res r' g4 i2 ->
r = r'.
Proof. (* use inductive principle proved in BeeTypes.v *)
Admitted.

Lemma transBeePL_expr_expr_type_equiv : forall e ce g g' i,
transBeePL_expr_expr e g = Res ce g' i ->
transBeePL_type (typeof_expr e) g = Res (Csyntax.typeof ce) g' i.
Proof.
Admitted. 

(*
Lemma val_cannot_be_reduced : forall bge benv e m e' m',
is_val e -> 
~ (rreduction bge benv e m e' m') /\
~ (lreduction bge benv e m e' m').
Proof.
move=> bge benv e. elim: e=> //= v t m e' m' _ /=. split=> //=.
+ move=> h. by inversion h.
move=> h. by inversion h.
Qed.

Lemma addr_cannot_be_reduced : forall bge benv e m e' m',
is_addr e -> 
~ (rreduction bge benv e m e' m') /\
~ (lreduction bge benv e m e' m').
Proof.
move=> beg benv e. elim: e=> //= v t m e' m' _ /=. split=> //=.
+ move=> h. by inversion h.
move=> h. by inversion h.
Qed.*)


