Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import BeePL BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import compcert.common.Errors Initializersproof Cstrategy compcert.lib.Coqlib Errors.

From mathcomp Require Import all_ssreflect. 

Lemma access_mode_preserved : forall ty cty md, 
access_mode ty = md ->
transBeePL_type ty =  cty ->
Ctypes.access_mode cty = md.
Proof.
  intros ty cty md HACCESS HTRANS.
  destruct ty eqn:Htype.
  (* Prim *)
  - destruct p eqn:Hp;
    simpl in *;
    subst;
    reflexivity.
  (* Ref *)
  - destruct b; simpl in *.
    + destruct p; simpl in *;
      subst;
      reflexivity.
    + subst. reflexivity.
  (* Ftype *)
  - destruct e; simpl in *;
    subst;
    reflexivity.
  (* Stype *)
  - subst. reflexivity.
  (* Otype *)
  - subst. reflexivity.
Qed.

Lemma non_volatile_type_preserved : forall ty cty b,
type_is_volatile ty = b ->
transBeePL_type ty = cty ->
Ctypes.type_is_volatile cty = b.
Proof.
  intros ty cty b HVOL HTRANS.
  destruct ty eqn:Htype.
  (* Prim *)
  - destruct p eqn:Hp; 
    simpl in *;
    subst;
    reflexivity.
  (* Ref *)
  - destruct b0; simpl in *.
    + destruct p; simpl in *;
      subst;
      reflexivity.
    + admit.
  (* Ftype *)
  - destruct e; simpl in *;
    subst;
    reflexivity.
  (* Stype *)
  - subst. reflexivity.
  (* Otype *)
  - subst. reflexivity.
Admitted.

(* Lemma typec_expr : forall e ct ce g' g'' i',
transBeePL_type (typeof_expr e) = ct ->
transBeePL_expr_expr e  g' = Res ce g'' i' ->
ct = Csyntax.typeof ce.
Proof.
Admitted. *)

Lemma bv_cv_reflex : forall v' v,
trans_cvalue_bvalue v' = OK v ->
trans_bvalue_cvalue v = v'.
Proof.
  intros v' v H.
  destruct v' eqn:?; simpl in *; try discriminate;
  inv H; reflexivity.
Qed.

(* Since translation of types does not depend on the generator, it 
   should produce the same result irrespective of them *)
(* Coqlib.v has lot of lemmas related to Ple *)
Lemma type_preserved_generator : forall t r r' ,
transBeePL_type t = r ->
transBeePL_type t = r'->
r = r'.
Proof. (* use inductive principle proved in BeeTypes.v *)
  intro t.
  apply transBeePL_type_ind with (t := t); intros.
  (* Prim *)
  - unfold transBeePL_type in *.
    destruct t0;
    subst;
    reflexivity.
  (* Ref *)
  - unfold transBeePL_type in *.
    destruct bt; simpl in *.
    + destruct p;
      subst;
      reflexivity.
    + subst. reflexivity.
  (* Ftype *)
  - admit.
Admitted.

(* Lemma transBeePL_expr_expr_type_equiv : forall e ce g g' i,
transBeePL_expr_expr e g = Res ce g' i ->
transBeePL_type (typeof_expr e) = (Csyntax.typeof ce).
Proof.
Admitted.  *)

(*
Lemma value_cannot_be_reduced : forall bge benv e m e' m',
is_value e -> 
~ (rreduction bge benv e m e' m') /\
~ (lreduction bge benv e m e' m').
Proof.
move=> bge benv e. elim: e=> //= v t m e' m' _ /=. split=> //=.
+ move=> h. by inversion h.
move=> h. by inversion h.
Qed.
*)

(* 
Lemma addr_cannot_be_reduced : forall bge benv e m e' m',
is_addr e -> 
~ (rreduction bge benv e m e' m') /\
~ (lreduction bge benv e m e' m').
Proof.
move=> beg benv e. elim: e=> //= v t m e' m' _ /=. split=> //=.
+ move=> h. by inversion h.
move=> h. by inversion h.
Qed.*)

Lemma unzip1_cancel {A} {B} : forall (l1 : list A) (l2 : list B),
  length l1 = length l2 ->
  l1 = BeePL_aux.unzip1 (BeePL_aux.zip l1 l2).
Proof.
  induction l1; intros.
  - destruct l2; auto.
  - simpl.
    destruct l2.
    + discriminate.
    + simpl. f_equal. auto.
Qed.

Lemma unzip2_cancel {A} {B} : forall (l1 : list A) (l2 : list B),
  length l1 = length l2 ->
  l1 = BeePL_aux.unzip2 (BeePL_aux.zip l2 l1).
Proof.
  induction l1; intros.
  - destruct l2; auto.
  - simpl.
    destruct l2.
    + discriminate.
    + simpl. f_equal. auto.
Qed.

Lemma unzip1_preserves_length {A} {B} {C} : forall (l1 : list (A * B)) (l2 : list C),
  length (BeePL_aux.unzip1 l1) = length l2 <->
  length l1 = length l2.
Proof.
  induction l1; intros; split; intros; auto.
  - simpl. 
    destruct l2.
    + discriminate.
    + simpl in *. f_equal. rewrite <- IHl1. auto.
  - simpl.
    destruct l2.
    + discriminate.
    + simpl in *. f_equal. rewrite IHl1. auto.
Qed.

Lemma unzip2_preserves_length {A} {B} {C} : forall (l1 : list (A * B)) (l2 : list C),
  length (BeePL_aux.unzip2 l1) = length l2 <->
  length l1 = length l2.
Proof.
  induction l1; intros; split; intros; auto.
  - simpl. 
    destruct l2.
    + discriminate.
    + simpl in *. f_equal. rewrite <- IHl1. auto.
  - simpl.
    destruct l2.
    + discriminate.
    + simpl in *. f_equal. rewrite IHl1. auto.
Qed.

Lemma to_typelist_cancel : forall (l : typelist),
  to_typelist (from_typelist l) = l.
Proof.
  induction l.
  - auto.
  - simpl. f_equal. auto.
Qed.

Lemma from_typelist_cancel : forall (l : list Ctypes.type),
  from_typelist (to_typelist l) = l.
Proof.
  induction l.
  - auto.
  - simpl. f_equal. auto.
Qed.
