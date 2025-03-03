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
  destruct ty eqn:Htype.
  (* Prim *)
  - destruct p eqn:Hp;
    simpl in *;
    injection HTRANS as H1 H2;
    subst;
    reflexivity.
  (* Ref *)
  - destruct b; simpl in *;
    destruct p; simpl in *;
    injection HTRANS as H1 H2;
    subst;
    reflexivity.
  (* Ftype *)
  - destruct e; simpl in *;
    unfold SimplExpr.bind in HTRANS;
    destruct (transBeePL_types transBeePL_type l g) eqn:Htypes; try discriminate;
    destruct (transBeePL_type t g'0) eqn:Htype'; try discriminate;
    injection HTRANS as H1 H2; subst;
    reflexivity.
Qed.

Lemma non_volatile_type_preserved : forall ty cty g g' i' b,
type_is_volatile ty = b ->
transBeePL_type ty g = Res cty g' i' ->
Ctypes.type_is_volatile cty = b.
Proof.
  intros ty cty g g' i' b HVOL HTRANS.
  destruct ty eqn:Htype.
  (* Prim *)
  - destruct p eqn:Hp; 
    simpl in *;
    injection HTRANS as H1 H2;
    subst;
    reflexivity.
  (* Ref *)
  - destruct b0; simpl in *;
    destruct p; simpl in *;
    injection HTRANS as H1 H2;
    subst;
    reflexivity.
(* Ftype *)
  - destruct e; simpl in *;
    unfold SimplExpr.bind in HTRANS;
    destruct (transBeePL_types transBeePL_type l g) eqn:Htypes; try discriminate;
    destruct (transBeePL_type t g'0) eqn:Htype'; try discriminate;
    injection HTRANS as H1 H2; subst;
    reflexivity.
Qed.

Lemma typec_expr : forall e ct ce g g' g'' i i',
transBeePL_type (typeof_expr e) g = Res ct g' i ->
transBeePL_expr_expr e  g' = Res ce g'' i' ->
ct = Csyntax.typeof ce.
Proof.
  induction e; intros; simpl in *; unfold SimplExpr.bind in H0.
  (* Val *)
  - destruct t eqn:?.
    + destruct p; simpl in *;
      injection H0 as H1 H2; subst;
      injection H as H1 H2; subst;
      reflexivity.
    + destruct b; simpl in *;
      destruct p; simpl in *;
      injection H as H1 H2; subst;
      injection H0 as H1 H2; subst;
      reflexivity.
    + admit.
  - (* Rest of proofs should be similar *)
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
  intro t.
  apply transBeePL_type_ind with (t := t); intros.
  (* Prim *)
  - unfold transBeePL_type in *.
    destruct t0;
    injection H1 as H1 H1'; subst;
    injection H2 as H2 H2'; subst;
    reflexivity.
  (* Ref *)
  - unfold transBeePL_type in *.
    destruct bt; destruct p;
    injection H1 as H1 H1'; subst;
    injection H2 as H2 H2'; subst;
    reflexivity.
  (* Ftype *)
  - admit.

Admitted.

Lemma transBeePL_expr_expr_type_equiv : forall e ce g g' i,
transBeePL_expr_expr e g = Res ce g' i ->
transBeePL_type (typeof_expr e) g = Res (Csyntax.typeof ce) g' i.
Proof.
  induction e; intros; simpl in *; unfold SimplExpr.bind in H.
  - destruct (transBeePL_type t g) eqn:Htype; try discriminate.
    destruct (ret (Eval (transBeePL_value_cvalue v) t0) g'0) eqn:Hret; try discriminate.
    inversion Hret. subst.
    injection H as H1 H2; subst.
    simpl.
    unfold transBeePL_type in Htype. 
    f_equal.
    (* Need i = p *)
    (* reflexivity. *)
Admitted.


Lemma value_cannot_be_reduced : forall bge benv e m e' m',
is_value e -> 
~ (rreduction bge benv e m e' m') /\
~ (lreduction bge benv e m e' m').
Proof.
move=> bge benv e. elim: e=> //= v t m e' m' _ /=. split=> //=.
+ move=> h. by inversion h.
move=> h. by inversion h.
Qed.

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


