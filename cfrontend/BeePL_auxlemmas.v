Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import BeePL BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import compcert.common.Errors Initializersproof Cstrategy lib.Coqlib Errors.

From mathcomp Require Import all_ssreflect. 

Lemma access_mode_preserved : forall ty cty md, 
access_mode ty = md ->
transBeePL_type ty =  cty ->
Ctypes.access_mode cty = md.
Proof.
Admitted.

Lemma non_volatile_type_preserved : forall ty cty b,
type_is_volatile ty = b ->
transBeePL_type ty = cty ->
Ctypes.type_is_volatile cty = b.
Proof.
Admitted.

Lemma typec_expr : forall e ct ce g' g'' i',
transBeePL_type (typeof_expr e) = ct ->
transBeePL_expr_expr e  g' = Res ce g'' i' ->
ct = Csyntax.typeof ce.
Proof.
Admitted.

Lemma bv_cv_reflex : forall v' v,
transC_val_bplvalue v' = OK v ->
transBeePL_value_cvalue v = v'.
Proof.
Admitted.

(* Since translation of types does not depend on the generator, it 
   should produce the same result irrespective of them *)
(* Coqlib.v has lot of lemmas related to Ple *)
Lemma type_preserved_generator : forall t r r' ,
transBeePL_type t = r ->
transBeePL_type t = r'->
r = r'.
Proof. (* use inductive principle proved in BeeTypes.v *)
Admitted.

Lemma transBeePL_expr_expr_type_equiv : forall e ce g g' i,
transBeePL_expr_expr e g = Res ce g' i ->
transBeePL_type (typeof_expr e) = (Csyntax.typeof ce).
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







