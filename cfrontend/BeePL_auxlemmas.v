Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import BeePL BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import compcert.common.Errors Initializersproof Cstrategy lib.Coqlib Errors.

From mathcomp Require Import all_ssreflect. 

Lemma access_mode_preserved : forall ty cty md, 
access_mode_type ty = md ->
transBeePL_type ty =  cty ->
Ctypes.access_mode cty = md.
Proof.
Admitted.

Lemma non_volatile_type_preserved : forall ty cty b,
type_is_volatile (transBeePL_type ty) = b ->
transBeePL_type ty = cty ->
Ctypes.type_is_volatile cty = b.
Proof.
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
Admitted.

Lemma bc_cv_comp : forall v,
trans_cvalue_bvalue (trans_bvalue_cvalue v) = OK v.
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


(*** Auxillary lemmas related to types and effects ***)
(* Complete Me: Easy *)
Lemma sub_effect_refl : forall ef, 
sub_effect ef ef = true.
Proof.
Admitted.

(* Complete Me: Easy *)
Lemma sub_effect_nil : forall ef, 
sub_effect nil ef = true.
Proof.
Admitted.

(* Complete Me: Easy *)
Lemma sub_effect_trans : forall ef1 ef2 ef3, 
sub_effect ef1 ef2 = true ->
sub_effect ef2 ef3 = true ->
sub_effect ef1 ef3 = true.
Proof.
Admitted.

(* Complete Me: Easy *)
Lemma prefix_sub_effect : forall (ef1 ef2 : effect), 
sub_effect ef1 (ef1 ++ ef2)%list = true.
Proof. 
Admitted.

(* Complete Me: Easy *)
Lemma suffix_sub_effect : forall (ef1 ef2 : effect), 
sub_effect ef2 (ef1 ++ ef2)%list = true.
Proof. 
Admitted.

(* Complete Me: Easy *)
Lemma sub_effect_concat : forall ef1 ef2 ef1' ef2',
sub_effect ef1 ef1' ->
sub_effect ef2 ef2' ->
sub_effect (ef1 ++ ef2) (ef1' ++ ef2').
Proof.
Admitted.

(* Complete Me: Easy *)
Lemma no_divergence_concat : forall ef ef',
no_divergence ef ->
no_divergence ef' ->
no_divergence (ef ++ ef').
Proof.
Admitted. 







