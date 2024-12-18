Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import compcert.common.Errors Initializersproof Cstrategy lib.Coqlib Errors.

From mathcomp Require Import all_ssreflect. 

Lemma access_mode_preserved : forall ty cty md, 
access_mode ty = md ->
transBeePL_type ty = OK cty ->
Ctypes.access_mode cty = md.
Proof.
Admitted.

Lemma non_volatile_type_preserved : forall ty cty,
type_is_volatile ty = false ->
transBeePL_type ty = OK cty ->
Ctypes.type_is_volatile cty = false.
Proof.
Admitted.

Lemma typec_expr : forall e ct ce,
transBeePL_type (typeof_expr e) = OK ct ->
transBeePL_expr_expr e = OK ce ->
ct = Csyntax.typeof ce.
Proof.
Admitted.

Lemma bv_cv_reflex : forall v' v,
transC_val_bplvalue v' = OK v ->
transBeePL_value_cvalue v = v'.
Proof.
Admitted.


