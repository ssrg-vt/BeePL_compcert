Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import compcert.common.Errors Initializersproof Cstrategy BeePL_auxlemmas Coqlib Errors Memory.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import BeePL_sem BeePL_typesystem BeePL_safety BeePL_typesystem_proofs.

From mathcomp Require Import all_ssreflect.

(***** Termination *****)
(* A well typed program where the effects contain no divergence effect is always terminating *)
Lemma guaranteed_termination : 
(forall Gamma Sigma es efs ts bge vm m n m' vm' es', 
 type_exprs Gamma Sigma es efs ts ->
 no_divergence efs ->
 ssem_closures bge vm m es n m' vm' es' ->
 exists m, (n <= m)%nat) /\
(forall Gamma Sigma e ef t bge vm m n m' vm' e', 
 type_expr Gamma Sigma e ef t ->
 no_divergence ef ->
 ssem_closure bge vm m e n m' vm' e' ->
 exists m, (n <= m)%nat).
Proof.
Admitted.
