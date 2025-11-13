Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Csem Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import Initializersproof Cstrategy BeePL_auxlemmas Coqlib Errors BeePL_values BeePL_sem Ctyping.

From mathcomp Require Import all_ssreflect. 

Lemma c_eval_expr_type_preservation: forall e cge cvm m e' tr m',
eval_expr cge cvm m RV e tr m' e' ->
Csyntax.typeof e = Csyntax.typeof e'.
Proof.
move=> e. elim: e=> //=.
(* val *)
+ move=> v ty cge cvm m e' tr m' he. by inversion he; subst.
(* var *)
+ move=> x ty cge cvm m e' tr m' he. by inversion he; subst.
(* field *)
+ move=> e' hin f ty cge cvm m e'' tr m' he. by inversion he; subst.
(* evalof *)
+ move=> e' hin ty cge cvm m e'' tr m' he. by inversion he; subst.
(* deref *)
+ move=> e' hin ty cge cvm m e'' tr m' he. by inversion he; subst.
(* addrof *)
+ move=> e' hin ty cge cvm m e'' tr m' he. by inversion he; subst.
(* uop *)
+ move=> o e' hin ty cge cvm m e'' tr m' he. by inversion he; subst.
(* bop *)
+ move=> o e1 hin1 e2 hin2 ty cge cvm m e'' tr m' he. by inversion he; subst.
(* cast *)
+ move=> e' hin ty cge cvm m e'' tr m' he. by inversion he; subst.
(* seqand *)
+ move=> e1 hin1 e2 hin2 ty cge cvm m e'' tr m' he. by inversion he; subst.
(* seqor *)
+ move=> e1 hin1 e2 hin2 ty cge cvm m e'' tr m' he. by inversion he; subst.
(* condition *)
+ move=> e1 hin e2 hin2 e3 hin3 ty cge cvm m e'' tr m' he. by inversion he; subst.
(* sizeof *)
+ move=> ty1 ty2 cge cvm m e'' tr m' he. by inversion he; subst.
(* alignof *)
+ move=> ty1 ty2 cge cvm m e'' tr m' he. by inversion he; subst.
(* assign *)
+ move=> e1 hin e2 hin' ty cge cvm m e'' tr m' he. by inversion he; subst.
(* assignop *)
+ move=> op e' hin e1 hin' t1 t2 cge cvm m e'' tr m' he. by inversion he; subst.
(* postincr *)
+ move=> id e' hin ty cge cvm m e'' tr m' he. by inversion he; subst.
(* comma *)
+ move=> e1 hin e2 hin' ty cge cvm m e'' tr m' he. inversion he; subst.
  move: (hin cge cvm m r1' t1 m1 H2)=> ht1. 
  by move: (hin' cge cvm m1 e'' t2 m' H6)=> ht2; subst.
(* call *)
+ move=> e1 hin args ty cge cvm m e' tr m' he. by inversion he; subst.
(* builtin *)
+ move=> ef ts args ty cge cvm m e' tr m' he. by inversion he; subst.
(* loc *)
+ move=> b ofs bf ty cge cvm m e' tr m' he. by inversion he; subst.
move=> e1 hin t1 t2 cge cvm m e' tr m' he. by inversion he; subst.
Qed.

(* Medium *)
Lemma deref_loc_no_trace_nonvolatile : forall cge t m l ofs bf v,
Csem.deref_loc cge t m l ofs bf Events.E0 v ->
type_is_volatile t = false.
Proof.
Admitted.

(*Lemma eval_simple_rvalue_type_preservation: forall e cge cvm m v,
eval_simple_rvalue cge cvm m e v ->
Ctyping.wt_val v (Csyntax.typeof e).
Proof.
move=> e. elim: e=> //=.
(* val *)
+ move=> v t cge cvm m  v' hrv. inversion hrv; subst.
  case: v' hrv=> //=.
  + move=> hrv. by apply wt_val_undef.
  + case: t=> //=.
    + move=> i hrv. by apply wt_val_void.
    + move=> sz s a i hrv. apply wt_val_int.
      Print wt_int.

Lemma eval_expression_type_preservation:
eval_expression cge cvm m e tr m' v ->
Cop.val_casted v (Csyntax.typeof e).*)
