Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Csem Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import Initializersproof Cstrategy BeePL_auxlemmas Coqlib Errors BeePL_values BeePL_sem.

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

(*Lemma div_c_exec : forall cge cvm m ce1 ce2 tr m' a' v1 v2 zv g g' i' rs t,
eval_expr cge cvm m RV (hd default_expr (exprlist_list_expr ce2)) tr m' a' ->
eval_simple_rvalue cge cvm m' a' (trans_bvalue_cvalue v2) ->
signedness_of_type t = Some Signed ->
is_zero_val v2 || is_overflow_vals v1 v2 ->
check_div (Econs ce1 ce2) zv (transBeePL_type t) g = Res rs g' i' ->
rs = Eval zv (transBeePL_type t).
Proof.
move=> cge cvm m ce1 ce2 tr m' a' v1 v2 zv g g' i' rs t he he' hs hv hc.
rewrite /check_div in hc. case: t hs hc=> //=.
+ move=> [] //=.
  + move=> sz s a [] hs; subst; rewrite /=.
    case: sz=> //=. move=> [] h1 h2; subst.*)















