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
Admitted.

Lemma non_volatile_type_preserved : forall ty cty g g' i',
type_is_volatile ty = false ->
transBeePL_type ty g = Res cty g' i' ->
Ctypes.type_is_volatile cty = false.
Proof.
Admitted.

Lemma typec_expr : forall e ct ce g g' g'' i i',
transBeePL_type (typeof_expr e) g = Res ct g' i ->
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
Lemma type_preserved_generator : forall t r r' g1 g2 g3 g4 i1 i2,
Ple (gen_next g1) (gen_next g2) ->
Ple (gen_next g3) (gen_next g4) ->
transBeePL_type t g1 = Res r g2 i1 ->
transBeePL_type t g3 = Res r' g4 i2 ->
r = r'.
Proof.
move=> t r r' g1 g2 g3 g4 i1 i2 hp hp'. move: r r' g1 g2 g3 g4 i1 i2 hp hp'. elim: t=> //=.
+ move=> p. case: p=> //=.
  + by move=> r r' g1 g2 g3 g4 i1 i2 hp hp' [] h1 h2 [] h1' h2'; subst.
  + by move=> r r' i s a g1 g2 g3 g4 i1 i2 hp hp' [] h1 h2 [] h1' h2'; subst.
  by move=> r r' s a g1 g2 g3 g4 i1 i2 hp hp' [] h1 h2 [] h1' h2'; subst.
+ move=> id b a r r' g1 g2 g3 g4 i1 i2 hp hp'. case: b=> //= p.
  case: p=> //=.
  + by move=> [] h1 h2 [] h3 h4; subst.
  + by move=> i s a' [] h1 h2 [] h3 h4; subst.
  by move=> s a' [] h1 h2 [] h3 h4; subst.
move=> es ef t hi r r' g1 g2 g3 g4 i1 i2 hp hp'.
Admitted.

Lemma transBeePL_expr_expr_type_equiv : forall e ce g g' i,
transBeePL_expr_expr e g = Res ce g' i ->
transBeePL_type (typeof_expr e) g = Res (Csyntax.typeof ce) g' i.
Proof.
Admitted. 







