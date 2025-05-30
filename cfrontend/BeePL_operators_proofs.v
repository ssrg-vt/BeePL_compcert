Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import compcert.common.Errors Initializersproof Cstrategy BeePL_auxlemmas Coqlib Errors Memory.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import BeePL_sem BeePL_typesystem BeePL_compiler_proofs BeePL_values BeePL_notations.

From mathcomp Require Import all_ssreflect.

(* notbool are well-formed *) 
Lemma well_formed_notbool : forall cenv Gamma Sigma bge vm m v ef,
store_well_typed cenv Gamma Sigma bge vm m ->
type_expr cenv Gamma Sigma (Val v (Vtype Tbool)) ef (Vtype Tbool) ->
exists v' v'',
Cop.sem_unary_operation (Cop.Onotbool) (trans_bvalue_cvalue v) (transBeePL_type (Vtype Tbool)) m = Some v' /\
v' <> Values.Vundef /\
trans_cvalue_bvalue v' = OK v''.
Proof.
move=> cenv Gamma Sigma bge vm m v ef hw hte. 
rewrite / Cop.sem_unary_operation /= /Cop.sem_notbool /= /option_map /=.
case: v hte=> //=.
(* unit : bad case *)
+ move=> hte. by inversion hte.
(* bool : good case *)
+ move=> b hte. case: b hte=> //=. 
  (* b = true *)
  + move=> hte. rewrite /Values.Val.of_bool /=.
    have hn : ~~ ~~ Int.eq (Int.repr 1) Int.zero = false.
    + rewrite /negb /=. have hz : Int.eq (Int.repr 1) Int.zero = false.
      + by auto. by rewrite hz /=.
    rewrite hn /=. exists Values.Vfalse. rewrite /trans_cvalue_bvalue /=. 
    by exists (Vint Int.zero).
  (* b = false *)
  move=> hte. rewrite /Values.Val.of_bool /=.
  have hn : ~~ ~~ Int.eq (Int.repr 0) Int.zero = true.
  + rewrite /negb /=. have hz : Int.eq (Int.repr 0) Int.zero = true.
    + by auto. by rewrite hz /=.
  rewrite hn /=. exists Values.Vtrue. rewrite /trans_cvalue_bvalue /=. 
  by exists (Vint Int.one).
(* int : bad case *)
+ move=> i hte. by inversion hte.
(* int64 : bad case *)
+ move=> l hte. by inversion hte.
(* ptr : bad case *)
+ move=> p o hte. by inversion hte.
(* o : bad case *)
move=> o hte. by inversion hte.
Qed.
