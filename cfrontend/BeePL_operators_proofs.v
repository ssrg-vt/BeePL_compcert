Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import compcert.common.Errors Initializersproof Cstrategy BeePL_auxlemmas Coqlib Errors Memory.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import BeePL_sem BeePL_typesystem BeePL_compiler_proofs BeePL_values BeePL_notations.

From mathcomp Require Import all_ssreflect.

(* notbool is well-formed *) 
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

(* notint is well-formed *) 
Lemma well_formed_notint : forall cenv Gamma Sigma bge vm m v t ef,
store_well_typed cenv Gamma Sigma bge vm m ->
type_expr cenv Gamma Sigma (Val v t) ef t ->
is_primint t || is_primlong t ->
exists v' v'',
Cop.sem_unary_operation (Cop.Onotint) (trans_bvalue_cvalue v) (transBeePL_type t) m = Some v' /\
v' <> Values.Vundef /\
trans_cvalue_bvalue v' = OK v''.
Proof.
move=> cenv Gamma Sigma bge vm m v t ef hw hte heq. 
case: t hte heq=> //= p; case: p=> //=.
(* int *)
+ move=> sz s a hte _. rewrite /Cop.sem_notint /= /option_map /=.
  case: sz hte=> //=.
  (* I8 *)
  + case: v=> //=.
    + move=> hte. by inversion hte.
    + move=> b hte. by inversion hte.
    + move=> i hte. exists (Values.Vint (Int.not i)). 
      rewrite /trans_cvalue_bvalue /=. by exists (Vint (Int.not i)).
    + move=> i hte. by inversion hte.
    + move=> p i hte. by inversion hte.
    move=> o hte. by inversion hte.
  (* I16 *)
  + case: v=> //=.
    + move=> hte. by inversion hte.
    + move=> b hte. by inversion hte.
    + move=> i hte. exists (Values.Vint (Int.not i)). 
      rewrite /trans_cvalue_bvalue /=. by exists (Vint (Int.not i)).
    + move=> i hte. by inversion hte.
    + move=> p i hte. by inversion hte.
    move=> o hte. by inversion hte.
  (* I32 *)
  + case: v=> //=.
    + move=> hte. by inversion hte.
    + move=> b hte. by inversion hte.
    + move=> i hte. case: s hte=> //=. 
      + exists (Values.Vint (Int.not i)). 
        rewrite /trans_cvalue_bvalue /=. by exists (Vint (Int.not i)).
      exists (Values.Vint (Int.not i)). 
      rewrite /trans_cvalue_bvalue /=. by exists (Vint (Int.not i)).
    + move=> i hte. by inversion hte.
    + move=> p i hte. by inversion hte.
    move=> o hte. by inversion hte.
  (* IBool *) 
  case: v=> //=.
  + move=> hte. by inversion hte.
  + move=> b hte. by inversion hte.
  + move=> i hte. case: s hte=> //=. 
    + exists (Values.Vint (Int.not i)). 
      rewrite /trans_cvalue_bvalue /=. by exists (Vint (Int.not i)).
      exists (Values.Vint (Int.not i)). 
      rewrite /trans_cvalue_bvalue /=. by exists (Vint (Int.not i)).
    + move=> i hte. by inversion hte.
    + move=> p i hte. by inversion hte.
  move=> o hte. by inversion hte.
(* long *)
move=> s a. case: v=> //=.
+ move=> hte. by inversion hte.
+ move=> b hte. by inversion hte.
+ move=> i hte _. by inversion hte.
+ move=> i hte. rewrite /Cop.sem_notint /=. 
  exists (Values.Vlong (Int64.not i)). rewrite /trans_cvalue_bvalue /=.
  by exists (Vint64 (Int64.not i)).
+ move=> p i hte. by inversion hte.
move=> o hte. by inversion hte.
Qed.
  
(* neg is well-formed *) 
Lemma well_formed_neg : forall cenv Gamma Sigma bge vm m v t ef,
store_well_typed cenv Gamma Sigma bge vm m ->
type_expr cenv Gamma Sigma (Val v t) ef t ->
is_primint t || is_primlong t ->
exists v' v'',
Cop.sem_unary_operation (Cop.Oneg) (trans_bvalue_cvalue v) (transBeePL_type t) m = Some v' /\
v' <> Values.Vundef /\
trans_cvalue_bvalue v' = OK v''.
Proof.
move=> cenv Gamma Sigma bge vm m v t ef hw hte heq.
case: t hte heq=> //= p; case: p=> //=.
(* int *)
+ move=> sz s a hte _. case: v hte=> //=.
  + move=> hte. by inversion hte.
  + move=> b hte. by inversion hte.
  + move=> i hte. rewrite /Cop.sem_neg /=.
    case: sz hte=> //=.
    (* I8 *)
    + exists (Values.Vint (Int.neg i)). rewrite /trans_cvalue_bvalue.
      by exists (Vint (Int.neg i)).
    (* I16 *)
    + exists (Values.Vint (Int.neg i)). rewrite /trans_cvalue_bvalue.
      by exists (Vint (Int.neg i)).
   (* I32 *)
    + exists (Values.Vint (Int.neg i)). rewrite /trans_cvalue_bvalue.
      case: s hte=> //=;by exists (Vint (Int.neg i)).
    move=> hte. exists (Values.Vint (Int.neg i)).
    rewrite /trans_cvalue_bvalue. by exists (Vint (Int.neg i)).
  (* I64 *)
  + move=> i hte. by inversion hte.
  + move=> l o hte. by inversion hte.
  + move=> o hte. by inversion hte.
move=> s a. rewrite /Cop.sem_neg /=.
case: v=> //=.
+ move=> hte. by inversion hte.
+ move=> b hte. by inversion hte.
+ move=> i hte. by inversion hte.
+ move=> i hte _. exists (Values.Vlong (Int64.neg i)).
  rewrite /trans_cvalue_bvalue. by exists (Vint64 (Int64.neg i)).
+ move=> p i hte. by inversion hte.
move=> o hte. by inversion hte.
Qed.   

(* add is well-formed *) 
Lemma well_formed_add : forall cenv benv Gamma Sigma bge vm m v1 t ef1 v2 ef2,
store_well_typed benv Gamma Sigma bge vm m ->
type_expr benv Gamma Sigma (Val v1 t) ef1 t ->
type_expr benv Gamma Sigma (Val v2 t) ef2 t ->
is_primint t || is_primlong t ->
exists v' v'',
Cop.sem_binary_operation cenv Cop.Oadd (trans_bvalue_cvalue v1) (transBeePL_type t) 
      (trans_bvalue_cvalue v2) (transBeePL_type t) m = Some v' /\
v' <> Values.Vundef /\
trans_cvalue_bvalue v' = OK v''.
Proof.
move=> cnev benv Gamma Sigma bge vm m v1 t ef1 v2 ef2 hw ht1 ht2 hteq.
case: t ht1 ht2 hteq=> //= p; case: p=> //= sz s a.
(* int *)
+ move=> ht1 ht2 _. case: v1 ht1=> //=.
  + move=> ht1. by inversion ht1.
  + move=> b ht1. by inversion ht1.
  + move=> i ht1. case: v2 ht2=> //=.
    + move=> ht2. by inversion ht2.
    + move=> b ht2. by inversion ht2.
    + move=> i' ht3. rewrite /Cop.sem_add /Cop.classify_add /=.
      case: sz ht1 ht3=>//=.
      + rewrite /Cop.sem_binarith /= /Cop.sem_cast /=. case: Archi.ptr64=> //= hp.
        + exists (Values.Vint (Int.add i i')). rewrite /trans_cvalue_bvalue /=.
          by exists (Vint (Int.add i i')).
        case: (intsize_eq I32 I32)=> //= _. exists (Values.Vint (Int.add i i')). 
        rewrite /trans_cvalue_bvalue /=. by exists (Vint (Int.add i i')).
      + rewrite /Cop.sem_binarith /= /Cop.sem_cast /=. case: Archi.ptr64=> //= hp.
        + exists (Values.Vint (Int.add i i')). rewrite /trans_cvalue_bvalue /=.
          by exists (Vint (Int.add i i')).
        case: (intsize_eq I32 I32)=> //= _. exists (Values.Vint (Int.add i i')). 
        rewrite /trans_cvalue_bvalue /=. by exists (Vint (Int.add i i')).
      + rewrite /Cop.sem_binarith /= /Cop.sem_cast /= /Cop.classify_cast /=. 
        case: s=> //=.
        + case: Archi.ptr64=> //= hp.
          + exists (Values.Vint (Int.add i i')). rewrite /trans_cvalue_bvalue /=.
            by exists (Vint (Int.add i i')).
          case: (intsize_eq I32 I32)=> //= _. exists (Values.Vint (Int.add i i')). 
          rewrite /trans_cvalue_bvalue /=. by exists (Vint (Int.add i i')).
        case: Archi.ptr64=> //= hp.
        + exists (Values.Vint (Int.add i i')). rewrite /trans_cvalue_bvalue /=.
          by exists (Vint (Int.add i i')).
        case: (intsize_eq I32 I32)=> //= _. exists (Values.Vint (Int.add i i')). 
        rewrite /trans_cvalue_bvalue /=. by exists (Vint (Int.add i i')).
      rewrite /Cop.sem_binarith /= /Cop.sem_cast /=. case: Archi.ptr64=> //= hp.
      + exists (Values.Vint (Int.add i i')). rewrite /trans_cvalue_bvalue /=.
        by exists (Vint (Int.add i i')).
      case: (intsize_eq I32 I32)=> //= _. exists (Values.Vint (Int.add i i')). 
      rewrite /trans_cvalue_bvalue /=. by exists (Vint (Int.add i i')).
   + move=> i' ht3. by inversion ht3. 
   + move=> p ofs ht3. by inversion ht3.
   + move=> o ht3. by inversion ht3.
   + move=> l ht3. by inversion ht3.
   + move=> l o ht3. by inversion ht3.
(* long *)
(*+ move=> ht1 ht2 _. case: v1 ht1=> //=.
  + move=> ht1. by inversion ht1.
  + move=> b ht1. by inversion ht1.
  + move=> i ht1. case: v2 ht2=> //=.
    + move=> ht2. by inversion ht2.
    + move=> b ht2. by inversion ht2.
    + move=> i' ht3. rewrite /Cop.sem_add /Cop.classify_add /=.
      case: sz ht1 ht3=>//=.
      + rewrite /Cop.sem_binarith /= /Cop.sem_cast /=. case: Archi.ptr64=> //= hp.
        + exists (Values.Vint (Int.add i i')). rewrite /trans_cvalue_bvalue /=.
          by exists (Vint (Int.add i i')).
        case: (intsize_eq I32 I32)=> //= _. exists (Values.Vint (Int.add i i')). 
        rewrite /trans_cvalue_bvalue /=. by exists (Vint (Int.add i i')).
      + rewrite /Cop.sem_binarith /= /Cop.sem_cast /=. case: Archi.ptr64=> //= hp.
        + exists (Values.Vint (Int.add i i')). rewrite /trans_cvalue_bvalue /=.
          by exists (Vint (Int.add i i')).
        case: (intsize_eq I32 I32)=> //= _. exists (Values.Vint (Int.add i i')). 
        rewrite /trans_cvalue_bvalue /=. by exists (Vint (Int.add i i')).
      + rewrite /Cop.sem_binarith /= /Cop.sem_cast /= /Cop.classify_cast /=. 
        case: s=> //=.
        + case: Archi.ptr64=> //= hp.
          + exists (Values.Vint (Int.add i i')). rewrite /trans_cvalue_bvalue /=.
            by exists (Vint (Int.add i i')).
          case: (intsize_eq I32 I32)=> //= _. exists (Values.Vint (Int.add i i')). 
          rewrite /trans_cvalue_bvalue /=. by exists (Vint (Int.add i i')).
        case: Archi.ptr64=> //= hp.
        + exists (Values.Vint (Int.add i i')). rewrite /trans_cvalue_bvalue /=.
          by exists (Vint (Int.add i i')).
        case: (intsize_eq I32 I32)=> //= _. exists (Values.Vint (Int.add i i')). 
        rewrite /trans_cvalue_bvalue /=. by exists (Vint (Int.add i i')).
      rewrite /Cop.sem_binarith /= /Cop.sem_cast /=. case: Archi.ptr64=> //= hp.
      + exists (Values.Vint (Int.add i i')). rewrite /trans_cvalue_bvalue /=.
        by exists (Vint (Int.add i i')).
      case: (intsize_eq I32 I32)=> //= _. exists (Values.Vint (Int.add i i')). 
      rewrite /trans_cvalue_bvalue /=. by exists (Vint (Int.add i i')).
   + move=> i' ht3. by inversion ht3. 
   + move=> p ofs ht3. by inversion ht3.
   + move=> o ht3. by inversion ht3.
   + move=> l ht3. by inversion ht3.
   move=> l o ht3. by inversion ht3.*)
Admitted.


 
