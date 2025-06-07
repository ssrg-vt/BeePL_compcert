Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import compcert.common.Errors Initializersproof Cstrategy BeePL_auxlemmas Coqlib Errors Memory.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import BeePL_sem BeePL_typesystem BeePL_compiler_proofs BeePL_values BeePL_notations.

From mathcomp Require Import all_ssreflect.

Lemma signedness_exists : forall t,
is_primint t || is_primlong t ->
exists s, signedness_of_type t = Some s.
Proof.
move=> [] //= p. case: p=> //=.
+ move=> sz a _ _. by exists a.
move=> s _ _. by exists s.
Qed.

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
    + move=> b hte. 
by inversion hte.
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
   move=> l o ht3. by inversion ht3.
  move=> o hto. by inversion hto.
(* long *)
+ case: v1 a=> //=.
  + move=> hte. by inversion hte.
  + move=> b hte. by inversion hte.
  + move=> i hte. by inversion hte.
  + move=> l hte. case: v2=> //=.
    + move=> hte'. by inversion hte'.
    + move=> b' hte'. by inversion hte'.
    + move=> i' hte'. by inversion hte'.
    + move=> l' hte' _. rewrite /Cop.sem_add /= /Cop.sem_binarith /= /Cop.sem_cast /=.
      case: sz hte hte'=> //=.
      + case: Archi.ptr64=> //= hp.
        + move=>hte'. exists (Values.Vlong (Int64.add l l')). 
          rewrite /trans_cvalue_bvalue /=. by exists (Vint64 (Int64.add l l')).
        move=>hte'. exists (Values.Vlong (Int64.add l l')). 
        rewrite /trans_cvalue_bvalue /=. by exists (Vint64 (Int64.add l l')).
      case: Archi.ptr64=> //= hp.
      + move=>hte'. exists (Values.Vlong (Int64.add l l')). 
        rewrite /trans_cvalue_bvalue /=. by exists (Vint64 (Int64.add l l')).
      move=>hte'. exists (Values.Vlong (Int64.add l l')). 
      rewrite /trans_cvalue_bvalue /=. by exists (Vint64 (Int64.add l l')).
    + move=> p i hte'. by inversion hte'.
    move=> o hte'. by inversion hte'.
  + move=> p i hte hte'. by inversion hte.
move=> o hte hte'. by inversion hte.
Qed.

(* sub is well-formed *) 
Lemma well_formed_sub : forall cenv benv Gamma Sigma bge vm m v1 t ef1 v2 ef2,
store_well_typed benv Gamma Sigma bge vm m ->
type_expr benv Gamma Sigma (Val v1 t) ef1 t ->
type_expr benv Gamma Sigma (Val v2 t) ef2 t ->
is_primint t || is_primlong t ->
exists v' v'',
Cop.sem_binary_operation cenv Cop.Osub (trans_bvalue_cvalue v1) (transBeePL_type t) 
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
    + move=> i' ht3. rewrite /Cop.sem_sub /Cop.classify_sub /=.
      case: sz ht1 ht3=>//=.
      + rewrite /Cop.sem_binarith /= /Cop.sem_cast /=. case: Archi.ptr64=> //= hp.
        + exists (Values.Vint (Int.sub i i')). rewrite /trans_cvalue_bvalue /=.
          by exists (Vint (Int.sub i i')).
        case: (intsize_eq I32 I32)=> //= _. exists (Values.Vint (Int.sub i i')). 
        rewrite /trans_cvalue_bvalue /=. by exists (Vint (Int.sub i i')).
      + rewrite /Cop.sem_binarith /= /Cop.sem_cast /=. case: Archi.ptr64=> //= hp.
        + exists (Values.Vint (Int.sub i i')). rewrite /trans_cvalue_bvalue /=.
          by exists (Vint (Int.sub i i')).
        case: (intsize_eq I32 I32)=> //= _. exists (Values.Vint (Int.sub i i')). 
        rewrite /trans_cvalue_bvalue /=. by exists (Vint (Int.sub i i')).
      + rewrite /Cop.sem_binarith /= /Cop.sem_cast /= /Cop.classify_cast /=. 
        case: s=> //=.
        + case: Archi.ptr64=> //= hp.
          + exists (Values.Vint (Int.sub i i')). rewrite /trans_cvalue_bvalue /=.
            by exists (Vint (Int.sub i i')).
          case: (intsize_eq I32 I32)=> //= _. exists (Values.Vint (Int.sub i i')). 
          rewrite /trans_cvalue_bvalue /=. by exists (Vint (Int.sub i i')).
        case: Archi.ptr64=> //= hp.
        + exists (Values.Vint (Int.sub i i')). rewrite /trans_cvalue_bvalue /=.
          by exists (Vint (Int.sub i i')).
        case: (intsize_eq I32 I32)=> //= _. exists (Values.Vint (Int.sub i i')). 
        rewrite /trans_cvalue_bvalue /=. by exists (Vint (Int.sub i i')).
      rewrite /Cop.sem_binarith /= /Cop.sem_cast /=. case: Archi.ptr64=> //= hp.
      + exists (Values.Vint (Int.sub i i')). rewrite /trans_cvalue_bvalue /=.
        by exists (Vint (Int.sub i i')).
      case: (intsize_eq I32 I32)=> //= _. exists (Values.Vint (Int.sub i i')). 
      rewrite /trans_cvalue_bvalue /=. by exists (Vint (Int.sub i i')).
   + move=> i' ht3. by inversion ht3. 
   + move=> p ofs ht3. by inversion ht3.
   + move=> o ht3. by inversion ht3.
   + move=> l ht3. by inversion ht3.
   move=> l o ht3. by inversion ht3.
  move=> o hto. by inversion hto.
(* long *)
+ case: v1 a=> //=.
  + move=> hte. by inversion hte.
  + move=> b hte. by inversion hte.
  + move=> i hte. by inversion hte.
  + move=> l hte. case: v2=> //=.
    + move=> hte'. by inversion hte'.
    + move=> b' hte'. by inversion hte'.
    + move=> i' hte'. by inversion hte'.
    + move=> l' hte' _. rewrite /Cop.sem_sub /= /Cop.sem_binarith /= /Cop.sem_cast /=.
      case: sz hte hte'=> //=.
      + case: Archi.ptr64=> //= hp.
        + move=>hte'. exists (Values.Vlong (Int64.sub l l')). 
          rewrite /trans_cvalue_bvalue /=. by exists (Vint64 (Int64.sub l l')).
        move=>hte'. exists (Values.Vlong (Int64.sub l l')). 
        rewrite /trans_cvalue_bvalue /=. by exists (Vint64 (Int64.sub l l')).
      case: Archi.ptr64=> //= hp.
      + move=>hte'. exists (Values.Vlong (Int64.sub l l')). 
        rewrite /trans_cvalue_bvalue /=. by exists (Vint64 (Int64.sub l l')).
      move=>hte'. exists (Values.Vlong (Int64.sub l l')). 
      rewrite /trans_cvalue_bvalue /=. by exists (Vint64 (Int64.sub l l')).
    + move=> p i hte'. by inversion hte'.
    move=> o hte'. by inversion hte'.
  + move=> p i hte hte'. by inversion hte.
move=> o hte hte'. by inversion hte.
Qed.
        
(* mult is well-formed *) 
Lemma well_formed_mul : forall cenv benv Gamma Sigma bge vm m v1 t ef1 v2 ef2,
store_well_typed benv Gamma Sigma bge vm m ->
type_expr benv Gamma Sigma (Val v1 t) ef1 t ->
type_expr benv Gamma Sigma (Val v2 t) ef2 t ->
is_primint t || is_primlong t ->
exists v' v'',
Cop.sem_binary_operation cenv Cop.Omul (trans_bvalue_cvalue v1) (transBeePL_type t) 
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
    + move=> i' ht3. rewrite /Cop.sem_sub /Cop.classify_sub /=.
      case: sz ht1 ht3=>//=.
      + rewrite /Cop.sem_binarith /= /Cop.sem_cast /=. case: Archi.ptr64=> //= hp.
        + exists (Values.Vint (Int.mul i i')). rewrite /trans_cvalue_bvalue /=.
          by exists (Vint (Int.mul i i')).
        case: (intsize_eq I32 I32)=> //= _. exists (Values.Vint (Int.mul i i')). 
        rewrite /trans_cvalue_bvalue /=. by exists (Vint (Int.mul i i')).
      + rewrite /Cop.sem_binarith /= /Cop.sem_cast /=. case: Archi.ptr64=> //= hp.
        + exists (Values.Vint (Int.mul i i')). rewrite /trans_cvalue_bvalue /=.
          by exists (Vint (Int.mul i i')).
        case: (intsize_eq I32 I32)=> //= _. exists (Values.Vint (Int.mul i i')). 
        rewrite /trans_cvalue_bvalue /=. by exists (Vint (Int.mul i i')).
      + rewrite /Cop.sem_binarith /= /Cop.sem_cast /= /Cop.classify_cast /=. 
        case: s=> //=.
        + case: Archi.ptr64=> //= hp.
          + exists (Values.Vint (Int.mul i i')). rewrite /trans_cvalue_bvalue /=.
            by exists (Vint (Int.mul i i')).
          case: (intsize_eq I32 I32)=> //= _. exists (Values.Vint (Int.mul i i')). 
          rewrite /trans_cvalue_bvalue /=. by exists (Vint (Int.mul i i')).
        case: Archi.ptr64=> //= hp.
        + exists (Values.Vint (Int.mul i i')). rewrite /trans_cvalue_bvalue /=.
          by exists (Vint (Int.mul i i')).
        case: (intsize_eq I32 I32)=> //= _. exists (Values.Vint (Int.mul i i')). 
        rewrite /trans_cvalue_bvalue /=. by exists (Vint (Int.mul i i')).
      rewrite /Cop.sem_binarith /= /Cop.sem_cast /=. case: Archi.ptr64=> //= hp.
      + exists (Values.Vint (Int.mul i i')). rewrite /trans_cvalue_bvalue /=.
        by exists (Vint (Int.mul i i')).
      case: (intsize_eq I32 I32)=> //= _. exists (Values.Vint (Int.mul i i')). 
      rewrite /trans_cvalue_bvalue /=. by exists (Vint (Int.mul i i')).
   + move=> i' ht3. by inversion ht3. 
   + move=> p ofs ht3. by inversion ht3.
   + move=> o ht3. by inversion ht3.
   + move=> l ht3. by inversion ht3.
   move=> l o ht3. by inversion ht3.
  move=> o hto. by inversion hto.
(* long *)
+ case: v1 a=> //=.
  + move=> hte. by inversion hte.
  + move=> b hte. by inversion hte.
  + move=> i hte. by inversion hte.
  + move=> l hte. case: v2=> //=.
    + move=> hte'. by inversion hte'.
    + move=> b' hte'. by inversion hte'.
    + move=> i' hte'. by inversion hte'.
    + move=> l' hte' _. rewrite /Cop.sem_sub /= /Cop.sem_binarith /= /Cop.sem_cast /=.
      case: sz hte hte'=> //=.
      + case: Archi.ptr64=> //= hp.
        + move=>hte'. exists (Values.Vlong (Int64.mul l l')). 
          rewrite /trans_cvalue_bvalue /=. by exists (Vint64 (Int64.mul l l')).
        move=>hte'. exists (Values.Vlong (Int64.mul l l')). 
        rewrite /trans_cvalue_bvalue /=. by exists (Vint64 (Int64.mul l l')).
      case: Archi.ptr64=> //= hp.
      + move=>hte'. exists (Values.Vlong (Int64.mul l l')). 
        rewrite /trans_cvalue_bvalue /=. by exists (Vint64 (Int64.mul l l')).
      move=>hte'. exists (Values.Vlong (Int64.mul l l')). 
      rewrite /trans_cvalue_bvalue /=. by exists (Vint64 (Int64.mul l l')).
    + move=> p i hte'. by inversion hte'.
    move=> o hte'. by inversion hte'.
  + move=> p i hte hte'. by inversion hte.
move=> o hte hte'. by inversion hte.
Qed.

Lemma construct_zero : forall t,
is_primint t || is_primlong t ->
exists zv, return_bzero t = ret zv. 
Proof.
move=> t ht. rewrite /return_bzero /=. case: t ht=> //= p.
case: p=> //=.
+ move=> sz s a _. by exists (Vint (Int.repr 0)).
move=> s a _. by exists (Vint64 (Int64.repr 0)).
Qed.

(* int range *)
Lemma int_range_invalid: forall benv Gamma Sigma i sz a ef,
type_expr benv Gamma Sigma (Val (Vint i) (Vtype (Tint sz Unsigned a))) ef (Vtype (Tint sz Unsigned a)) ->  
negb (Int.eq i (Int.repr Int.min_signed)). 
Proof.
Admitted.

(* div is well-formed *) (* make the proof small using ltac latter *)
Lemma well_formed_div : forall cenv benv Gamma Sigma bge vm m v1 t ef1 v2 ef2 s,
store_well_typed benv Gamma Sigma bge vm m ->
type_expr benv Gamma Sigma (Val v1 t) ef1 t ->
type_expr benv Gamma Sigma (Val v2 t) ef2 t ->
is_primint t || is_primlong t ->
signedness_of_type t = Some s ->
check_unsafe_op Cop.Odiv s v1 v2 = false ->
exists v' v'',
Cop.sem_binary_operation cenv Cop.Odiv (trans_bvalue_cvalue v1) (transBeePL_type t) 
      (trans_bvalue_cvalue v2) (transBeePL_type t) m = Some v' /\
v' <> Values.Vundef /\
trans_cvalue_bvalue v' = OK v''.
Proof.
move=> cnev benv Gamma Sigma bge vm m v1 t ef1 v2 ef2 s hw ht1 ht2 hteq hs hc.
case: s hs hc=> //=.
(* signed *)
+ case: t ht1 ht2 hteq=> //= p; case: p=> //=.
  (* int *)
  + move=> sz s a ht1 ht2 _ [] h1; subst. case: ifP=> //= h.
    case: sz ht1 ht2=> //=.
    (* I8 *)
    + rewrite /Cop.sem_div /Cop.sem_binarith /= /Cop.sem_cast /Cop.classify_cast /=.
      case: Archi.ptr64=> //=.
      + case: v1 h=> //=.
        + move=> _ ht. by inversion ht.
        + move=> b _ ht. by inversion ht. 
        + move=> i. case: v2=> //=.
          + move=> _ _ ht; by inversion ht.
          + move=> b _ _ ht; inversion ht.
          + move=> i1. case: ifP=> //= hi. case: ifP=> //= hi' _ ht1 ht2.
            exists (Values.Vint (Int.divs i i1)). rewrite / trans_cvalue_bvalue /=.  
            by exists (Vint (Int.divs i i1)).
          + move=> i' _ _ ht; by inversion ht.
          + move=> p o _ _ ht; by inversion ht.
          move=>  o _ _ ht; by inversion ht.
      + move=> i. case: v2=> //=.
        + move=> _ ht; by inversion ht.
        + move=> b _ ht. by inversion ht.
        + move=> i' _ ht; by inversion ht.
        + move=> i' _ ht; by inversion ht.
        + move=> p o _ ht; by inversion ht.
        move=> o _ ht; by inversion ht.
      move=> p i _ ht; by inversion ht.
     move=> o _ ht; by inversion ht.
    case: (intsize_eq I32 I32)=> //=.
    case: v1 h=> //=.
    + move=> _ _ ht; by inversion ht.
    + move=> b _ _ ht; by inversion ht.
    + case: v2=> //=.
      + move=> i _ _ _ ht; by inversion ht.
      + move=> b i _ _ _ ht; by inversion ht.
      + move=> i i'. case: ifP=> //= hi. case: ifP=> //= hi' _ _ ht1 ht2 _.
        exists (Values.Vint (Int.divs i' i)). rewrite / trans_cvalue_bvalue /=.  
        by exists (Vint (Int.divs i' i)).
      + move=> i i' _ _ _ ht; by inversion ht.
      + move=> p i i' _ _ _ ht; by inversion ht.
      + move=> o i _ _ _ ht; by inversion ht.
    + move=> i _ _ ht; by inversion ht.
    + move=> p i _ _ ht; by inversion ht.
    + move=> o _ _ ht; by inversion ht.
   (* I16 *)
    + rewrite /Cop.sem_div /Cop.sem_binarith /= /Cop.sem_cast /Cop.classify_cast /=.
      case: Archi.ptr64=> //=.
      + case: v1 h=> //=.
        + move=> _ ht. by inversion ht.
        + move=> b _ ht. by inversion ht. 
        + move=> i. case: v2=> //=.
          + move=> _ _ ht; by inversion ht.
          + move=> b _ _ ht; inversion ht.
          + move=> i'. case: ifP=> //= h; case: ifP=> //= h' _ ht1 ht2 _.
            exists (Values.Vint (Int.divs i i')). rewrite /trans_cvalue_bvalue.
            by exists (Vint (Int.divs i i')).
          + move=> i' _ _ ht; by inversion ht.
          + move=> p o _ _ ht; by inversion ht.
          move=>  o _ _ ht; by inversion ht.
      + move=> i. case: v2=> //=.
        + move=> _ ht; by inversion ht.
        + move=> b _ ht. by inversion ht.
        + move=> i' _ ht; by inversion ht.
        + move=> i' _ ht; by inversion ht.
        + move=> p o _ ht; by inversion ht.
        move=> o _ ht; by inversion ht.
      move=> p i _ ht; by inversion ht.
     move=> o _ ht; by inversion ht.
    case: (intsize_eq I32 I32)=> //=.
    case: v1 h=> //=.
    + move=> _ _ ht; by inversion ht.
    + move=> b _ _ ht; by inversion ht.
    + case: v2=> //=.
      + move=> i _ _ _ ht; by inversion ht.
      + move=> b i _ _ _ ht; by inversion ht.
      + move=> i i'. case: ifP=> //= hi. case: ifP=> //= hi' _ _ ht1 ht2 _.
        exists (Values.Vint (Int.divs i' i)). rewrite / trans_cvalue_bvalue /=.  
        by exists (Vint (Int.divs i' i)).
      + move=> i i' _ _ _ ht; by inversion ht.
      + move=> p i i' _ _ _ ht; by inversion ht.
      + move=> o i _ _ _ ht; by inversion ht.
    + move=> i _ _ ht; by inversion ht.
    + move=> p i _ _ ht; by inversion ht.
    move=> o _ _ ht; by inversion ht.
  (* I32 *)
    + rewrite /Cop.sem_div /Cop.sem_binarith /= /Cop.sem_cast /Cop.classify_cast /=.
      case: Archi.ptr64=> //=.
      + case: v1 h=> //=.
        + move=> _ ht. by inversion ht.
        + move=> b _ ht. by inversion ht. 
        + move=> i. case: v2=> //=.
          + move=> _ _ ht; by inversion ht.
          + move=> b _ _ ht; inversion ht.
          + move=> i'. case: ifP=> //= h; case: ifP=> //= h' _ ht1 ht2 _.
            exists (Values.Vint (Int.divs i i')). rewrite /trans_cvalue_bvalue.
            by exists (Vint (Int.divs i i')).
          + move=> i' _ _ ht; by inversion ht.
          + move=> p o _ _ ht; by inversion ht.
          move=>  o _ _ ht; by inversion ht.
      + move=> i. case: v2=> //=.
        + move=> _ ht; by inversion ht.
        + move=> b _ ht. by inversion ht.
        + move=> i' _ ht; by inversion ht.
        + move=> i' _ ht; by inversion ht.
        + move=> p o _ ht; by inversion ht.
        move=> o _ ht; by inversion ht.
      move=> p i _ ht; by inversion ht.
     move=> o _ ht; by inversion ht.
    case: (intsize_eq I32 I32)=> //=.
    case: v1 h=> //=.
    + move=> _ _ ht; by inversion ht.
    + move=> b _ _ ht; by inversion ht.
    + case: v2=> //=.
      + move=> i _ _ _ ht; by inversion ht.
      + move=> b i _ _ _ ht; by inversion ht.
      + move=> i i'. case: ifP=> //= hi. case: ifP=> //= hi' _ _ ht1 ht2 _.
        exists (Values.Vint (Int.divs i' i)). rewrite / trans_cvalue_bvalue /=.  
        by exists (Vint (Int.divs i' i)).
      + move=> i i' _ _ _ ht; by inversion ht.
      + move=> p i i' _ _ _ ht; by inversion ht.
      + move=> o i _ _ _ ht; by inversion ht.
    + move=> i _ _ ht; by inversion ht.
    + move=> p i _ _ ht; by inversion ht.
    move=> o _ _ ht; by inversion ht.
  (* IBool *)
  rewrite /Cop.sem_div /Cop.sem_binarith /= /Cop.sem_cast /Cop.classify_cast /=.
  case: Archi.ptr64=> //=.
  + case: v1 h=> //=.
    + move=> _ ht. by inversion ht.
    + move=> b _ ht. by inversion ht. 
      + move=> i. case: v2=> //=.
        + move=> _ _ ht; by inversion ht.
        + move=> b _ _ ht; inversion ht.
        + move=> i'. case: ifP=> //= h; case: ifP=> //= h' _ ht1 ht2 _.
            exists (Values.Vint (Int.divs i i')). rewrite /trans_cvalue_bvalue.
            by exists (Vint (Int.divs i i')).
          + move=> i' _ _ ht; by inversion ht.
          + move=> p o _ _ ht; by inversion ht.
          move=>  o _ _ ht; by inversion ht.
      + move=> i. case: v2=> //=.
        + move=> _ ht; by inversion ht.
        + move=> b _ ht. by inversion ht.
        + move=> i' _ ht; by inversion ht.
        + move=> i' _ ht; by inversion ht.
        + move=> p o _ ht; by inversion ht.
        move=> o _ ht; by inversion ht.
      move=> p i _ ht; by inversion ht.
     move=> o _ ht; by inversion ht.
    case: (intsize_eq I32 I32)=> //=.
    case: v1 h=> //=.
    + move=> _ _ ht; by inversion ht.
    + move=> b _ _ ht; by inversion ht.
    + case: v2=> //=.
      + move=> i _ _ _ ht; by inversion ht.
      + move=> b i _ _ _ ht; by inversion ht.
      + move=> i i'. case: ifP=> //= hi. case: ifP=> //= hi' _ _ ht1 ht2 _.
        exists (Values.Vint (Int.divs i' i)). rewrite / trans_cvalue_bvalue /=.  
        by exists (Vint (Int.divs i' i)).
      + move=> i i' _ _ _ ht; by inversion ht.
      + move=> p i i' _ _ _ ht; by inversion ht.
      + move=> o i _ _ _ ht; by inversion ht.
    + move=> i _ _ ht; by inversion ht.
    + move=> p i _ _ ht; by inversion ht.
    move=> o _ _ ht; by inversion ht.
(* long *)
+ move=> s. case: s=> //= a.
  case: v1=> //=.
  + by move=> ht; inversion ht.
  + by move=> b ht; inversion ht.
  + case: v2=> //=.
    + by move=>  i _ ht; inversion ht.
    + by move=> b i _ ht; inversion ht.
    + by move=> i i' ht; inversion ht.
    + by move=> i i' ht; inversion ht.
    + by move=> p o i' _ ht; inversion ht.
    + by move=> o i ht; inversion ht.
    case: v2=> //=.
    + by move=> i _ ht; inversion ht.
    + by move=> b i _ ht; inversion ht.
    + by move=> i i' _ ht; inversion ht.
    + move=> i1 i2 ht1 ht2 _ _. case: ifP=> //=.
      case: ifP=> //=. case: ifP=> //= h1 h2 _ _.
      rewrite /Cop.sem_div /Cop.sem_binarith /Cop.sem_cast /=.
      case: Archi.ptr64=> //=.
      + rewrite h2 /= h1 /=. exists (Values.Vlong (Int64.divs i2 i1)).
        rewrite /trans_cvalue_bvalue /=. by exists  (Vint64 (Int64.divs i2 i1)).
      rewrite h2 /= h1 /=. exists (Values.Vlong (Int64.divs i2 i1)).
      rewrite /trans_cvalue_bvalue /=. by exists  (Vint64 (Int64.divs i2 i1)).
    + by move=> p o i' _ ht; inversion ht.
    + by move=> o i _ ht; inversion ht.
    by move=> l o ht; inversion ht.
  by move=> o ht; inversion ht.
(* unsigned *)
+ case: t ht1 ht2 hteq=> //= p; case: p=> //=.
  (* int *)
  + move=> sz s a. case: s=> //=. case: sz=> //=.
    + case: v2=> //=.
      + move=> _ ht; by inversion ht.
      + move=> b _ ht; by inversion ht.
      + move=> i h1 h2 _ _. case: ifP=> //= hi _.
        rewrite /Cop.sem_div /= /Cop.sem_binarith /Cop.sem_cast /=.
        case: ifP=> //= h. + by rewrite h in hi.
        case: Archi.ptr64=> //=. case: v1 h1=> //=.
        + move=> ht; by inversion ht.
        + move=> b ht; by inversion ht.
        + move=> i' ht /=. rewrite hi /=.
          have hn := int_range_invalid benv Gamma Sigma i' I8 a ef1 ht.
          rewrite /negb in hn. move: hn. case: ifP=> //= hn _. 
          exists (Values.Vint (Int.divs i' i)). rewrite /trans_cvalue_bvalue /=.
          by exists (Vint (Int.divs i' i)).
        + move=> i' ht; by inversion ht.
        + move=> l o ht; by inversion ht.
      move=> o ht; by inversion ht.
  + case: (intsize_eq I32 I32)=> //= _. case: v1 h1=> //=.
    + move=> h1. by inversion h1.
    + move=> b ht; by inversion ht.
    + move=> i' ht. rewrite hi /=.
      have hn := int_range_invalid benv Gamma Sigma i' I8 a ef1 ht.
      rewrite /negb in hn. move: hn. case: ifP=> //= hn _. 
      exists (Values.Vint (Int.divs i' i)). rewrite /trans_cvalue_bvalue /=.
      by exists (Vint (Int.divs i' i)).
    + move=> i' ht; by inversion ht.
    + move=> l o ht; by inversion ht.
    move=> o ht; by inversion ht.
  + move=> i' _ ht; by inversion ht.
  + move=> l o _ ht; by inversion ht.
  move=> o _ ht; by inversion ht.
 +  + case: v2=> //=.
      + move=> _ ht; by inversion ht.
      + move=> b _ ht; by inversion ht.
      + move=> i h1 h2 _ _. case: ifP=> //= hi _.
        rewrite /Cop.sem_div /= /Cop.sem_binarith /Cop.sem_cast /=.
        case: ifP=> //= h. + by rewrite h in hi.
        case: Archi.ptr64=> //=. case: v1 h1=> //=.
        + move=> ht; by inversion ht.
        + move=> b ht; by inversion ht.
        + move=> i' ht /=. rewrite hi /=.
          have hn := int_range_invalid benv Gamma Sigma i' I16 a ef1 ht.
          rewrite /negb in hn. move: hn. case: ifP=> //= hn _. 
          exists (Values.Vint (Int.divs i' i)). rewrite /trans_cvalue_bvalue /=.
          by exists (Vint (Int.divs i' i)).
        + move=> i' ht; by inversion ht.
        + move=> l o ht; by inversion ht.
      move=> o ht; by inversion ht.
  + case: (intsize_eq I32 I32)=> //= _. case: v1 h1=> //=.
    + move=> h1. by inversion h1.
    + move=> b ht; by inversion ht.
    + move=> i' ht. rewrite hi /=.
      have hn := int_range_invalid benv Gamma Sigma i' I16 a ef1 ht.
      rewrite /negb in hn. move: hn. case: ifP=> //= hn _. 
      exists (Values.Vint (Int.divs i' i)). rewrite /trans_cvalue_bvalue /=.
      by exists (Vint (Int.divs i' i)).
    + move=> i' ht; by inversion ht.
    + move=> l o ht; by inversion ht.
    move=> o ht; by inversion ht.
  + move=> i' _ ht; by inversion ht.
  + move=> l o _ ht; by inversion ht.
  move=> o _ ht; by inversion ht.
  + case: v2=> //=.
      + move=> _ ht; by inversion ht.
      + move=> b _ ht; by inversion ht.
      + move=> i h1 h2 _ _. case: ifP=> //= hi _.
        rewrite /Cop.sem_div /= /Cop.sem_binarith /Cop.sem_cast /=.
        case: ifP=> //= h. + by rewrite h in hi.
        case: Archi.ptr64=> //=. case: v1 h1=> //=.
        + move=> ht; by inversion ht.
        + move=> b ht; by inversion ht.
        + move=> i' ht /=. rewrite hi /=.
          exists (Values.Vint (Int.divu i' i)). rewrite /trans_cvalue_bvalue /=.
          by exists (Vint (Int.divu i' i)).
        + move=> i' ht; by inversion ht.
        + move=> l o ht; by inversion ht.
      move=> o ht; by inversion ht.
  + case: (intsize_eq I32 I32)=> //= _. case: v1 h1=> //=.
    + move=> h1. by inversion h1.
    + move=> b ht; by inversion ht.
    + move=> i' ht. rewrite hi /=.
      exists (Values.Vint (Int.divu i' i)). rewrite /trans_cvalue_bvalue /=.
      by exists (Vint (Int.divu i' i)).
    + move=> i' ht; by inversion ht.
    + move=> l o ht; by inversion ht.
    move=> o ht; by inversion ht.
  + move=> i' _ ht; by inversion ht.
  + move=> l o _ ht; by inversion ht.
  move=> o _ ht; by inversion ht.
  + case: v2=> //=.
      + move=> _ ht; by inversion ht.
      + move=> b _ ht; by inversion ht.
      + move=> i h1 h2 _ _. case: ifP=> //= hi _.
        rewrite /Cop.sem_div /= /Cop.sem_binarith /Cop.sem_cast /=.
        case: ifP=> //= h. + by rewrite h in hi.
        case: Archi.ptr64=> //=. case: v1 h1=> //=.
        + move=> ht; by inversion ht.
        + move=> b ht; by inversion ht.
        + move=> i' ht /=. rewrite hi /=.
          have hn := int_range_invalid benv Gamma Sigma i' IBool a ef1 ht.
          rewrite /negb in hn. move: hn. case: ifP=> //= hn _. 
          exists (Values.Vint (Int.divs i' i)). rewrite /trans_cvalue_bvalue /=.
          by exists (Vint (Int.divs i' i)).
        + move=> i' ht; by inversion ht.
        + move=> l o ht; by inversion ht.
      move=> o ht; by inversion ht.
  + case: (intsize_eq I32 I32)=> //= _. case: v1 h1=> //=.
    + move=> h1. by inversion h1.
    + move=> b ht; by inversion ht.
    + move=> i' ht. rewrite hi /=.
      have hn := int_range_invalid benv Gamma Sigma i' IBool a ef1 ht.
      rewrite /negb in hn. move: hn. case: ifP=> //= hn _. 
      exists (Values.Vint (Int.divs i' i)). rewrite /trans_cvalue_bvalue /=.
      by exists (Vint (Int.divs i' i)).
    + move=> i' ht; by inversion ht.
    + move=> l o ht; by inversion ht.
    move=> o ht; by inversion ht.
  + move=> i' _ ht; by inversion ht.
  + move=> l o _ ht; by inversion ht.
  move=> o _ ht; by inversion ht.
(* long *)
move=> s a. case: s=> //=.
case: v1=> //=.
+ move=> ht; by inversion ht.
+ move=> b ht; by inversion ht.
+ move=> i ht; by inversion ht.
+ move=> i' ht. case: v2=> //=.
  + move=> ht'; by inversion ht'.
  + move=> b ht'; by inversion ht'.
  + move=> i ht'; by inversion ht'.
  + move=> i ht' _ _. case: ifP=> //= h _.
    rewrite /Cop.sem_div /Cop.sem_binarith /Cop.sem_cast /Cop.classify_cast /Cop.binarith_type.
    rewrite /Cop.classify_binarith. case: Archi.ptr64=>//=.
    + rewrite h /=. exists (Values.Vlong (Int64.divu i' i)). rewrite /trans_cvalue_bvalue /=.
      by exists (Vint64 (Int64.divu i' i)).
    rewrite h /=. exists (Values.Vlong (Int64.divu i' i)). rewrite /trans_cvalue_bvalue /=.
    by exists (Vint64 (Int64.divu i' i)).
  + move=> p o ht'; by inversion ht'.
  + move=> o ht'; by inversion ht'.
  move=> p i ht'; by inversion ht'.
move=> o ht'; by inversion ht'.
Qed.

(* mod is well-formed *) 
Lemma well_formed_mod : forall cenv benv Gamma Sigma bge vm m v1 t ef1 v2 ef2 s,
store_well_typed benv Gamma Sigma bge vm m ->
type_expr benv Gamma Sigma (Val v1 t) ef1 t ->
type_expr benv Gamma Sigma (Val v2 t) ef2 t ->
is_primint t || is_primlong t ->
signedness_of_type t = Some s ->
check_unsafe_op Cop.Omod s v1 v2 = false ->
exists v' v'',
Cop.sem_binary_operation cenv Cop.Omod (trans_bvalue_cvalue v1) (transBeePL_type t) 
      (trans_bvalue_cvalue v2) (transBeePL_type t) m = Some v' /\
v' <> Values.Vundef /\
trans_cvalue_bvalue v' = OK v''.
Proof.
move=> cnev benv Gamma Sigma bge vm m v1 t ef1 v2 ef2 s hw ht1 ht2 hteq hs hc.
case: s hs hc=> //=.
(* signed *)
+ case: t ht1 ht2 hteq=> //= p; case: p=> //=.
  (* int *)
  + move=> sz s a ht1 ht2 _ [] h1; subst. case: ifP=> //= h.
    case: sz ht1 ht2=> //=.
    (* I8 *)
    + rewrite /Cop.sem_mod /Cop.sem_binarith /= /Cop.sem_cast /Cop.classify_cast /=.
      case: Archi.ptr64=> //=.
      + case: v1 h=> //=.
        + move=> _ ht. by inversion ht.
        + move=> b _ ht. by inversion ht. 
        + move=> i. case: v2=> //=.
          + move=> _ _ ht; by inversion ht.
          + move=> b _ _ ht; inversion ht.
          + move=> i1. case: ifP=> //= hi. case: ifP=> //= hi' _ ht1 ht2.
            exists (Values.Vint (Int.mods i i1)). rewrite / trans_cvalue_bvalue /=.  
            by exists (Vint (Int.mods i i1)).
          + move=> i' _ _ ht; by inversion ht.
          + move=> p o _ _ ht; by inversion ht.
          move=>  o _ _ ht; by inversion ht.
      + move=> i. case: v2=> //=.
        + move=> _ ht; by inversion ht.
        + move=> b _ ht. by inversion ht.
        + move=> i' _ ht; by inversion ht.
        + move=> i' _ ht; by inversion ht.
        + move=> p o _ ht; by inversion ht.
        move=> o _ ht; by inversion ht.
      move=> p i _ ht; by inversion ht.
     move=> o _ ht; by inversion ht.
    case: (intsize_eq I32 I32)=> //=.
    case: v1 h=> //=.
    + move=> _ _ ht; by inversion ht.
    + move=> b _ _ ht; by inversion ht.
    + case: v2=> //=.
      + move=> i _ _ _ ht; by inversion ht.
      + move=> b i _ _ _ ht; by inversion ht.
      + move=> i i'. case: ifP=> //= hi. case: ifP=> //= hi' _ _ ht1 ht2 _.
        exists (Values.Vint (Int.mods i' i)). rewrite / trans_cvalue_bvalue /=.  
        by exists (Vint (Int.mods i' i)).
      + move=> i i' _ _ _ ht; by inversion ht.
      + move=> p i i' _ _ _ ht; by inversion ht.
      + move=> o i _ _ _ ht; by inversion ht.
    + move=> i _ _ ht; by inversion ht.
    + move=> p i _ _ ht; by inversion ht.
    + move=> o _ _ ht; by inversion ht.
   (* I16 *)
    + rewrite /Cop.sem_mod /Cop.sem_binarith /= /Cop.sem_cast /Cop.classify_cast /=.
      case: Archi.ptr64=> //=.
      + case: v1 h=> //=.
        + move=> _ ht. by inversion ht.
        + move=> b _ ht. by inversion ht. 
        + move=> i. case: v2=> //=.
          + move=> _ _ ht; by inversion ht.
          + move=> b _ _ ht; inversion ht.
          + move=> i'. case: ifP=> //= h; case: ifP=> //= h' _ ht1 ht2 _.
            exists (Values.Vint (Int.mods i i')). rewrite /trans_cvalue_bvalue.
            by exists (Vint (Int.mods i i')).
          + move=> i' _ _ ht; by inversion ht.
          + move=> p o _ _ ht; by inversion ht.
          move=>  o _ _ ht; by inversion ht.
      + move=> i. case: v2=> //=.
        + move=> _ ht; by inversion ht.
        + move=> b _ ht. by inversion ht.
        + move=> i' _ ht; by inversion ht.
        + move=> i' _ ht; by inversion ht.
        + move=> p o _ ht; by inversion ht.
        move=> o _ ht; by inversion ht.
      move=> p i _ ht; by inversion ht.
     move=> o _ ht; by inversion ht.
    case: (intsize_eq I32 I32)=> //=.
    case: v1 h=> //=.
    + move=> _ _ ht; by inversion ht.
    + move=> b _ _ ht; by inversion ht.
    + case: v2=> //=.
      + move=> i _ _ _ ht; by inversion ht.
      + move=> b i _ _ _ ht; by inversion ht.
      + move=> i i'. case: ifP=> //= hi. case: ifP=> //= hi' _ _ ht1 ht2 _.
        exists (Values.Vint (Int.mods i' i)). rewrite / trans_cvalue_bvalue /=.  
        by exists (Vint (Int.mods i' i)).
      + move=> i i' _ _ _ ht; by inversion ht.
      + move=> p i i' _ _ _ ht; by inversion ht.
      + move=> o i _ _ _ ht; by inversion ht.
    + move=> i _ _ ht; by inversion ht.
    + move=> p i _ _ ht; by inversion ht.
    move=> o _ _ ht; by inversion ht.
  (* I32 *)
    + rewrite /Cop.sem_mod /Cop.sem_binarith /= /Cop.sem_cast /Cop.classify_cast /=.
      case: Archi.ptr64=> //=.
      + case: v1 h=> //=.
        + move=> _ ht. by inversion ht.
        + move=> b _ ht. by inversion ht. 
        + move=> i. case: v2=> //=.
          + move=> _ _ ht; by inversion ht.
          + move=> b _ _ ht; inversion ht.
          + move=> i'. case: ifP=> //= h; case: ifP=> //= h' _ ht1 ht2 _.
            exists (Values.Vint (Int.mods i i')). rewrite /trans_cvalue_bvalue.
            by exists (Vint (Int.mods i i')).
          + move=> i' _ _ ht; by inversion ht.
          + move=> p o _ _ ht; by inversion ht.
          move=>  o _ _ ht; by inversion ht.
      + move=> i. case: v2=> //=.
        + move=> _ ht; by inversion ht.
        + move=> b _ ht. by inversion ht.
        + move=> i' _ ht; by inversion ht.
        + move=> i' _ ht; by inversion ht.
        + move=> p o _ ht; by inversion ht.
        move=> o _ ht; by inversion ht.
      move=> p i _ ht; by inversion ht.
     move=> o _ ht; by inversion ht.
    case: (intsize_eq I32 I32)=> //=.
    case: v1 h=> //=.
    + move=> _ _ ht; by inversion ht.
    + move=> b _ _ ht; by inversion ht.
    + case: v2=> //=.
      + move=> i _ _ _ ht; by inversion ht.
      + move=> b i _ _ _ ht; by inversion ht.
      + move=> i i'. case: ifP=> //= hi. case: ifP=> //= hi' _ _ ht1 ht2 _.
        exists (Values.Vint (Int.mods i' i)). rewrite / trans_cvalue_bvalue /=.  
        by exists (Vint (Int.mods i' i)).
      + move=> i i' _ _ _ ht; by inversion ht.
      + move=> p i i' _ _ _ ht; by inversion ht.
      + move=> o i _ _ _ ht; by inversion ht.
    + move=> i _ _ ht; by inversion ht.
    + move=> p i _ _ ht; by inversion ht.
    move=> o _ _ ht; by inversion ht.
  (* IBool *)
  rewrite /Cop.sem_mod /Cop.sem_binarith /= /Cop.sem_cast /Cop.classify_cast /=.
  case: Archi.ptr64=> //=.
  + case: v1 h=> //=.
    + move=> _ ht. by inversion ht.
    + move=> b _ ht. by inversion ht. 
      + move=> i. case: v2=> //=.
        + move=> _ _ ht; by inversion ht.
        + move=> b _ _ ht; inversion ht.
        + move=> i'. case: ifP=> //= h; case: ifP=> //= h' _ ht1 ht2 _.
            exists (Values.Vint (Int.mods i i')). rewrite /trans_cvalue_bvalue.
            by exists (Vint (Int.mods i i')).
          + move=> i' _ _ ht; by inversion ht.
          + move=> p o _ _ ht; by inversion ht.
          move=>  o _ _ ht; by inversion ht.
      + move=> i. case: v2=> //=.
        + move=> _ ht; by inversion ht.
        + move=> b _ ht. by inversion ht.
        + move=> i' _ ht; by inversion ht.
        + move=> i' _ ht; by inversion ht.
        + move=> p o _ ht; by inversion ht.
        move=> o _ ht; by inversion ht.
      move=> p i _ ht; by inversion ht.
     move=> o _ ht; by inversion ht.
    case: (intsize_eq I32 I32)=> //=.
    case: v1 h=> //=.
    + move=> _ _ ht; by inversion ht.
    + move=> b _ _ ht; by inversion ht.
    + case: v2=> //=.
      + move=> i _ _ _ ht; by inversion ht.
      + move=> b i _ _ _ ht; by inversion ht.
      + move=> i i'. case: ifP=> //= hi. case: ifP=> //= hi' _ _ ht1 ht2 _.
        exists (Values.Vint (Int.mods i' i)). rewrite / trans_cvalue_bvalue /=.  
        by exists (Vint (Int.mods i' i)).
      + move=> i i' _ _ _ ht; by inversion ht.
      + move=> p i i' _ _ _ ht; by inversion ht.
      + move=> o i _ _ _ ht; by inversion ht.
    + move=> i _ _ ht; by inversion ht.
    + move=> p i _ _ ht; by inversion ht.
    move=> o _ _ ht; by inversion ht.
(* long *)
+ move=> s. case: s=> //= a.
  case: v1=> //=.
  + by move=> ht; inversion ht.
  + by move=> b ht; inversion ht.
  + case: v2=> //=.
    + by move=>  i _ ht; inversion ht.
    + by move=> b i _ ht; inversion ht.
    + by move=> i i' ht; inversion ht.
    + by move=> i i' ht; inversion ht.
    + by move=> p o i' _ ht; inversion ht.
    + by move=> o i ht; inversion ht.
    case: v2=> //=.
    + by move=> i _ ht; inversion ht.
    + by move=> b i _ ht; inversion ht.
    + by move=> i i' _ ht; inversion ht.
    + move=> i1 i2 ht1 ht2 _ _. case: ifP=> //=.
      case: ifP=> //=. case: ifP=> //= h1 h2 _ _.
      rewrite /Cop.sem_mod /Cop.sem_binarith /Cop.sem_cast /=.
      case: Archi.ptr64=> //=.
      + rewrite h2 /= h1 /=. exists (Values.Vlong (Int64.mods i2 i1)).
        rewrite /trans_cvalue_bvalue /=. by exists  (Vint64 (Int64.mods i2 i1)).
      rewrite h2 /= h1 /=. exists (Values.Vlong (Int64.mods i2 i1)).
      rewrite /trans_cvalue_bvalue /=. by exists  (Vint64 (Int64.mods i2 i1)).
    + by move=> p o i' _ ht; inversion ht.
    + by move=> o i _ ht; inversion ht.
    by move=> l o ht; inversion ht.
  by move=> o ht; inversion ht.
(* unsigned *)
+ case: t ht1 ht2 hteq=> //= p; case: p=> //=.
  (* int *)
  + move=> sz s a. case: s=> //=. case: sz=> //=.
    + case: v2=> //=.
      + move=> _ ht; by inversion ht.
      + move=> b _ ht; by inversion ht.
      + move=> i h1 h2 _ _. case: ifP=> //= hi _.
        rewrite /Cop.sem_mod /= /Cop.sem_binarith /Cop.sem_cast /=.
        case: ifP=> //= h. + by rewrite h in hi.
        case: Archi.ptr64=> //=. case: v1 h1=> //=.
        + move=> ht; by inversion ht.
        + move=> b ht; by inversion ht.
        + move=> i' ht /=. rewrite hi /=.
          have hn := int_range_invalid benv Gamma Sigma i' I8 a ef1 ht.
          rewrite /negb in hn. move: hn. case: ifP=> //= hn _. 
          exists (Values.Vint (Int.mods i' i)). rewrite /trans_cvalue_bvalue /=.
          by exists (Vint (Int.mods i' i)).
        + move=> i' ht; by inversion ht.
        + move=> l o ht; by inversion ht.
      move=> o ht; by inversion ht.
  + case: (intsize_eq I32 I32)=> //= _. case: v1 h1=> //=.
    + move=> h1. by inversion h1.
    + move=> b ht; by inversion ht.
    + move=> i' ht. rewrite hi /=.
      have hn := int_range_invalid benv Gamma Sigma i' I8 a ef1 ht.
      rewrite /negb in hn. move: hn. case: ifP=> //= hn _. 
      exists (Values.Vint (Int.mods i' i)). rewrite /trans_cvalue_bvalue /=.
      by exists (Vint (Int.mods i' i)).
    + move=> i' ht; by inversion ht.
    + move=> l o ht; by inversion ht.
    move=> o ht; by inversion ht.
  + move=> i' _ ht; by inversion ht.
  + move=> l o _ ht; by inversion ht.
  move=> o _ ht; by inversion ht.
 +  + case: v2=> //=.
      + move=> _ ht; by inversion ht.
      + move=> b _ ht; by inversion ht.
      + move=> i h1 h2 _ _. case: ifP=> //= hi _.
        rewrite /Cop.sem_mod /= /Cop.sem_binarith /Cop.sem_cast /=.
        case: ifP=> //= h. + by rewrite h in hi.
        case: Archi.ptr64=> //=. case: v1 h1=> //=.
        + move=> ht; by inversion ht.
        + move=> b ht; by inversion ht.
        + move=> i' ht /=. rewrite hi /=.
          have hn := int_range_invalid benv Gamma Sigma i' I16 a ef1 ht.
          rewrite /negb in hn. move: hn. case: ifP=> //= hn _. 
          exists (Values.Vint (Int.mods i' i)). rewrite /trans_cvalue_bvalue /=.
          by exists (Vint (Int.mods i' i)).
        + move=> i' ht; by inversion ht.
        + move=> l o ht; by inversion ht.
      move=> o ht; by inversion ht.
  + case: (intsize_eq I32 I32)=> //= _. case: v1 h1=> //=.
    + move=> h1. by inversion h1.
    + move=> b ht; by inversion ht.
    + move=> i' ht. rewrite hi /=.
      have hn := int_range_invalid benv Gamma Sigma i' I16 a ef1 ht.
      rewrite /negb in hn. move: hn. case: ifP=> //= hn _. 
      exists (Values.Vint (Int.mods i' i)). rewrite /trans_cvalue_bvalue /=.
      by exists (Vint (Int.mods i' i)).
    + move=> i' ht; by inversion ht.
    + move=> l o ht; by inversion ht.
    move=> o ht; by inversion ht.
  + move=> i' _ ht; by inversion ht.
  + move=> l o _ ht; by inversion ht.
  move=> o _ ht; by inversion ht.
  + case: v2=> //=.
      + move=> _ ht; by inversion ht.
      + move=> b _ ht; by inversion ht.
      + move=> i h1 h2 _ _. case: ifP=> //= hi _.
        rewrite /Cop.sem_mod /= /Cop.sem_binarith /Cop.sem_cast /=.
        case: ifP=> //= h. + by rewrite h in hi.
        case: Archi.ptr64=> //=. case: v1 h1=> //=.
        + move=> ht; by inversion ht.
        + move=> b ht; by inversion ht.
        + move=> i' ht /=. rewrite hi /=.
          exists (Values.Vint (Int.modu i' i)). rewrite /trans_cvalue_bvalue /=.
          by exists (Vint (Int.modu i' i)).
        + move=> i' ht; by inversion ht.
        + move=> l o ht; by inversion ht.
      move=> o ht; by inversion ht.
  + case: (intsize_eq I32 I32)=> //= _. case: v1 h1=> //=.
    + move=> h1. by inversion h1.
    + move=> b ht; by inversion ht.
    + move=> i' ht. rewrite hi /=.
      exists (Values.Vint (Int.modu i' i)). rewrite /trans_cvalue_bvalue /=.
      by exists (Vint (Int.modu i' i)).
    + move=> i' ht; by inversion ht.
    + move=> l o ht; by inversion ht.
    move=> o ht; by inversion ht.
  + move=> i' _ ht; by inversion ht.
  + move=> l o _ ht; by inversion ht.
  move=> o _ ht; by inversion ht.
  + case: v2=> //=.
      + move=> _ ht; by inversion ht.
      + move=> b _ ht; by inversion ht.
      + move=> i h1 h2 _ _. case: ifP=> //= hi _.
        rewrite /Cop.sem_mod /= /Cop.sem_binarith /Cop.sem_cast /=.
        case: ifP=> //= h. + by rewrite h in hi.
        case: Archi.ptr64=> //=. case: v1 h1=> //=.
        + move=> ht; by inversion ht.
        + move=> b ht; by inversion ht.
        + move=> i' ht /=. rewrite hi /=.
          have hn := int_range_invalid benv Gamma Sigma i' IBool a ef1 ht.
          rewrite /negb in hn. move: hn. case: ifP=> //= hn _. 
          exists (Values.Vint (Int.mods i' i)). rewrite /trans_cvalue_bvalue /=.
          by exists (Vint (Int.mods i' i)).
        + move=> i' ht; by inversion ht.
        + move=> l o ht; by inversion ht.
      move=> o ht; by inversion ht.
  + case: (intsize_eq I32 I32)=> //= _. case: v1 h1=> //=.
    + move=> h1. by inversion h1.
    + move=> b ht; by inversion ht.
    + move=> i' ht. rewrite hi /=.
      have hn := int_range_invalid benv Gamma Sigma i' IBool a ef1 ht.
      rewrite /negb in hn. move: hn. case: ifP=> //= hn _. 
      exists (Values.Vint (Int.mods i' i)). rewrite /trans_cvalue_bvalue /=.
      by exists (Vint (Int.mods i' i)).
    + move=> i' ht; by inversion ht.
    + move=> l o ht; by inversion ht.
    move=> o ht; by inversion ht.
  + move=> i' _ ht; by inversion ht.
  + move=> l o _ ht; by inversion ht.
  move=> o _ ht; by inversion ht.
(* long *)
move=> s a. case: s=> //=.
case: v1=> //=.
+ move=> ht; by inversion ht.
+ move=> b ht; by inversion ht.
+ move=> i ht; by inversion ht.
+ move=> i' ht. case: v2=> //=.
  + move=> ht'; by inversion ht'.
  + move=> b ht'; by inversion ht'.
  + move=> i ht'; by inversion ht'.
  + move=> i ht' _ _. case: ifP=> //= h _.
    rewrite /Cop.sem_mod /Cop.sem_binarith /Cop.sem_cast /Cop.classify_cast /Cop.binarith_type.
    rewrite /Cop.classify_binarith. case: Archi.ptr64=>//=.
    + rewrite h /=. exists (Values.Vlong (Int64.modu i' i)). rewrite /trans_cvalue_bvalue /=.
      by exists (Vint64 (Int64.modu i' i)).
    rewrite h /=. exists (Values.Vlong (Int64.modu i' i)). rewrite /trans_cvalue_bvalue /=.
    by exists (Vint64 (Int64.modu i' i)).
  + move=> p o ht'; by inversion ht'.
  + move=> o ht'; by inversion ht'.
  move=> p i ht'; by inversion ht'.
move=> o ht'; by inversion ht'.
Qed.
