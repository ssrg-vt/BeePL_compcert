Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import compcert.common.Errors.

From mathcomp Require Import all_ssreflect. 

Lemma extract_type_notbool : forall v t v',
sem_unary_operation Notbool v t = Some v' -> 
t = Ptype Tbool.
Proof.
move=> v t v' /= hs. rewrite /sem_notbool /= in hs.
move: hs. case: v=> //=.
+ case: t=> //= p. by case: p=> //=.
+ case: t=> //= p. by case: p=> //=.
+ case: t=> //= p. case: p=> //=.
case: t=> //= i b. case: b=> //= p. case: p=> //=.
Qed.

Lemma extract_type_notint : forall v t v',
sem_unary_operation Notint v t = Some v' -> 
exists sz s, t = Ptype (Tint sz s).
Proof.
move=> v t v' /= hs. rewrite /sem_notint in hs.
move: hs. case: v=> //=.
+ case: t=> //= p. by case: p=> //=.
+ case: t=> //= p i. case: p=> //= sz s [] hv; subst. 
  by exists sz, s.
+ case: t=> //= p. by case: p=> //=.
case: t=> //= i b. case: b=> //= p.
by case: p=> //=.
Qed.

Lemma extract_type_neg : forall v t v',
sem_unary_operation Neg v t = Some v' -> 
exists sz s, t = Ptype (Tint sz s).
Proof.
move=> v t v' /= hs. rewrite /sem_notint in hs.
move: hs. case: v=> //=.
+ case: t=> //= p. by case: p=> //=.
+ case: t=> //= p i. case: p=> //= sz s [] hv; subst. 
  by exists sz, s.
+ case: t=> //= p. by case: p=> //=.
case: t=> //= i b. case: b=> //= p.
by case: p=> //=.
Qed.
 
Lemma extract_type_plus1 : forall v1 v2 t1 t2 v,
sem_binary_operation Plus v1 v2 t1 t2 = Some v -> 
exists sz s, t1 = Ptype (Tint sz s). 
Proof.
move=> v1 v2 t1 t2 v. rewrite /sem_binary_operation /sem_plus.
case: v1=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. by case: p=> //=.
+ case: v2=> //=. case: t1=> //= p i i'. case: p=> //= sz s.
  case: t2=> //= p. case: p=> //= sz' s' [] hv; subst. by exists sz, s.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=. case: t2=> //= p.
  by case: p=> //=.
case: v2=> //=. case: t1=> //= i b. case: b=> //= p.
case: p=> //= sz s. case: t2=> //= b b'. case: b'=> //= p. by case: p.
Qed.

Lemma extract_type_plus2 : forall v1 v2 t1 t2 v,
sem_binary_operation Plus v1 v2 t1 t2 = Some v -> 
exists sz s, t2 = Ptype (Tint sz s). 
Proof.
move=> v1 v2 t1 t2 v. rewrite /sem_binary_operation /sem_plus.
case: v1=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. by case: p=> //=.
+ case: v2=> //=. case: t1=> //= p i i'. case: p=> //= sz s.
  case: t2=> //= p. case: p=> //= sz' s' [] hv; subst. by exists sz', s'.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=. case: t2=> //= p.
  by case: p=> //=.
case: v2=> //=. case: t1=> //= i b. case: b=> //= p.
case: p=> //= sz s. case: t2=> //= b b'. case: b'=> //= p. by case: p.
Qed.

Lemma extract_type_minus1 : forall v1 v2 t1 t2 v,
sem_binary_operation Minus v1 v2 t1 t2 = Some v -> 
exists sz s, t1 = Ptype (Tint sz s). 
Proof.
move=> v1 v2 t1 t2 v. rewrite /sem_binary_operation /sem_minus.
case: v1=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. by case: p=> //=.
+ case: v2=> //=. case: t1=> //= p i i'. case: p=> //= sz s.
  case: t2=> //= p. case: p=> //= sz' s' [] hv; subst. by exists sz, s.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=. case: t2=> //= p.
  by case: p=> //=.
case: v2=> //=. case: t1=> //= i b. case: b=> //= p.
case: p=> //= sz s. case: t2=> //= b b'. case: b'=> //= p. by case: p.
Qed.

Lemma extract_type_minus2 : forall v1 v2 t1 t2 v,
sem_binary_operation Minus v1 v2 t1 t2 = Some v -> 
exists sz s, t2 = Ptype (Tint sz s). 
Proof.
move=> v1 v2 t1 t2 v. rewrite /sem_binary_operation /sem_plus.
case: v1=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. by case: p=> //=.
+ case: v2=> //=. case: t1=> //= p i i'. case: p=> //= sz s.
  case: t2=> //= p. case: p=> //= sz' s' [] hv; subst. by exists sz', s'.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=. case: t2=> //= p.
  by case: p=> //=.
case: v2=> //=. case: t1=> //= i b. case: b=> //= p.
case: p=> //= sz s. case: t2=> //= b b'. case: b'=> //= p. by case: p.
Qed.

Lemma extract_type_mult1 : forall v1 v2 t1 t2 v,
sem_binary_operation Mult v1 v2 t1 t2 = Some v -> 
exists sz s, t1 = Ptype (Tint sz s). 
Proof.
move=> v1 v2 t1 t2 v. rewrite /sem_binary_operation /sem_plus.
case: v1=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. by case: p=> //=.
+ case: v2=> //=. case: t1=> //= p i i'. case: p=> //= sz s.
  case: t2=> //= p. case: p=> //= sz' s' [] hv; subst. by exists sz, s.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=. case: t2=> //= p.
  by case: p=> //=.
case: v2=> //=. case: t1=> //= i b. case: b=> //= p.
case: p=> //= sz s. case: t2=> //= b b'. case: b'=> //= p. by case: p.
Qed.

Lemma extract_type_mult2 : forall v1 v2 t1 t2 v,
sem_binary_operation Mult v1 v2 t1 t2 = Some v -> 
exists sz s, t2 = Ptype (Tint sz s). 
Proof.
move=> v1 v2 t1 t2 v. rewrite /sem_binary_operation /sem_plus.
case: v1=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. by case: p=> //=.
+ case: v2=> //=. case: t1=> //= p i i'. case: p=> //= sz s.
  case: t2=> //= p. case: p=> //= sz' s' [] hv; subst. by exists sz', s'.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=. case: t2=> //= p.
  by case: p=> //=.
case: v2=> //=. case: t1=> //= i b. case: b=> //= p.
case: p=> //= sz s. case: t2=> //= b b'. case: b'=> //= p. by case: p.
Qed.

Lemma extract_type_div1 : forall v1 v2 t1 t2 v,
sem_binary_operation Div v1 v2 t1 t2 = Some v -> 
exists sz s, t1 = Ptype (Tint sz s). 
Proof.
move=> v1 v2 t1 t2 v. rewrite /sem_binary_operation /sem_div.
case: v1=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. by case: p=> //=.
+ case: v2=> //=. case: t1=> //= p i i'. case: p=> //= sz s.
  case: t2=> //= p. case: p=> //= sz' s'. by exists sz, s.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=. case: t2=> //= p.
  by case: p=> //=.
case: v2=> //=. case: t1=> //= i b. case: b=> //= p.
case: p=> //= sz s. case: t2=> //= b b'. case: b'=> //= p. by case: p.
Qed.

Lemma extract_type_div2 : forall v1 v2 t1 t2 v,
sem_binary_operation Div v1 v2 t1 t2 = Some v -> 
exists sz s, t2 = Ptype (Tint sz s). 
Proof.
move=> v1 v2 t1 t2 v. rewrite /sem_binary_operation /sem_div.
case: v1=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. by case: p=> //=.
+ case: v2=> //=. case: t1=> //= p i i'. case: p=> //= sz s.
  case: t2=> //= p. case: p=> //= sz' s'. by exists sz', s'.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=. case: t2=> //= p.
  by case: p=> //=.
case: v2=> //=. case: t1=> //= i b. case: b=> //= p.
case: p=> //= sz s. case: t2=> //= b b'. case: b'=> //= p. by case: p.
Qed.

Lemma extract_type_shl1 : forall v1 v2 t1 t2 v,
sem_binary_operation Shl v1 v2 t1 t2 = Some v -> 
exists sz s, t1 = Ptype (Tint sz s). 
Proof.
move=> v1 v2 t1 t2 v. rewrite /sem_binary_operation /sem_shl.
case: v1=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. by case: p=> //=.
+ case: v2=> //=. case: t1=> //= p i i'. case: p=> //= sz s.
  case: t2=> //= p. case: p=> //= sz' s'. case: sz=> //=. 
  case: sz'=> //=. case: ifP=> //= hl [] hv. by exists I32, s.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=. case: t2=> //= p.
  by case: p=> //=.
case: v2=> //=. case: t1=> //= i b. case: b=> //= p.
case: p=> //= sz s. case: t2=> //= b b'. case: b'=> //= p. by case: p.
Qed.

Lemma extract_type_shl2 : forall v1 v2 t1 t2 v,
sem_binary_operation Shl v1 v2 t1 t2 = Some v -> 
exists sz s, t2 = Ptype (Tint sz s). 
Proof.
move=> v1 v2 t1 t2 v. rewrite /sem_binary_operation /sem_shl.
case: v1=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. by case: p=> //=.
+ case: v2=> //=. case: t1=> //= p i i'. case: p=> //= sz s.
  case: t2=> //= p. case: p=> //= sz' s'.
  case: sz=> //=. case: sz'=> //=.  case: ifP=> //= hl [] hv. by exists I32, s'.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=. case: t2=> //= p.
  by case: p=> //=.
case: v2=> //=. case: t1=> //= i b. case: b=> //= p.
case: p=> //= sz s. case: t2=> //= b b'. case: b'=> //= p. by case: p.
Qed.

Lemma extract_type_shr1 : forall v1 v2 t1 t2 v,
sem_binary_operation Shr v1 v2 t1 t2 = Some v -> 
exists s, t1 = Ptype (Tint I32 s). 
Proof.
move=> v1 v2 t1 t2 v. rewrite /sem_binary_operation /sem_shl.
case: v1=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. by case: p=> //=.
+ case: v2=> //=. case: t1=> //= p i i'. case: p=> //= sz s.
  case: t2=> //= p. case: p=> //= sz' s'. case: s=> //=. 
  case: s'=> //=. case: sz=> //=. case: sz'=> //=. 
  case: ifP=> //= hl [] hv. by exists Signed.
+ case: s'=> //=. case: sz=> //=. case: sz'=> //=.
  case: ifP=> //= hl [] hv; subst. by exists Unsigned.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=. case: t2=> //= p.
  by case: p=> //=.
case: v2=> //=. case: t1=> //= i b. case: b=> //= p.
case: p=> //= sz s. case: t2=> //= b b'. case: b'=> //= p. by case: p.
Qed.

Lemma extract_type_shr2 : forall v1 v2 t1 t2 v,
sem_binary_operation Shr v1 v2 t1 t2 = Some v -> 
exists s, t2 = Ptype (Tint I32 s). 
Proof.
move=> v1 v2 t1 t2 v. rewrite /sem_binary_operation /sem_shl.
case: v1=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. by case: p=> //=.
+ case: v2=> //=. case: t1=> //= p i i'. case: p=> //= sz s.
  case: t2=> //= p. case: p=> //= sz' s'. case: s=> //=. 
  case: s'=> //=. case: sz=> //=. case: sz'=> //=. 
  case: ifP=> //= hl [] hv. by exists Signed.
+ case: s'=> //=. case: sz=> //=. case: sz'=> //=.
  case: ifP=> //= hl [] hv; subst. by exists Unsigned.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=. case: t2=> //= p.
  by case: p=> //=.
case: v2=> //=. case: t1=> //= i b. case: b=> //= p.
case: p=> //= sz s. case: t2=> //= b b'. case: b'=> //= p. by case: p.
Qed.

Lemma int_gt_zero : forall i,
Int.eq i Int.zero = false -> 
(-1 < Int.intval i < Int.modulus)%Z ->
(0 < Int.intval i)%Z.
Proof.
move=> [] i ir /= heq h. case: i ir heq h=> //=. 
move=> p ir /= heq h. inversion h; subst. have hz := Zlt_neg_0 p.
rewrite /Int.modulus /= /Int.wordsize /= /Wordsize_32.wordsize /two_power_nat /= in H0.
by case: p ir heq h H hz H0=> //=.
Qed.

Lemma sem_unary_operation_val_type : forall op v t v', 
sem_unary_operation op v t = Some v' ->
typeof_value v t /\ typeof_value v' t.
Proof.
move=> [].
+ move=> v t v' hs.
  have ht := extract_type_notbool v t v' hs; subst. split.
  + by case: v hs=> //=.
  case: v' hs=> //=.
  + move=> hs. rewrite /sem_notbool in hs. by case: v hs=> //=.
  + move=> i hs. rewrite /sem_notbool in hs. by case: v hs=> //=.
  move=> i hs. rewrite /sem_notbool in hs. by case: v hs=> //=.
+ move=> v t v' hs.
  have [sz [s ht]]:= extract_type_notint v t v' hs; subst. split.
  + case: v hs=> //=. case: v' hs=> //=.
    + rewrite /sem_notint /=. by case: v=> //=.
    rewrite /sem_notint /=. by case: v=> //=.
  rewrite /sem_notint /=. by case: v=> //=.
move=> v t v' hs. have [sz [s ht]] := extract_type_neg v t v' hs; subst. split.
+ by case: v hs=> //=.
case: v' hs=> //=.
+ rewrite /sem_neg /=. by case: v=> //=.
+ rewrite /sem_neg /=. by case: v=> //=.
rewrite /sem_neg /=. by case: v=> //=.
Qed.

Lemma sem_binary_operation_val_type : forall op v1 v2 t v, 
sem_binary_operation op v1 v2 t t = Some v ->
typeof_value v (if (is_not_comparison op) then t else (Ptype Tbool)).
Proof.
move=> [];rewrite /sem_binary_operation.
+ move=> v1 v2 t v hs. move: hs. rewrite /sem_plus. 
  case: v1=> //=.
  + case: v2=> //=. case: t=> //= p. by case: p=> //=.
  + case: v2=> //=. case: t=> //= p. by case: p=> //= [] s s' i i' [] hv; subst.
  + case: v2=> //=. case: t=> //= p. by case: p=> //=.
  case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
+ move=> v1 v2 t v hs. move: hs. rewrite /sem_plus. 
  case: v1=> //=.
  + case: v2=> //=. case: t=> //= p. by case: p=> //=.
  + case: v2=> //=. case: t=> //= p. by case: p=> //= [] s s' i i' [] hv; subst.
  + case: v2=> //=. case: t=> //= p. by case: p=> //=.
  case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
+ move=> v1 v2 t v hs. move: hs. rewrite /sem_plus. 
  case: v1=> //=.
  + case: v2=> //=. case: t=> //= p. by case: p=> //=.
  + case: v2=> //=. case: t=> //= p. by case: p=> //= [] s s' i i' [] hv; subst.
  + case: v2=> //=. case: t=> //= p. by case: p=> //=.
  case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
+ move=> v1 v2 t v hs. move: hs. rewrite /sem_plus. 
  case: v1=> //=.
  + case: v2=> //=. case: t=> //= p. by case: p=> //=.
  + case: v2=> //=. case: t=> //= p. case: p=> //= i s i1 i2. 
    case: s=> //=. 
    + case: i=> //=. by case: ifP=> //= he [] hv; subst.
    case: i=> //=. by case: ifP=> //= he [] hv; subst.
  + case: v2=> //=. case: t=> //= p. case: p=> //=.
    case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
+ move=> v1 v2 t v. case: v1=> //=.  
  + case: v2=> //=. case: t=> //= p. by case: p=> //=.
    case: v2=> //=. case: t=> //= p. by case: p=> //=.
  case: v2=> //=. case: t=> //= p. by case:p=> //= b b' [] hv; subst.
  case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
+ move=> v1 v2 t v. case: v1=> //=.  
  + case: v2=> //=. case: t=> //= p. by case: p=> //=.
    case: v2=> //=. case: t=> //= p. by case: p=> //=.
  case: v2=> //=. case: t=> //= p. by case:p=> //= b b' [] hv; subst.
  case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
+ move=> v1 v2 t v. case: v1=> //=.  
  + case: v2=> //=. case: t=> //= p. by case: p=> //=.
    case: v2=> //=. case: t=> //= p. by case: p=> //=.
  case: v2=> //=. case: t=> //= p. by case:p=> //= b b' [] hv; subst.
  case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
+ move=> v1 v2 t v. case: v1=> //=.  
  + case: v2=> //=. case: t=> //= p. by case: p=> //=.
    case: v2=> //=. case: t=> //= p. case: p=> //= sz s. case: sz=> //= i i'.
    by case: ifP=> //= hl [] hv; subst.
  case: v2=> //=. case: t=> //= p. by case:p=> //= b b' [] hv; subst.
  case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
+ move=> v1 v2 t v. case: v1=> //=.  
  + case: v2=> //=. case: t=> //= p. by case: p=> //=.
    case: v2=> //=. case: t=> //= p. case: p=> //= sz s. case: s=> //= i i'.
    case: sz=> //=. by case: ifP=> //= hl [] hv; subst.
    case: sz=> //=. by case: ifP=> //= hl [] hv; subst.
  case: v2=> //=. case: t=> //= p. by case:p=> //= b b' [] hv; subst.
  case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
+ move=> v1 v2 t v. rewrite /is_not_comparison /=. case: v1=> //=.
  + case: v2=> //=. case: t=> //= p. by case: p=> //= [] [] hv; subst.
  + case: v2=> //= i i'. case: t=> //= p. case: p=> //= sz s. case: s=> //=.
    + by case: sz=> //= [] [] hv; subst.
    + by case: sz=> //= [] [] hv; subst.
    case: v2=> //= b b'. case: t=> //= p. by case: p=> //= [] [] hv; subst.
  case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
+ move=> v1 v2 t v. rewrite /is_not_comparison /=. case: v1=> //=.
  + case: v2=> //=. case: t=> //= p. by case: p=> //= [] [] hv; subst.
  + case: v2=> //= i i'. case: t=> //= p. case: p=> //= sz s. case: s=> //=.
    + by case: sz=> //= [] [] hv; subst.
    + by case: sz=> //= [] [] hv; subst.
    case: v2=> //= b b'. case: t=> //= p. by case: p=> //= [] [] hv; subst.
  case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
+ move=> v1 v2 t v. rewrite /is_not_comparison /=. case: v1=> //=.
  + case: v2=> //=. case: t=> //= p. by case: p=> //= [] [] hv; subst.
  + case: v2=> //= i i'. case: t=> //= p. case: p=> //= sz s. case: s=> //=.
    + by case: sz=> //= [] [] hv; subst.
    + by case: sz=> //= [] [] hv; subst.
    case: v2=> //= b b'. case: t=> //= p. by case: p=> //= [] [] hv; subst.
  case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
+ move=> v1 v2 t v. rewrite /is_not_comparison /=. case: v1=> //=.
  + case: v2=> //=. case: t=> //= p. by case: p=> //= [] [] hv; subst.
  + case: v2=> //= i i'. case: t=> //= p. case: p=> //= sz s. case: s=> //=.
    + by case: sz=> //= [] [] hv; subst.
    + by case: sz=> //= [] [] hv; subst.
    case: v2=> //= b b'. case: t=> //= p. case: p=> //= [] [] hv; subst.
    move: hv. by case: ifP=> //= hb [] hv; subst.
  case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
+ move=> v1 v2 t v. rewrite /is_not_comparison /=. case: v1=> //=.
  + case: v2=> //=. case: t=> //= p. by case: p=> //= [] [] hv; subst.
  + case: v2=> //= i i'. case: t=> //= p. case: p=> //= sz s. case: s=> //=.
    + by case: sz=> //= [] [] hv; subst.
    + by case: sz=> //= [] [] hv; subst.
    case: v2=> //= b b'. case: t=> //= p. by case: p=> //= [] [] hv; subst.
  case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
move=> v1 v2 t v. rewrite /is_not_comparison /=. case: v1=> //=.
+ case: v2=> //=. case: t=> //= p. by case: p=> //= [] [] hv; subst.
+ case: v2=> //= i i'. case: t=> //= p. case: p=> //= sz s. case: s=> //=.
  + by case: sz=> //= [] [] hv; subst.
  + by case: sz=> //= [] [] hv; subst.
  case: v2=> //= b b'. case: t=> //= p. case: p=> //= [] [] hv; subst.
  move: hv. by case: ifP=> //= hb [] hv; subst.
case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
Qed.

Lemma sem_binary_operation_val_type1 : forall op v1 v2 t1 t2 v, 
sem_binary_operation op v1 v2 t1 t2 = Some v ->
typeof_value v (if (is_not_comparison op) then t1 else (Ptype Tbool)).
Proof.
move=> [].
(* plus *)
+ move=> v1 v2 t1 t2 v ho. have := extract_type_plus1 v1 v2 t1 t2 v ho.
  move=> [] sz [] s h1; subst. rewrite /is_not_comparison /=.
  case: v ho=> //=.
  + case: t2=> //= p.
    + by case: p=> //=;case: v1=> //=; case: v2=> //=.
    + by case: v1=> //=; case: v2=> //=.
    by case: v1=> //=; case: v2=> //=.
  + case: t2=> //= p.
    + by case: p=> //=;case: v1=> //=; case: v2=> //=.
    + by case: v1=> //=; case: v2=> //=.
    by case: v1=> //=; case: v2=> //=.
  case: t2=> //= p.
  + by case: p=> //=;case: v1=> //=; case: v2=> //=.
  + by case: v1=> //=; case: v2=> //=.
  by case: v1=> //=; case: v2=> //=.
(* minus *)
+ move=> v1 v2 t1 t2 v ho. have := extract_type_minus1 v1 v2 t1 t2 v ho.
  move=> [] sz [] s h1; subst. rewrite /is_not_comparison /=.
  case: v ho=> //=.
  + case: t2=> //= p.
    + by case: p=> //=;case: v1=> //=; case: v2=> //=.
    + by case: v1=> //=; case: v2=> //=.
    by case: v1=> //=; case: v2=> //=.
  + case: t2=> //= p.
    + by case: p=> //=;case: v1=> //=; case: v2=> //=.
    + by case: v1=> //=; case: v2=> //=.
    by case: v1=> //=; case: v2=> //=.
  case: t2=> //= p.
  + by case: p=> //=;case: v1=> //=; case: v2=> //=.
  + by case: v1=> //=; case: v2=> //=.
  by case: v1=> //=; case: v2=> //=.
(* mult *)
+ move=> v1 v2 t1 t2 v ho. have := extract_type_mult1 v1 v2 t1 t2 v ho.
  move=> [] sz [] s h1; subst. rewrite /is_not_comparison /=.
  case: v ho=> //=.
  + case: t2=> //= p.
    + by case: p=> //=;case: v1=> //=; case: v2=> //=.
    + by case: v1=> //=; case: v2=> //=.
    by case: v1=> //=; case: v2=> //=.
  + case: t2=> //= p.
    + by case: p=> //=;case: v1=> //=; case: v2=> //=.
    + by case: v1=> //=; case: v2=> //=.
    by case: v1=> //=; case: v2=> //=.
  case: t2=> //= p.
  + by case: p=> //=;case: v1=> //=; case: v2=> //=.
  + by case: v1=> //=; case: v2=> //=.
  by case: v1=> //=; case: v2=> //=.
(* div *)
+ move=> v1 v2 t1 t2 v ho. have := extract_type_div1 v1 v2 t1 t2 v ho.
  move=> [] sz [] s h1; subst. rewrite /is_not_comparison /=.
  case: v ho=> //=.
  + case: t2=> //= p.
    + by case: p=> //=;case: v1=> //=; case: v2=> //=; case:s=> //= i i' sz' s; case: s=> //=;
      case: sz=> //=; case: sz'=> //=; case: ifP=> //=. 
    + by case: v1=> //=; case: v2=> //=.
    by case: v1=> //=; case: v2=> //=.
  + case: t2=> //= p.
    + + by case: p=> //=;case: v1=> //=; case: v2=> //=; case:s=> //= i i' sz' s; case: s=> //=;
      case: sz=> //=; case: sz'=> //=; case: ifP=> //=.
    + by case: v1=> //=; case: v2=> //=.
    by case: v1=> //=; case: v2=> //=.
  case: t2=> //= p.
  + by case: p=> //=;case: v1=> //=; case: v2=> //=; case:s=> //= i i' sz' s; case: s=> //=;
      case: sz=> //=; case: sz'=> //=; case: ifP=> //=.
  + by case: v1=> //=; case: v2=> //=.
  by case: v1=> //=; case: v2=> //=.
(* and *)
+ move=> v1 v2 t1 t2 v;case: v1=> //=; case: v2 => //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= b b' [] hv; subst.
  by case: t1=> //= i b; case: b=> //= p; case: p=> //= sz s; case: t2=> //= b b'; case: b'=> //= p;
  case: p=> //=.
(* or *)
+ move=> v1 v2 t1 t2 v;case: v1=> //=; case: v2 => //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= b b' [] hv; subst.
  by case: t1=> //= i b; case: b=> //= p; case: p=> //= sz s; case: t2=> //= b b'; case: b'=> //= p;
  case: p=> //=.
(* xor *)
+ move=> v1 v2 t1 t2 v;case: v1=> //=; case: v2 => //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= b b' [] hv; subst.
  by case: t1=> //= i b; case: b=> //= p; case: p=> //= sz s; case: t2=> //= b b'; case: b'=> //= p;
  case: p=> //=.
(* shl *)
+ move=> v1 v2 t1 t2 v;case: v1=> //=; case: v2 => //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p sz s i i'; case: p=> //= sz'; case: sz=> //=;
    case: sz'=> //=; case: ifP=> //= hl s' [] hv; subst.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //=.
  case: t1=> //= i b; case: b=> //= p; case: p=> //= sz s; case: t2=> //= b; case: b=> //= p b';
  case: b'=> //= p'.
  + by case: p'=> //=. 
  + by case: p'=> //=.
  by case: p=> //= p; case: p=> //=.
(* shr *)
+ move=> v1 v2 t1 t2 v;case: v1=> //=; case: v2 => //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= sz s sz' s' i i';
    case: s=> //=; case: s'=> //=; case: sz'=> //=; case: sz=> //=; case: ifP=> //= hl [] hv; subst.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //=.
  case: t1=> //= i b; case: b=> //= p; case: p=> //= sz s; case: t2=> //= b; case: b=> //= p b';
  case: b'=> //= p'.
  + by case: p'=> //=. 
  + by case: p'=> //=.
  by case: p=> //= p; case: p=> //=.
(* eq *)
+ move=> v1 v2 t1 t2 v;case: v1=> //=; case: v2 => //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= [] [] hv; subst.
  + by case: t1=> //= p i i'; case: p=> //=; case: t2=> //= p sz s; case: p=> //= sz' s'; case: s=> //=;
    case: s'=> //=; case: sz=> //=; case: sz'=> //= [] [] hv; subst.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= b b' [] hb; subst.
  case: t1=> //= i b; case: b=> //= p; case: p=> //=; case: t2=> //= b; case: b=> //= p b. 
  + by case: b=> //= p'; case: p'=> //=.
  + by case: b=> //= p'; case: p'=> //=.
  by case: p=> //= p; case: p=> //=.
(* neq *)
+ move=> v1 v2 t1 t2 v;case: v1=> //=; case: v2 => //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= [] [] hv; subst.
  + by case: t1=> //= p i i'; case: p=> //=; case: t2=> //= p sz s; case: p=> //= sz' s'; case: s=> //=;
    case: s'=> //=; case: sz=> //=; case: sz'=> //= [] [] hv; subst.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= b b' [] hb; subst.
  case: t1=> //= i b; case: b=> //= p; case: p=> //=; case: t2=> //= b; case: b=> //= p b. 
  + by case: b=> //= p'; case: p'=> //=.
  + by case: b=> //= p'; case: p'=> //=.
  by case: p=> //= p; case: p=> //=.
(* lt *)
+ move=> v1 v2 t1 t2 v;case: v1=> //=; case: v2 => //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= [] [] hv; subst.
  + by case: t1=> //= p i i'; case: p=> //=; case: t2=> //= p sz s; case: p=> //= sz' s'; case: s=> //=;
    case: s'=> //=; case: sz=> //=; case: sz'=> //= [] [] hv; subst.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= b b' [] hb; subst.
  case: t1=> //= i b; case: b=> //= p; case: p=> //=; case: t2=> //= b; case: b=> //= p b. 
  + by case: b=> //= p'; case: p'=> //=.
  + by case: b=> //= p'; case: p'=> //=.
  by case: p=> //= p; case: p=> //=.
(* lte *)
+ move=> v1 v2 t1 t2 v;case: v1=> //=; case: v2 => //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= [] [] hv; subst.
  + by case: t1=> //= p i i'; case: p=> //=; case: t2=> //= p sz s; case: p=> //= sz' s'; case: s=> //=;
    case: s'=> //=; case: sz=> //=; case: sz'=> //= [] [] hv; subst.
  + by case: t1=> //= p b b'; case: p=> //=; case: t2=> //= p; case: p=> //=; case: ifP=> //= hb [] hv; subst.
  by case: t1=> //= i b; case: b=> //= p; case: p=> //=; case: t2=> //= i' b; case: b=> //= p; case: p=> //=.
(* gt *)
+ move=> v1 v2 t1 t2 v;case: v1=> //=; case: v2 => //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= [] [] hv; subst.
  + by case: t1=> //= p i i'; case: p=> //=; case: t2=> //= p sz s; case: p=> //= sz' s'; case: s=> //=;
    case: s'=> //=; case: sz=> //=; case: sz'=> //= [] [] hv; subst.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= b b' [] hb; subst.
  case: t1=> //= i b; case: b=> //= p; case: p=> //=; case: t2=> //= b; case: b=> //= p b. 
  + by case: b=> //= p'; case: p'=> //=.
  + by case: b=> //= p'; case: p'=> //=.
  by case: p=> //= p; case: p=> //=.
(* gte *)
 move=> v1 v2 t1 t2 v;case: v1=> //=; case: v2 => //=.
+ by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= [] [] hv; subst.
+ by case: t1=> //= p i i'; case: p=> //=; case: t2=> //= p sz s; case: p=> //= sz' s'; case: s=> //=;
  case: s'=> //=; case: sz=> //=; case: sz'=> //= [] [] hv; subst.
+ by case: t1=> //= p b b'; case: p=> //=; case: t2=> //= p; case: p=> //=; case: ifP=> //= hb [] hv; subst.
by case: t1=> //= i b; case: b=> //= p; case: p=> //=; case: t2=> //= i' b; case: b=> //= p; case: p=> //=.
Qed.

Lemma sem_binary_operation_val_type2 : forall op v1 v2 t1 t2 v, 
sem_binary_operation op v1 v2 t1 t2 = Some v ->
typeof_value v (if (is_not_comparison op) then t2 else (Ptype Tbool)).
Proof.
move=> [].
(* plus *)
+ move=> v1 v2 t1 t2 v ho. have := extract_type_plus2 v1 v2 t1 t2 v ho.
  move=> [] sz [] s h1; subst. rewrite /is_not_comparison /=.
  case: v ho=> //=.
  + case: t1=> //= p.
    + by case: p=> //=;case: v1=> //=; case: v2=> //=.
    + move=> b. case: b=> //= p'. by case: v1=> //=; case: v2=> //=; case: p'=> //=.
    by case: v1=> //=; case: v2=> //=.
  + case: t1=> //= p.
    + by case: p=> //=;case: v1=> //=; case: v2=> //=.
    + move=> b. case: b=> //= p'. by case: v1=> //=; case: v2=> //=; case: p'=> //=.
    by case: v1=> //=; case: v2=> //=.
  case: t1=> //= p.
  + by case: p=> //=;case: v1=> //=; case: v2=> //=.
  + move=> b. case: b=> //= p'. by case: v1=> //=; case: v2=> //=; case: p'=> //=.
  by case: v1=> //=; case: v2=> //=.
(* minus *)
+ move=> v1 v2 t1 t2 v ho. have := extract_type_minus2 v1 v2 t1 t2 v ho.
  move=> [] sz [] s h1; subst. rewrite /is_not_comparison /=.
  case: v ho=> //=.
  + case: t1=> //= p.
    + by case: p=> //=;case: v1=> //=; case: v2=> //=.
    + move=> b. case: b=> //= p'. by case: v1=> //=; case: v2=> //=; case: p'=> //=.
    by case: v1=> //=; case: v2=> //=.
  + case: t1=> //= p.
    + by case: p=> //=;case: v1=> //=; case: v2=> //=.
    + move=> b. case: b=> //= p'. by case: v1=> //=; case: v2=> //=; case: p'=> //=.
    by case: v1=> //=; case: v2=> //=.
  case: t1=> //= p.
  + by case: p=> //=;case: v1=> //=; case: v2=> //=.
  + move=> b. case: b=> //= p'. by case: v1=> //=; case: v2=> //=; case: p'=> //=.
  by case: v1=> //=; case: v2=> //=.
(* mult *)
+ move=> v1 v2 t1 t2 v ho. have := extract_type_mult2 v1 v2 t1 t2 v ho.
  move=> [] sz [] s h1; subst. rewrite /is_not_comparison /=.
  case: v ho=> //=.
  + case: t1=> //= p.
    + by case: p=> //=;case: v1=> //=; case: v2=> //=.
    + move=> b. case: b=> //= p'. by case: v1=> //=; case: v2=> //=; case: p'=> //=.
    by case: v1=> //=; case: v2=> //=.
  + case: t1=> //= p.
    + by case: p=> //=;case: v1=> //=; case: v2=> //=.
    + move=> b. case: b=> //= p'. by case: v1=> //=; case: v2=> //=; case: p'=> //=.
    by case: v1=> //=; case: v2=> //=.
  case: t1=> //= p.
  + by case: p=> //=;case: v1=> //=; case: v2=> //=.
  + move=> b. case: b=> //= p'. by case: v1=> //=; case: v2=> //=; case: p'=> //=.
  by case: v1=> //=; case: v2=> //=.
(* div *)
+ move=> v1 v2 t1 t2 v ho. have := extract_type_div1 v1 v2 t1 t2 v ho.
  move=> [] sz [] s h1; subst. rewrite /is_not_comparison /=.
  case: v ho=> //=.
  + case: t2=> //= p.
    + by case: p=> //=;case: v1=> //=; case: v2=> //=; case:s=> //= i i' sz' s; case: s=> //=;
      case: sz=> //=; case: sz'=> //=; case: ifP=> //=. 
    + by case: v1=> //=; case: v2=> //=.
    by case: v1=> //=; case: v2=> //=.
  + case: t2=> //= p.
    + + by case: p=> //=;case: v1=> //=; case: v2=> //=; case:s=> //= i i' sz' s; case: s=> //=;
      case: sz=> //=; case: sz'=> //=; case: ifP=> //=.
    + by case: v1=> //=; case: v2=> //=.
    by case: v1=> //=; case: v2=> //=.
  + case: t2=> //= p.
    + by case: p=> //=;case: v1=> //=; case: v2=> //=; case:s=> //= i i' sz' s; case: s=> //=;
      case: sz=> //=; case: sz'=> //=; case: ifP=> //=.
    + by case: v1=> //=; case: v2=> //=.
    by case: v1=> //=; case: v2=> //=.
  case: t2=> //= p.
  + by case: p=> //=;case: v1=> //=; case: v2=> //=; case:s=> //= i i' sz' s; case: s=> //=;
    case: sz=> //=; case: sz'=> //=; case: ifP=> //=.
  by case: v1=> //=; case: v2=> //=.
(* and *)
+ move=> v1 v2 t1 t2 v;case: v1=> //=; case: v2 => //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= b b' [] hv; subst.
  by case: t1=> //= i b; case: b=> //= p; case: p=> //= sz s; case: t2=> //= b b'; case: b'=> //= p;
  case: p=> //=.
(* or *)
+ move=> v1 v2 t1 t2 v;case: v1=> //=; case: v2 => //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= b b' [] hv; subst.
  by case: t1=> //= i b; case: b=> //= p; case: p=> //= sz s; case: t2=> //= b b'; case: b'=> //= p;
  case: p=> //=.
(* xor *)
+ move=> v1 v2 t1 t2 v;case: v1=> //=; case: v2 => //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= b b' [] hv; subst.
  by case: t1=> //= i b; case: b=> //= p; case: p=> //= sz s; case: t2=> //= b b'; case: b'=> //= p;
  case: p=> //=.
(* shl *)
+ move=> v1 v2 t1 t2 v;case: v1=> //=; case: v2 => //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p sz s i i'; case: p=> //= sz'; case: sz=> //=;
    case: sz'=> //=; case: ifP=> //= hl s' [] hv; subst.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //=.
  case: t1=> //= i b; case: b=> //= p; case: p=> //= sz s; case: t2=> //= b; case: b=> //= p b';
  case: b'=> //= p'.
  + by case: p'=> //=. 
  + by case: p'=> //=.
  by case: p=> //= p; case: p=> //=.
(* shr *)
+ move=> v1 v2 t1 t2 v;case: v1=> //=; case: v2 => //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= sz s sz' s' i i';
    case: s=> //=; case: s'=> //=; case: sz'=> //=; case: sz=> //=; case: ifP=> //= hl [] hv; subst.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //=.
  case: t1=> //= i b; case: b=> //= p; case: p=> //= sz s; case: t2=> //= b; case: b=> //= p b';
  case: b'=> //= p'.
  + by case: p'=> //=. 
  + by case: p'=> //=.
  by case: p=> //= p; case: p=> //=.
(* eq *)
+ move=> v1 v2 t1 t2 v;case: v1=> //=; case: v2 => //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= [] [] hv; subst.
  + by case: t1=> //= p i i'; case: p=> //=; case: t2=> //= p sz s; case: p=> //= sz' s'; case: s=> //=;
    case: s'=> //=; case: sz=> //=; case: sz'=> //= [] [] hv; subst.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= b b' [] hb; subst.
  case: t1=> //= i b; case: b=> //= p; case: p=> //=; case: t2=> //= b; case: b=> //= p b. 
  + by case: b=> //= p'; case: p'=> //=.
  + by case: b=> //= p'; case: p'=> //=.
  by case: p=> //= p; case: p=> //=.
(* neq *)
+ move=> v1 v2 t1 t2 v;case: v1=> //=; case: v2 => //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= [] [] hv; subst.
  + by case: t1=> //= p i i'; case: p=> //=; case: t2=> //= p sz s; case: p=> //= sz' s'; case: s=> //=;
    case: s'=> //=; case: sz=> //=; case: sz'=> //= [] [] hv; subst.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= b b' [] hb; subst.
  case: t1=> //= i b; case: b=> //= p; case: p=> //=; case: t2=> //= b; case: b=> //= p b. 
  + by case: b=> //= p'; case: p'=> //=.
  + by case: b=> //= p'; case: p'=> //=.
  by case: p=> //= p; case: p=> //=.
(* lt *)
+ move=> v1 v2 t1 t2 v;case: v1=> //=; case: v2 => //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= [] [] hv; subst.
  + by case: t1=> //= p i i'; case: p=> //=; case: t2=> //= p sz s; case: p=> //= sz' s'; case: s=> //=;
    case: s'=> //=; case: sz=> //=; case: sz'=> //= [] [] hv; subst.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= b b' [] hb; subst.
  case: t1=> //= i b; case: b=> //= p; case: p=> //=; case: t2=> //= b; case: b=> //= p b. 
  + by case: b=> //= p'; case: p'=> //=.
  + by case: b=> //= p'; case: p'=> //=.
  by case: p=> //= p; case: p=> //=.
(* lte *)
+ move=> v1 v2 t1 t2 v;case: v1=> //=; case: v2 => //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= [] [] hv; subst.
  + by case: t1=> //= p i i'; case: p=> //=; case: t2=> //= p sz s; case: p=> //= sz' s'; case: s=> //=;
    case: s'=> //=; case: sz=> //=; case: sz'=> //= [] [] hv; subst.
  + by case: t1=> //= p b b'; case: p=> //=; case: t2=> //= p; case: p=> //=; case: ifP=> //= hb [] hv; subst.
  by case: t1=> //= i b; case: b=> //= p; case: p=> //=; case: t2=> //= i' b; case: b=> //= p; case: p=> //=.
(* gt *)
+ move=> v1 v2 t1 t2 v;case: v1=> //=; case: v2 => //=.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= [] [] hv; subst.
  + by case: t1=> //= p i i'; case: p=> //=; case: t2=> //= p sz s; case: p=> //= sz' s'; case: s=> //=;
    case: s'=> //=; case: sz=> //=; case: sz'=> //= [] [] hv; subst.
  + by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= b b' [] hb; subst.
  case: t1=> //= i b; case: b=> //= p; case: p=> //=; case: t2=> //= b; case: b=> //= p b. 
  + by case: b=> //= p'; case: p'=> //=.
  + by case: b=> //= p'; case: p'=> //=.
  by case: p=> //= p; case: p=> //=.
(* gte *)
 move=> v1 v2 t1 t2 v;case: v1=> //=; case: v2 => //=.
+ by case: t1=> //= p; case: p=> //=; case: t2=> //= p; case: p=> //= [] [] hv; subst.
+ by case: t1=> //= p i i'; case: p=> //=; case: t2=> //= p sz s; case: p=> //= sz' s'; case: s=> //=;
  case: s'=> //=; case: sz=> //=; case: sz'=> //= [] [] hv; subst.
+ by case: t1=> //= p b b'; case: p=> //=; case: t2=> //= p; case: p=> //=; case: ifP=> //= hb [] hv; subst.
by case: t1=> //= i b; case: b=> //= p; case: p=> //=; case: t2=> //= i' b; case: b=> //= p; case: p=> //=.
Qed.


