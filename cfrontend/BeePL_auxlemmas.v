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

Lemma extract_type_sub2 : forall v1 v2 t1 t2 v,
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


