Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps.
Require Import BeeTypes.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Fixpoint unzip1 {A} {B} (es : list (A * B)) : list A :=
match es with 
| nil => nil
| e :: es => fst(e) :: unzip1 es
end.

Fixpoint unzip2 {A} {B} (es : list (A * B)) : list B :=
match es with 
| nil => nil
| e :: es => snd(e) :: unzip2 es
end.

Fixpoint zip {A} {B} (es1 : list A) (es2 : list B) : list (A * B) :=
match es1, es2 with 
| nil, nil => nil
| e1 :: es1, e2 :: es2 => (e1, e2) :: zip es1 es2
| _, _ => nil
end.

(*** Result Type ***)
Inductive error : Type :=
| ErrAddrInvalid
| ErrType
| ErrArith
| ErrNotAllowed.

(* Error or Ok state *)
Inductive result (E : Type) (A : Type) : Type :=
| Ok : A -> result E A
| Error : E -> result E A.

