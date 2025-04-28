Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Coq.Lists.List.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes Ctyping Cop.
Require Import BeePL_aux BeePL BeePL_values BeeTypes BeePL_mem Errors Csyntaxdefs.
From mathcomp Require Import all_ssreflect. 

(**** Value notations ****)
Notation " 'Vu' " := Vunit (at level 0).
Notation " 'Vb' b " := (Vbool b) (at level 0).
Notation " 'Vi' i " := (Vint i) (at level 0).
Notation " 'Vl' l" := (Vint64 l) (at level 0).
Notation " 'Ptr' p ofs " := (Vloc p ofs) (at level 0).

(**** Constant notations ****)
Notation " 'Cu' " := ConsUnit (at level 0).
Notation " 'Cb' b " := (ConsBool b) (at level 0).
Notation " 'Ci' i " := (ConsInt i) (at level 0).
Notation " 'Cl' l" := (ConsLong l) (at level 0).

(**** Effect labels ****)
Notation " 'Panic' " := Panic (at level 0).
Notation " 'Divergence' " := Divergence (at level 0).
Notation " 'Read''<' h '>' " := (Read h) (at level 0).
Notation " 'Write''<' h '>' " := (Write h) (at level 0).
Notation " 'Alloc''<' h '>' " := (Alloc h) (at level 0).
Notation " 'Hstate''<' h '>' " := (Hstate h) (at level 0).

(**** Effect ****)
Notation "x +ef y" := (x ++ y)%list (at level 60, right associativity) : effect_scope.
Notation "[ ]" := (@nil effect_label) : effect_scope.
Notation "[ x ]" := (cons x nil) : effect_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : effect_scope.

(**** Primitive type ****)
Notation " 'tu' " := Tunit (at level 0).
Notation " 'bool''<' b '>' " := (Tbool b) (at level 0).
Notation " 'int' '(' sz ',' s ',' a ')' " := (Tint sz s a) (at level 0, only parsing).
Notation " 'int64 '(' s ',' a ')' " := (Tlong s a) (at level 0).

(**** Basic type ***)
Notation " 'btype' '(' p ')' " := (Bprim p) (at level 0).
Notation " 'bstype' '(' s ',' a ')' " := (Bstruct s a) (at level 0).

(**** Type ****)
Notation " 'prim' p " := (Ptype p) (at level 0).
Notation " 't*' '(' h ',' bt ',' a ')' " := (Reftype h bt a) (at level 0).
Notation " ts '->' '(' t ',' ef ')' " := (Ftype ts ef t) (at level 0).
Notation " 'struct' '(' h ',' a ')' " := (Stype h a) (at level 0).
Notation " 'option' '(' t ')' " := (Otype t) (at level 0).

(**** List type ****)
Notation "x +t y" := (x ++ y)%list (at level 60, right associativity) : type_scope.
Notation "[ ]" := (@nil type) : type_scope.
Notation "[ x ]" := (cons x nil) : type_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : type_scope.

(**** Expr ****)
Notation "v ':::' t" := (Val v t) (at level 40).
Notation "x ':::' t"  := (Var x t) (at level 40).
Notation "c ':::' t" := (Const c t) (at level 40).
Notation "'fun' '' e '(' es ')' '@' t " := (App e es t) (at level 50).
Notation "'ref*' es '@' t " := (Prim Ref es t) (at level 50).
Notation "'!' es '@' t " := (Prim Ref es t) (at level 50).
Notation "e1 ':=' es '@' t " := (Prim Massgn (e1 :: es) t) (at level 50).
Notation "uop '(' es ')' '@' t " := (Prim (Uop uop) es t) (at level 50).
Notation "bop '(' es ')' '@' t " := (Prim (Bop bop) es t) (at level 50).
Notation "'Let' x '@' t '<-' e 'IN' e' '@' t' " := (Bind x t e e' t') (at level 50).
Notation "'IfB' e1 'ThenB' e2 'ElseB' e3 '@' t " := (Cond e1 e2 e3 t) (at level 50).
Notation "'Unit' @ t" := (Unit t) (at level 50, left associativity).
Notation "'efun' '' ef '(' ts ',' es ')' '@' t " := (Eapp ef ts es t) (at level 50).
Notation "e '#' x '@' t" := (Sfield e x t) (at level 50).
Notation "'For' x '(|' e1 ',' e2 ',' dir '|)' '{' e '}'  '@' t " := (For x e1 e2 dir e t) (at level 70, right associativity).


(**** Expr type ****)
Notation "x +e y" := (x ++ y)%list (at level 60, right associativity) : expr_scope.
Notation "[ ]" := (@nil expr) : expr_scope.
Notation "[ x ]" := (cons x nil) : expr_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : expr_scope.


Definition tbool := Tbool.
Definition tint8u := Tint I8 Unsigned noattr.
Definition tint8s := Tint I8 Signed noattr.
Definition tint16u := Tint I16 Unsigned noattr.
Definition tint16s := Tint I16 Signed noattr.
Definition tint32u := Tint I32 Unsigned noattr.
Definition tint32s := Tint I32 Signed noattr.
Definition tlongu := Tlong Unsigned noattr.
Definition tlongs := Tlong Signed noattr.

Definition bbool := Bprim tbool.
Definition bint8u := Bprim tint8u.
Definition bint8s := Bprim tint8s.
Definition bint16u := Bprim tint16u.
Definition bint16s := Bprim tint16s.
Definition bint32u := Bprim tint32u.
Definition bint32s := Bprim tint32s.
Definition blongu := Bprim tlongu.
Definition blongs := Bprim tlongs.
Definition bstruct x := Bstruct x noattr.

