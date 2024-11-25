Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST.

Inductive effect_label : Type :=
| Panic : effect_label               (* exception effect *)
| Divergence : effect_label          (* divergence effect *)
| Read : ident -> effect_label       (* read heap effect *)
| Write : ident -> effect_label      (* write heap effect *)
| Alloc : ident -> effect_label      (* allocation heap effect *).

Definition effect := list effect_label.  (* row of effects *)

Inductive signedness : Type :=
| Signed: signedness
| Unsigned: signedness.

Inductive intsize : Type :=
| I8: intsize
| I16: intsize
| I32: intsize.

Inductive primitive_type : Type :=
| Tunit : primitive_type
| Tint : intsize -> signedness -> primitive_type
| Tbool : primitive_type.

Inductive basic_type : Type :=  
| Bprim : primitive_type -> basic_type.

Inductive type : Type :=
| Ptype : primitive_type -> type                          (* primitive types *)
| Reftype : ident -> basic_type -> type                   (* reference type ref<h,int> *)
| Ftype : list type -> effect -> type -> type             (* function/arrow type *).

Definition sizeof_ptype (t : primitive_type) : Z :=
match t with 
| Tunit => 1
| Tint I8 _ => 1
| Tint I16 _ => 2
| Tint I32 _ => 4
| Tbool => 1
end.

Definition sizeof_btype (t : basic_type) : Z :=
match t with 
| Bprim t => sizeof_ptype t 
end. 

Definition sizeof_type (t : type) : Z :=
match t with 
| Ptype t => sizeof_ptype t 
| Reftype h t => sizeof_btype t + 1 (* 1 taking for the h *)
| Ftype ts e t => 1
end.

(* Equality on types *)
Definition eq_signedness (sg1 sg2 : signedness) : bool :=
match sg1, sg2 with 
| Signed, Signed => true 
| Unsigned, Unsigned => true 
| _, _ => false
end.

Definition eq_intsize (i1 i2: intsize) : bool :=
match i1, i2 with 
| I8, I8 => true 
| I16, I16 => true 
| I32, I32 => true 
| _, _ => false
end.

Definition eq_effect_label (e1 e2 : effect_label) : bool :=
match e1, e2 with 
| Panic, Panic => true 
| Divergence, Divergence => true 
| Read id1, Read id2 => (id1 =? id2)%positive
| Write id1, Read id2 => (id1 =? id2)%positive
| Alloc id1, Alloc id2 => (id1 =? id2)%positive
| _, _ => false
end.

Fixpoint eq_effect (es1 es2 : effect) : bool :=
match es1, es2 with 
| nil, nil => true 
| e :: es, e' :: es' => eq_effect_label e e' && eq_effect es es'
| _, _ => false
end.

Definition eq_primitive_type (p1 p2 : primitive_type) : bool :=
match p1, p2 with 
| Tunit, Tunit => true 
| Tint sz s, Tint sz' s'=> eq_intsize sz sz' && eq_signedness s s'
| Tbool, Tbool => true
| _, _ => false
end.   

Section Eq_basic_types.

Variable eq_basic_type : basic_type -> basic_type -> bool.

Fixpoint eq_basic_types (bs1 bs2 : list basic_type) : bool :=
match bs1, bs2 with 
| nil, nil => true 
| x :: xs, x' :: xs' => eq_basic_type x x' && eq_basic_types xs xs'
| _, _ => false
end.

End Eq_basic_types.

Definition eq_basic_type (b1 b2 : basic_type) : bool :=
match b1, b2 with 
| Bprim p1, Bprim p2 => eq_primitive_type p1 p2
end.

Section Eq_types.

Variable eq_type : type -> type -> bool.

Fixpoint eq_types (t1 t2: list type) : bool :=
match t1, t2 with 
| nil, nil => true 
| x :: xs, x' :: xs' => eq_type x x' && eq_types xs xs'
| _, _ => false
end.

End Eq_types.

Fixpoint eq_type (t1 t2 : type) : bool :=
match t1,t2 with 
| Ptype b1, Ptype b2 => eq_primitive_type b1 b2
| Ftype ts1 e1 t1, Ftype ts2 e2 t2 => 
  eq_types eq_type ts1 ts2 && eq_effect e1 e2 && eq_type t1 t2
| Reftype e1 b1, Reftype e2 b2 => (e1 =? e2)%positive && eq_basic_type b1 b2 
| _, _ => false
end.


(* Typing context *)
Definition ty_context := list (ident * type).
(* To ensure that a location does not contain another location (ref) 
   and only points to basic types like int, bool, unit or pair *)
Definition store_context := list (ident * type).   

Fixpoint remove_var_ty (t : ty_context) (k : ident) (T : type) : ty_context :=
match t with 
| nil => nil 
| x :: xs => if (k =? fst(x))%positive && (eq_type T (snd(x))) then xs else x :: remove_var_ty xs k T
end.

Fixpoint is_mem (k : ident) (t : ty_context) : bool :=
match t with 
| nil => false
| x :: xs => if (k =? fst(x))%positive then true else is_mem k xs
end.

Fixpoint extend_context (t : ty_context) (k : ident) (v : type) : ty_context := 
match t with 
| nil => ((k, v) :: nil)
| h :: t => if (k =? fst(h))%positive then (k, v) :: t else h :: extend_context t k v
end. 

Fixpoint append_context (t1 : ty_context) (t2 : ty_context) : ty_context :=
match t2 with 
| nil => t1
| h :: t =>  append_context (extend_context t1 (fst(h)) (snd(h))) t
end.

Fixpoint get_ty (t : ty_context) (k : ident) : option type :=
match t with 
| nil => None 
| x :: xs => if (fst(x) =? k)%positive then Some (snd(x)) else get_ty xs k
end.

Fixpoint extend_contexts (t : ty_context) (ks : list (ident * type)) : ty_context := 
match ks with 
| nil => t
| k :: ks => extend_contexts (extend_context t (fst(k)) (snd(k))) ks
end. 

Fixpoint get_sty (t : store_context) (k : ident) : option type :=
match t with 
| nil => None 
| x :: xs => if (fst(x) =? k)%positive then Some (snd(x)) else get_sty xs k
end.
