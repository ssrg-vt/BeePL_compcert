Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Ctypes Errors.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

Inductive effect_label : Type :=
| Panic : effect_label               (* exception effect *)
| Divergence : effect_label          (* divergence effect *)
| Read : ident -> effect_label       (* read heap effect *)
| Write : ident -> effect_label      (* write heap effect *)
| Alloc : ident -> effect_label      (* allocation heap effect *).

Definition effect := list effect_label.  (* row of effects *)

Inductive type : Type :=
| Tunit : type
| Tint : intsize -> signedness -> attr -> type
| Tlong : signedness -> attr -> type               (* primitive types *)
| Reftype : ident -> type -> attr -> type          (* reference type ref<h,int> *)
| Ftype : list type -> effect -> type -> type       (* function/arrow type *).

Fixpoint sizeof_type (t : type) : Z :=
match t with 
| Tunit => 1
| Tint I8 _ _ => 1
| Tint I16 _ _ => 2
| Tint I32 _ _ => 4
| Tint IBool _ _ => 1
| Tlong _ _ => 8
| Reftype h t _ => sizeof_type t + 1 (* 1 taking for the h *)
| Ftype ts e t => 1
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

Section Eq_types.

Variable eq_type : type -> type -> bool.

Fixpoint eq_types (t1 t2: list type) : bool :=
match t1, t2 with 
| nil, nil => true 
| x :: xs, x' :: xs' => eq_type x x' && eq_types xs xs'
| _, _ => false
end.

End Eq_types.

Fixpoint eq_type (p1 p2 : type) : bool :=
match p1, p2 with 
| Tunit, Tunit => true 
| Tint sz s a, Tint sz' s' a'=> if intsize_eq sz sz' 
                                then if signedness_eq s s'
                                     then if attr_eq a a'
                                          then true 
                                          else false
                                     else false
                                else false
| Tlong s a, Tlong s' a' => if signedness_eq s s'
                            then if attr_eq a a'
                                 then true 
                                 else false
                            else false
| Ftype ts1 e1 t1, Ftype ts2 e2 t2 => 
  eq_types eq_type ts1 ts2 && eq_effect e1 e2 && eq_type t1 t2
| Reftype e1 b1 a1, Reftype e2 b2 a2 => if attr_eq a1 a2  
                                        then (e1 =? e2)%positive && eq_type b1 b2
                                        else false
| _, _ => false
end.   

(** ** Access modes *)

(** The [access_mode] function describes how a l-value of the given
type must be accessed:
- [By_value ch]: access by value, i.e. by loading from the address
  of the l-value using the memory chunk [ch];
- [By_reference]: access by reference, i.e. by just returning
  the address of the l-value (used for arrays and functions);
- [By_copy]: access is by reference, assignment is by copy
  (used for [struct] and [union] types)
- [By_nothing]: no access is possible, e.g. for the [void] type.
*)

Definition access_mode (t : type) : mode :=
match t with 
| Tunit => By_nothing
| Tint I8 Signed _ => By_value Mint8signed
| Tint I8 Unsigned _ => By_value Mint8unsigned
| Tint I16 Signed _ => By_value Mint16signed
| Tint I16 Unsigned _ => By_value Mint16unsigned
| Tint I32 _ _ => By_value Mint32
| Tint IBool _ _ => By_value Mbool
| Tlong _ _ => By_value Mint64
| Reftype h t _ => By_value Mptr
| Ftype ts ef t => By_reference
end.

(****** Translation from BeePL types to Csyntax types ******)

Section translate_types.

Variable transBeePL_type : BeeTypes.type -> res Ctypes.type.

(* Translates a list of BeePL types to list of Clight types *) 
Fixpoint transBeePL_types (ts : list BeeTypes.type) : res Ctypes.typelist :=
match ts with 
| nil => OK Tnil
| t :: ts => do ct <- (transBeePL_type t);
             do cts <- (transBeePL_types ts);
             OK (Tcons ct cts)
end.

End translate_types.

Fixpoint typelist_list_type (ts : Ctypes.typelist) : list Ctypes.type :=
match ts with
| Tnil => nil
| Tcons t ts => t :: typelist_list_type ts
end. 

(* Translation of BeePL types to Clight Types *)
Fixpoint transBeePL_type (t : BeeTypes.type) : res Ctypes.type :=
match t with 
| Tunit => OK (Ctypes.Tint I8 Unsigned {| attr_volatile := false; attr_alignas := Some 1%N |}) (* Fix me *)
| Tint sz s a => OK (Ctypes.Tint sz s a)
| Tlong s a => OK (Ctypes.Tlong s a)
| Reftype h t a => do ct <- transBeePL_type t;
                 OK (Tpointer ct a)
| BeeTypes.Ftype ts ef t => do ats <- (transBeePL_types transBeePL_type ts);
                            do rt <- (transBeePL_type t);
                            OK (Tfunction ats rt {| cc_vararg := Some (Z.of_nat(length(ts))); cc_unproto := false; cc_structret := false |})  
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
