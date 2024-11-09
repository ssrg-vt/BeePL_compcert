Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps.
Require Import BeePL_aux BeeTypes.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Inductive value : Type :=
| Vunit : value
| Vint : int -> value
| Vuint : int -> value
| Vbool : bool -> value
| Vloc : positive -> value.

Definition typeof_value (v : value ) : type :=
match v with 
| Vunit => Ptype (Tunit)
| Vint i => Ptype (Tint)
| Vuint i => Ptype (Tuint)
| Vbool b => Ptype (Tbool)
| Vloc p => Ptype (Tunit) 
end.

Definition vals := list value.

Fixpoint typeof_values (vs : list value) : list type :=
match vs with 
| nil => nil
| v  :: vs => typeof_value v :: typeof_values vs 
end.

Definition of_bool (b : bool) : value := Vbool b.

Definition of_int (i : int) : value := Vint i.

Definition loc := positive. 

Definition heap := list (loc * value).

Definition vmap := list (ident * value).

Fixpoint update_heap (h : heap) (k : loc) (v : value) : heap := 
match h with 
| nil => (k, v) :: nil
| h :: t => if (k =? fst(h))%positive then (k, v) :: t else h :: update_heap t k v
end.

Fixpoint write_var (h : vmap) (k : ident) (v : value) : vmap := 
match h with 
| nil => (k, v) :: nil
| h :: t => if (k =? fst(h))%positive then (k, v) :: t else h :: write_var t k v
end.

Fixpoint write_vars (h : vmap) (ks : list ident) (vs : list value) : result error vmap :=
match ks, vs with 
| nil, nil => Ok error h
| k :: ks, v :: vs => (write_vars (write_var h k v) ks vs)
| _, _ => Error vmap ErrNotAllowed
end. 

Fixpoint get_val_loc (h : heap) (k : loc) : option value :=
match h with 
| nil => None 
| v :: vm => if (k =? fst(v))%positive then Some (snd(v)) else get_val_loc vm k
end.

Fixpoint get_val_var (h : vmap) (k : ident) : option value :=
match h with 
| nil => None 
| v :: vm => if (k =? fst(v))%positive then Some (snd(v)) else get_val_var vm k
end.

(* State is made from heap and virtual map (registers to values) *)
Record state : Type := mkstate {hmem : heap; vmem : vmap}.

Fixpoint mem (x : ident) (l : list ident) {struct l} : bool :=
match l with 
| nil => false
| y :: ys => if (x =? y)%positive then true else mem x ys
end. 

Definition valid_access_vmap (x : ident) (vm : vmap) : Prop :=
mem x (unzip1 vm) = true.

Fixpoint valid_access_vmaps (x : list ident) (vm : vmap) : Prop :=
match x with 
| nil => True 
| x :: xs => valid_access_vmap x vm /\ valid_access_vmaps xs vm
end. 


