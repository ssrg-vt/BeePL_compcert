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

Definition typeof_value (v : value ) (t : type) : Prop :=
match v,t with 
| Vunit, Ptype (Tunit) => True
| Vint i, Ptype (Tint) => True
| Vuint i, Ptype (Tuint) => True
| Vbool b, Ptype (Tbool) => True
| Vloc p, Reftype _ (Bprim (Tint)) => True
| _, _ => False
end.

Definition vals := list value.

Fixpoint typeof_values (vs : list value) (ts : list type) : Prop :=
match vs, ts with 
| nil, nil => True
| v :: vs, t :: ts => typeof_value v t /\ typeof_values vs ts
| _, _ => False
end.

Definition of_bool (b : bool) : value := Vbool b.

Definition of_int (i : int) : value := Vint i.

Definition loc := positive. 

Definition heap := list (loc * value).

Definition vmap := list (ident * value).

Fixpoint is_mem_vmap (x : ident) (l : list ident) {struct l} : bool :=
match l with 
| nil => false
| y :: ys => if (x =? y)%positive then true else is_mem_vmap x ys
end.

Fixpoint is_mem_heap (x : loc) (l : list loc) {struct l} : bool :=
match l with 
| nil => false
| y :: ys => if (x =? y)%positive then true else is_mem_heap x ys
end.

Fixpoint update_heap (h : heap) (k : loc) (v : value) : heap := 
match h with 
| nil => (k, v) :: nil
| h :: t => if (k =? fst(h))%positive then (k, v) :: t else h :: update_heap t k v
end.

Definition fresh_loc (h : heap) (l : loc) : bool :=
negb(is_mem_heap l (unzip1 h)).

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

Definition valid_access_vmap (x : ident) (vm : vmap) : Prop :=
is_mem_vmap x (unzip1 vm) = true.

Fixpoint valid_access_vmaps (x : list ident) (vm : vmap) : Prop :=
match x with 
| nil => True 
| x :: xs => valid_access_vmap x vm /\ valid_access_vmaps xs vm
end. 


