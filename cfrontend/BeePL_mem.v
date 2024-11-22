Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps.
Require Import BeePL_aux BeeTypes.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Inductive value : Type :=
| Vunit : value
| Vint : int -> value
| Vbool : bool -> value
| Vloc : positive -> value.

Definition typeof_value (v : value ) (t : type) : Prop :=
match v,t with 
| Vunit, Ptype (Tunit) => True
| Vint i, Ptype (Tint _ _) => True
| Vbool b, Ptype (Tbool) => True
| Vloc p, Reftype _ (Bprim (Tint _ _)) => True
| _, _ => False
end.

Definition vals := list value.

Fixpoint typeof_values (vs : list value) (ts : list type) : Prop :=
match vs, ts with 
| nil, nil => True
| v :: vs, t :: ts => typeof_value v t /\ typeof_values vs ts
| _, _ => False
end.

Definition loc := positive.

Definition of_bool (b : bool) : value := Vbool b.

Definition of_int (i : int) : value := Vint i.

Record vinfo : Type := mkvar { vname : ident; vtype : type }.
Record linfo : Type := mkloc { lname : loc; ltype : type }.

Fixpoint extract_types_vinfos (vs : list vinfo) : list type :=
match vs with 
| nil => nil
| v :: vs => v.(vtype) :: extract_types_vinfos vs
end.

Fixpoint extract_types_linfos (vs : list linfo) : list type :=
match vs with 
| nil => nil
| v :: vs => v.(ltype) :: extract_types_linfos vs
end.

Fixpoint extract_vars_vinfos (vs : list vinfo) : list ident :=
match vs with 
| nil => nil
| v :: vs => v.(vname) :: extract_vars_vinfos vs
end.

Fixpoint extract_locs_linfos (vs : list linfo) : list loc :=
match vs with 
| nil => nil
| v :: vs => v.(lname) :: extract_locs_linfos vs
end.

Fixpoint extract_list_rvtypes (l : list BeePL_mem.vinfo) : list (ident * type) :=
match l with 
| nil => nil
| x :: xs => (x.(vname), x.(vtype)) :: extract_list_rvtypes xs
end.

Definition eq_vinfo (v1 : vinfo) (v2 : vinfo) : bool :=
if (v1.(vname) =? v2.(vname))%positive && (eq_type v1.(vtype) v2.(vtype)) then true else false.

Definition eq_linfo (v1 : linfo) (v2 : linfo) : bool :=
if (v1.(lname) =? v2.(lname))%positive && (eq_type v1.(ltype) v2.(ltype)) then true else false.

Definition heap := list (linfo * value).

Definition vmap := list (vinfo * value).

Fixpoint is_mem_vmap (x : vinfo) (l : vmap) {struct l} : bool :=
match l with 
| nil => false
| y :: ys => if eq_vinfo x (fst y) then true else is_mem_vmap x ys
end.

Fixpoint is_mem_heap (x : linfo) (l : heap) {struct l} : bool :=
match l with 
| nil => false
| y :: ys => if eq_linfo x (fst y) then true else is_mem_heap x ys
end.

Fixpoint update_heap (h : heap) (k : linfo) (v : value) : heap := 
match h with 
| nil => (k, v) :: nil
| h :: t => if (eq_linfo k (fst h)) then (k, v) :: t else h :: update_heap t k v
end.

Definition fresh_loc (h : heap) (l : linfo) : bool :=
negb(is_mem_heap l h).

Fixpoint write_var (h : vmap) (k : vinfo) (v : value) : vmap := 
match h with 
| nil => (k, v) :: nil
| h :: t => if (eq_vinfo k (fst h)) then (k, v) :: t else h :: write_var t k v
end.

Fixpoint write_vars (h : vmap) (ks : list vinfo) (vs : list value) : result error vmap :=
match ks, vs with 
| nil, nil => Ok error h
| k :: ks, v :: vs => (write_vars (write_var h k v) ks vs)
| _, _ => Error vmap ErrNotAllowed
end. 

Fixpoint get_val_loc (h : heap) (k : linfo) : option value :=
match h with 
| nil => None 
| v :: vm => if (eq_linfo k (fst v)) then Some (snd(v)) else get_val_loc vm k
end.

Fixpoint get_val_var (h : vmap) (k : vinfo) : option value :=
match h with 
| nil => None 
| v :: vm => if (eq_vinfo k (fst v)) then Some (snd(v)) else get_val_var vm k
end.

(* State is made from heap and virtual map (registers to values) *)
Record state : Type := mkstate {hmem : heap; vmem : vmap}.

Definition valid_access_vmap (x : vinfo) (vm : vmap) : Prop :=
is_mem_vmap x vm = true.

Fixpoint valid_access_vmaps (x : list vinfo) (vm : vmap) : Prop :=
match x with 
| nil => True 
| x :: xs => valid_access_vmap x vm /\ valid_access_vmaps xs vm
end. 

