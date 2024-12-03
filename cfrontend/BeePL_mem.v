(*Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Memory compcert.lib.Coqlib.
Require Import BeePL_aux BeeTypes Axioms.
From mathcomp Require Import all_ssreflect. 

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Record vinfo : Type := mkvar { vname : ident; vtype : type }.
Record linfo : Type := mkloc { lname : ident; ltype : type }.

Inductive value : Type :=
| Vunit : value
| Vint : int -> value
| Vbool : bool -> value
| Vloc : linfo -> value.

Definition typeof_value (v : value ) (t : type) : Prop :=
match v,t with 
| Vunit, Ptype (Tunit) => True
| Vint i, Ptype (Tint _ _) => True
| Vbool b, Ptype (Tbool) => True
| Vloc p, Reftype _ _ => True
| _, _ => False
end.

Definition vals := list value.

Definition of_bool (b : bool) : value := Vbool b.

Definition of_int (i : int) : value := Vint i.

Fixpoint typeof_values (vs : list value) (ts : list type) : Prop :=
match vs, ts with 
| nil, nil => True
| v :: vs, t :: ts => typeof_value v t /\ typeof_values vs ts
| _, _ => False
end.

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

(*Definition heap := list (linfo * value).*)

Module Type HEAP.
Parameter heap : Type.
(* operations on heap *)

(* Initial heap state *)
Parameter empty : heap. 

(* [alloc m l] allocates a fresh location l *)
Parameter alloc : heap -> heap * linfo.

(* [free m l] deallocates a location l *)
(*Parameter free : heap -> linfo -> heap.*)

(* [load m l] reads the memory at location l and returns the value (option type)*) 
Parameter load : forall (m : heap) (l : linfo), option value.

(* [store m l v] stores the value v at location l in the memory m and returns the updated memory *)
(* Should include some cases where we are not allowed to write at an address and it return None *)
Parameter store : forall (m : heap) (l : linfo) (v : value), option heap.

(* Loadv defines the load operation when address is passed as a value *)
Definition loadv (m : heap) (addr : value) : option value :=
match addr with 
| Vloc l => load m l
| _ => None
end.

(* Storev defines the store operation when address is passed as a value *)
Definition storev (m : heap) (addr : value) (v : value) : option heap :=
match addr with 
| Vloc l => store m l v
| _ => None
end.

(* next_location represents the location for next allocation. 
   It increases by one for each allocation. Locations above next_location
   are fresh and invalid, i.e. not yet allocated. *)

Parameter next_location : heap -> linfo.

Definition valid_location (m : heap) (l : linfo) := Plt l.(lname) (next_location m).(lname).

(* An address is valid if it is nonempty in memory m 
Parameter valid_address: forall (m: heap) (l: linfo), bool.*)

End HEAP.

Module Heap <: HEAP.

Record heap' : Type := 
mkheap { heap_content : PMap.t (value);  (* location -> offset -> value *)
         next_location : linfo }.


(* The memory/heap maps references/locations to values *)
Definition heap := heap'.

(* Validity of locations: an address is valid if it was previously allocated *)
Definition valid_location (m: heap) (l: linfo) := Plt l.(lname) (next_location m).(lname).

Theorem valid_not_valid_diff:
  forall m l l', valid_location m l -> ~(valid_location m l') -> l.(lname) <> l'.(lname).
Proof.
  intros; red; intros; subst. rewrite /valid_location in H0 H; subst. 
  rewrite /not in H0. rewrite -H1 in H0. by move: (H0 H).
Qed.

(* Fix me: add more checks later *)
Definition valid_access (m : heap) (l : linfo) : Prop :=
valid_location m l.

Lemma valid_access_dec: forall m l,
{valid_access m l} + {~ valid_access m l}.
Proof. 
move=> m l. case: m=> //= hc hl. case: hl=> //= ln lt.
case: l=> //= ln' lt'. rewrite /valid_access /valid_location /=.
by apply plt.
Qed.

(* Load performs read at an address addr in the memory m *)
Definition load (m : heap) (addr : linfo) : option value :=
if valid_access_dec m addr 
then Some (PMap.get addr.(lname) m.(heap_content)) 
else None.

Definition loadv (m : heap) (addr : value) : option value :=
match addr with 
| Vloc l => load m l
| _ => None
end.

(* Store performs write at an address addr with the value v *)
Definition store (m : heap) (addr : linfo) (v : value) : option heap :=
if valid_access_dec m addr 
then Some (mkheap (PMap.set addr.(lname) v m.(heap_content)) m.(next_location)) 
else None.

(* Storev defines the store operation when address is passed as a value *)
Definition storev (m : heap) (addr : value) (v : value) : option heap :=
match addr with 
| Vloc l => store m l v
| _ => None
end.

Definition empty : heap := {| heap_content := (PMap.init (Vunit)); 
                              next_location := {| lname := 1%positive; ltype := (Ptype Tunit) |} |}.

(* Allocates a fresh location i.e. the next location after all allocated ones *)
Definition alloc (m : heap) :=
({| heap_content := PMap.set m.(next_location).(lname) Vunit m.(heap_content);
   next_location := {| lname := Pos.succ m.(next_location).(lname); ltype := m.(next_location).(ltype) |} |}, 
 m.(next_location)).

End Heap.

(***** Virtual map *****)

(** The local environment maps local variables to references/locations and types.
  The current value of the variable is stored in the associated memory
  location. *)
Definition vmap := PTree.t (positive * type). (* map variable -> location & type *)

(*Definition vmap := list (vinfo * value).*)

Notation heap := Heap.heap.

(* Treated as Opaque in all context withing the entire module or file, means the definitions
   will not be unfolded automatically during the proofs *)
Global Opaque Heap.alloc Heap.store Heap.load.
*)
