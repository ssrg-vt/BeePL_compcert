Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Globalenvs compcert.lib.Coqlib Ctypes.
Require Import Memory Int Cop Memtype Errors Csem SimplExpr Events BeeTypes.
From mathcomp Require Import all_ssreflect. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope string_scope.
Local Open Scope gensym_monad_scope.

Inductive constant : Type :=
| ConsInt : int -> constant
| ConsLong : int64 -> constant
| ConsUnit : constant.

(*Record vinfo : Type := mkvar { vname : ident; vtype : BeeTypes.basic_type }.*)
Record linfo : Type := mkloc { lname : ident; (*ltype : BeeTypes.basic_type;*) lbitfield : bitfield }.

Inductive value : Type :=
| Vunit : value
| Vint : int -> value
| Vint64 : int64 -> value
| Vloc : positive -> ptrofs -> value.

Definition is_vloc (v : value) : bool :=
match v with 
| Vunit => false
| Vint i => false 
| Vint64 l => false
| Vloc l ofs => true 
end.

Definition is_vint64 (v : value) : bool :=
match v with 
| Vint64 _ => true 
| _ => false
end.

(* Pointer will be stores in a 64 bit value or 32 bit value *) 
Definition default_attr (t : type) := {| attr_volatile := false;  
                                         attr_alignas := (attr_alignas (attr_of_type t)) |}.

Definition wtypeof_value (v : value) (t :  BeeTypes.wtype) : Prop :=
match v, t with 
| Vunit, Twuint => True 
| Vint i, BeeTypes.Twint => True 
| Vint64 i, BeeTypes.Twlong => True 
| Vloc p ofs, BeeTypes.Twref => True
| _, _ => False
end.

Definition typeof_value (v : value) (t : type) : Prop :=
match v, t with 
| Vunit, (Ptype Tunit) => True 
| Vint i, Ptype (Tint sz s a) => True 
| Vint64 i, Ptype (Tlong s a) => True 
| Vloc p ofs, Reftype h b a => True (* targeting only 64 bit arch *)
| _, _ => False
end.

Definition vals := list value.

Definition of_int (i : int) : value := Vint i.

Fixpoint wtypeof_values (vs : list value) (ts : list BeeTypes.wtype) : Prop :=
match vs, ts with 
| nil, nil => True
| v :: vs, t :: ts => wtypeof_value v t /\ wtypeof_values vs ts
| _, _ => False
end.

Fixpoint typeof_values (vs : list value) (ts : list BeeTypes.type) : Prop :=
match vs, ts with 
| nil, nil => True
| v :: vs, t :: ts => typeof_value v t /\ typeof_values vs ts
| _, _ => False
end.

(*Fixpoint extract_types_vinfos (vs : list vinfo) : list BeeTypes.basic_type :=
match vs with 
| nil => nil
| v :: vs => v.(vtype) :: extract_types_vinfos vs
end.

Fixpoint extract_types_linfos (vs : list linfo) : list BeeTypes.basic_type :=
match vs with 
| nil => nil
| v :: vs => v.(ltype) :: extract_types_linfos vs
end.

Fixpoint extract_vars_vinfos (vs : list vinfo) : list ident :=
match vs with 
| nil => nil
| v :: vs => v.(vname) :: extract_vars_vinfos vs
end.*)

Fixpoint extract_locs_linfos (vs : list linfo) : list ident :=
match vs with 
| nil => nil
| v :: vs => v.(lname) :: extract_locs_linfos vs
end.

(*Fixpoint extract_list_rvtypes (l : list vinfo) : list (ident * BeeTypes.basic_type) :=
match l with 
| nil => nil
| x :: xs => (x.(vname), x.(vtype)) :: extract_list_rvtypes xs
end.

Definition eq_vinfo (v1 : vinfo) (v2 : vinfo) : bool :=
if (v1.(vname) =? v2.(vname))%positive && (eq_basic_type (vtype v1) (vtype v2)) then true else false.*)

(* add equality over bitfield *)
Definition eq_linfo (v1 : linfo) (v2 : linfo) : bool :=
if (v1.(lname) =? v2.(lname))%positive then true else false.
