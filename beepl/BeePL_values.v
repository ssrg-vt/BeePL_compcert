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
| ConsBool : bool -> constant
| ConsInt : int -> constant
| ConsLong : int64 -> constant
| ConsUnit : constant.

Definition is_zero_constant (c : constant) : bool :=
match c with 
| ConsBool b => false
| ConsInt i => if Int.eq i Int.zero then true else false
| ConsLong i => if Int64.eq i Int64.zero then true else false
| ConsUnit => false
end.

Definition is_overflow_constant (c1 c2 : constant) : bool :=
match c1, c2 with 
| ConsInt i1, ConsInt i2 => if Int.eq i1 (Int.repr Int.min_signed) 
                               && Int.eq i2 Int.mone then true else false
| ConsLong i1, ConsLong i2 => if Int64.eq i1 (Int64.repr Int.min_signed) 
                                 && Int64.eq i2 Int64.mone then true else false 
| _, _ => false
end.

Definition is_constant_min_signed (c : constant) : bool :=
match c with 
| ConsInt i => if Int.eq i (Int.repr Int.min_signed) then true else false
| ConsLong i => if Int64.eq i (Int64.repr Int.min_signed) then true else false 
| _ => false
end.

Definition is_constant_mone (c : constant) : bool :=
match c with 
| ConsInt i => if Int.eq i Int.mone then true else false
| ConsLong i => if Int64.eq i Int64.mone then true else false 
| _ => false
end.

Definition is_constant_shift (c : constant) : bool :=
match c with 
| ConsInt i => if negb (Int.ltu i Int.iwordsize) then true else false
| ConsLong i => if negb (Int64.ltu i Int64.iwordsize) then true else false
| _ => false
end.

(*Record vinfo : Type := mkvar { vname : ident; vtype : BeeTypes.basic_type }.*)
Record linfo : Type := mkloc { lname : ident; (*ltype : BeeTypes.basic_type;*) lbitfield : bitfield }.

Inductive value : Type :=
| Vunit : value
| Vbool : bool -> value
| Vint : int -> value
| Vint64 : int64 -> value
| Vloc : positive -> ptrofs -> value.

Definition is_vloc (v : value) : bool :=
match v with 
| Vunit => false
| Vbool b => false
| Vint i => false 
| Vint64 l => false
| Vloc l ofs => true 
end.

Definition is_zero_val (v : value) : bool :=
match v with 
| Vunit => false
| Vbool b => false
| Vint i => if Int.eq i Int.zero then true else false
| Vint64 i => if Int64.eq i Int64.zero then true else false
| Vloc p ofs => false
end.

Definition is_overflow_vals (v1 v2 : value) : bool :=
match v1, v2 with 
| Vint i1, Vint i2 => if Int.eq i1 (Int.repr Int.min_signed) 
                         && Int.eq i2 Int.mone then true else false
| Vint64 i1, Vint64 i2 => if Int64.eq i1 (Int64.repr Int.min_signed) 
                             && Int64.eq i2 Int64.mone then true else false 
| _, _ => false
end.

Definition is_val_min_signed (v : value) : bool :=
match v with 
| Vint i => Int.eq i (Int.repr Int.min_signed)
| Vint64 i => Int64.eq i (Int64.repr Int64.min_signed)
| _ => false
end.

Definition is_val_mone (v : value) : bool :=
match v with 
| Vint i => Int.eq i Int.mone 
| Vint64 i => Int64.eq i Int64.mone 
| _ => false
end.

Definition is_val_shift (v : value) : bool :=
match v with 
| Vint i => if negb (Int.ltu i Int.iwordsize) then true else false
| Vint64 i => if negb (Int64.ltu i Int64.iwordsize) then true else false
| _ => false
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
| Vbool b, BeeTypes.Twbool => True
| Vint i, BeeTypes.Twint => True 
| Vint64 i, BeeTypes.Twlong => True 
| Vloc p ofs, BeeTypes.Twref => True
| _, _ => False
end.

Definition typeof_value (v : value) (t : type) : Prop :=
match v, t with 
| Vunit, Ptype Tunit => True 
| Vbool b, Ptype Tbool => True
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

Definition return_bzero (t : type) : mon value :=
match t with 
| Ptype p => match p with   
             | Tunit => error (msg "Tunit not allowed")
             | Tbool => error (msg "Tbool not allowed")
             | Tint i s a => ret (Vint (Int.repr 0))
             | Tlong s a => ret (Vint64 (Int64.repr 0))
             end
| Reftype h b a => error (msg "Tpointer not allowed")
| Ftype ts e t => error (msg "Tfunction not allowed")
end.
