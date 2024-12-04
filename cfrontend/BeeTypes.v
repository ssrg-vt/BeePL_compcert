Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Ctypes Errors.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

Inductive effect_label : Type :=
| Panic : effect_label               (* exception effect *)
| Divergence : effect_label          (* divergence effect *)
| Read : ident -> effect_label       (* read heap effect *)
| Write : ident -> effect_label      (* write heap effect *)
| Alloc : ident -> effect_label      (* allocation heap effect *).

Definition effect := list effect_label.  (* row of effects *)

Inductive primitive_type : Type :=
| Tunit : primitive_type
| Tint : intsize -> signedness -> attr -> primitive_type
| Tlong : signedness -> attr -> primitive_type.

Inductive basic_type : Type :=  
| Bprim : primitive_type -> basic_type.

Inductive type : Type :=
| Ptype : primitive_type -> type                          (* primitive types *)
| Reftype : ident -> basic_type -> attr -> type           (* reference type ref<h,int> *)
| Ftype : list type -> effect -> type -> type             (* function/arrow type *).

Inductive wtype : Type :=
| Twunit : wtype
| Twint : wtype
| Twlong : wtype.

(** The following describes types that can be interpreted as a boolean:
  integers, pointers.  It is used for the semantics of
  the [!] and [?] operators, as well as the [cond] expression *)

Inductive classify_bool_cases : Type :=
| bool_case_i     (**r integer *)
| bool_case_l     (**r long *)
| bool_default    (** default case to check if it does not have right type to represent bool *).

Definition classify_bool (t : type) : classify_bool_cases :=
match t with 
| Ptype t => match t with 
             | Tunit => bool_default
             | Tint _ _ _ => bool_case_i
             | Tlong _ _ => bool_case_l
             end
| Reftype _ _ _ => if Archi.ptr64 then bool_case_l else bool_case_i
| _ => bool_default
end.

Definition Twptr := if Archi.ptr64 then Twlong else Twint. 

Definition wtype_of_type (t : type) : wtype :=
match t with 
| Ptype p => match p with 
             | Tunit => Twunit 
             | Tint _ _ _ => Twint 
             | Tlong _ _ => Twlong 
             end
| Reftype _ _ _ => Twptr 
| Ftype _ _ _ => Twptr
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

Fixpoint eq_primitive_type (p1 p2 : primitive_type) : bool :=
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

Fixpoint eq_type (p1 p2 : type) : bool :=
match p1, p2 with 
| Ptype p1, Ptype p2 => eq_primitive_type p1 p1
| Ftype ts1 e1 t1, Ftype ts2 e2 t2 => 
  eq_types eq_type ts1 ts2 && eq_effect e1 e2 && eq_type t1 t2
| Reftype e1 b1 a1, Reftype e2 b2 a2 => if attr_eq a1 a2  
                                        then (e1 =? e2)%positive && eq_basic_type b1 b2
                                        else false
| _, _ => false
end. 

Definition eq_wtype (t1 t2 : wtype) : bool :=
match t1, t2 with 
| Twunit, Twunit => true 
| Twint, Twint => true 
| Twlong, Twlong => true 
| _, _ => false
end.  

Definition sizeof_ptype (t : primitive_type) : Z :=
match t with 
| Tunit => 1
| Tint I8 _ _ => 1
| Tint I16 _ _ => 2
| Tint I32 _ _ => 4
| Tint IBool _ _ => 1
| Tlong _ _ => 4
end.

Definition sizeof_btype (t : basic_type) : Z :=
match t with 
| Bprim t => sizeof_ptype t 
end. 

Definition sizeof_type (t : type) : Z :=
match t with 
| Ptype t => sizeof_ptype t 
| Reftype h t _ => sizeof_btype t
| Ftype ts e t => 1
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
Definition access_mode_prim (t : primitive_type) : mode :=
match t with 
| Tunit =>  By_nothing (* Fix me *)
| Tint I8 Signed _ => By_value Mint8signed
| Tint I8 Unsigned _ => By_value Mint8unsigned
| Tint I16 Signed _ => By_value Mint16signed
| Tint I16 Unsigned _ => By_value Mint16unsigned
| Tint I32 _ _ => By_value Mint32
| Tint IBool _ _ => By_value Mbool
| Tlong _ _ => By_value Mint64
end.

Definition access_mode_basic (t : basic_type) : mode :=
match t with 
| Bprim t => access_mode_prim t
end.

Definition access_mode (t : type) : mode :=
match t with 
| Ptype t => access_mode_prim t
| Reftype h t _ => By_value Mptr
| Ftype ts ef t => By_reference
end.

Definition attr_of_primitive_type (t : primitive_type) : attr :=
match t with 
| Tunit => noattr 
| Tint sz s a => a
| Tlong s a => a
end.

Definition attr_of_type (t : type) : attr :=
match t with 
| Ptype t => attr_of_primitive_type t
| Reftype h t a => a
| Ftype ts ef t => noattr
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
| Ptype t => match t with  
             | Tunit => OK (Ctypes.Tint I8 Unsigned {| attr_volatile := false; attr_alignas := Some 1%N |}) (* Fix me *)
             | Tint sz s a => OK (Ctypes.Tint sz s a)
             | Tlong s a => OK (Ctypes.Tlong s a)
             end
| Reftype h bt a => match bt with 
                    | Bprim Tunit => OK (Ctypes.Tpointer Ctypes.Tvoid a)
                    | Bprim (Tint sz s a) => OK (Ctypes.Tpointer (Ctypes.Tint sz s a) a)
                    | Bprim (Tlong s a) => OK (Ctypes.Tpointer (Ctypes.Tlong s a) a)
                    end
| BeeTypes.Ftype ts ef t => do ats <- (transBeePL_types transBeePL_type ts);
                            do rt <- (transBeePL_type t);
                            OK (Tfunction ats rt {| cc_vararg := Some (Z.of_nat(length(ts))); cc_unproto := false; cc_structret := false |}) (* Fix me *) 
end.

(* Typing context *)
Definition ty_context := PTree.t type.

(* To ensure that a location does not contain another location (ref) 
   and only points to basic types like int, bool, unit or pair *)
Definition store_context := PTree.t type.  

Definition extend_context (Gamma : ty_context) (k : ident) (t : type):= PTree.set k t Gamma. 

