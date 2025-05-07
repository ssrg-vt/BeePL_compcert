Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL PeanoNat Coq.NArith.BinNat Ctypes Errors Ctypes Coq.ZArith.Znumtheory.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps SimplExpr Coq.Strings.BinaryString  Coq.Numbers.DecimalString.
From mathcomp Require Import all_ssreflect. 
From compcert Require Import Csyntaxdefs. 
Import Csyntaxdefs.CsyntaxNotations.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope csyntax_scope.

Inductive effect_label : Type :=
| Panic : effect_label               (* exception effect *)
| Divergence : effect_label          (* divergence effect *)
| Read : ident -> effect_label       (* read heap effect *)
| Write : ident -> effect_label      (* write heap effect *)
| Alloc : ident -> effect_label      (* allocation heap effect *)
| Hstate : ident -> effect_label     (* state heap effect *).

Definition effect := list effect_label.  (* row of effects *)

Definition is_stateful_effectlabel (ef : effect_label) : bool :=
match ef with 
| Panic => false
| Divergence => false
| Read h => true 
| Write h => true 
| Alloc h => true 
| Hstate h => true
end.

Fixpoint is_stateful_effect (e : effect) : bool :=
match e with 
| nil => true
| e :: es => is_stateful_effectlabel e || is_stateful_effect es
end.

Inductive primitive_type : Type :=
| Tbool : primitive_type
| Tint : intsize -> signedness -> attr -> primitive_type
| Tlong : signedness -> attr -> primitive_type.

Inductive basic_type : Type :=  
| Bprim : primitive_type -> basic_type
| Bstruct : ident -> attr -> basic_type.

Inductive ptr_type : Type :=
| Reftype : ident -> basic_type -> attr -> ptr_type       (* Pointer to primitive types and struct : box - introduced in prog *)
| Vptype : primitive_type -> ptr_type                     (* Pointer to primitve types coming from outside *)
| Otype : ptr_type -> ptr_type                            (* Option type *)          
| Fptype : list type -> effect -> type -> ptr_type        (* function/arrow pointer type *)
| Sptype : ident -> attr -> ptr_type                      (* struct pointer - often used when it comes from helper functions *)
with type : Type :=
| Utype : type                                            (* Unit type *)
| Vtype : primitive_type -> type                          (* Value types *)
| Ptrtype : ptr_type -> type                              (* pointer type : can be ref, option or function pointer*)
| Stype : ident -> attr -> type                           (* struct type *)
| Ftype : list type -> effect -> type -> type             (* function type *).

(*| Bytes : type.*)

Section beepl_type_ind.

End beepl_type_ind.

Fixpoint get_data_type (pt : ptr_type) : type :=
match pt with 
| Reftype h bt a => match bt with 
                    | Bprim p => Vtype p
                    | Bstruct s a => Stype s a 
                    end
| Vptype pt => Vtype pt
| Otype pt => get_data_type pt
| Fptype ts ef t => Ftype ts ef t
| Sptype s a => Stype s a
end.

Inductive wtype : Type :=
| Twbool : wtype
| Twint : wtype
| Twlong : wtype
| Twunit : wtype
| Twref : wtype
| Twpv : wtype
| Twot : wtype
| Twpst : wtype
| Twfunptr : wtype
| Twst : wtype
| Twf : wtype
| Twv : wtype
| Twptr : wtype
| Twfun : wtype.
(*| Twbytes : wtype.*)

Definition attr_of_primitive_type (t : primitive_type) : attr :=
match t with 
| Tbool => noattr
| Tint sz s a => a
| Tlong s a => a
end.

Fixpoint attr_of_ptr_type (t : ptr_type) : attr :=
match t with 
| Reftype h bt a => a
| Vptype pt => attr_of_primitive_type pt
| Otype t => attr_of_ptr_type t
| Fptype ts ef t => noattr
| Sptype h a => a
end.

Definition attr_of_type (t : type) : attr :=
match t with 
| Utype => noattr
| Vtype pt => attr_of_primitive_type pt
| Ptrtype pt => attr_of_ptr_type pt
| Stype x a => a
| Ftype ts e t => noattr
(*| Bytes => noattr*)
end.

(****** Translation from BeePL types to Csyntax types ******)

Fixpoint from_typelist (ts : Ctypes.typelist) : list Ctypes.type :=
match ts with
| Tnil => nil
| Tcons t ts => t :: from_typelist ts
end. 

Fixpoint to_typelist (ts : list Ctypes.type) : Ctypes.typelist :=
match  ts with 
| nil => Tnil
| t :: ts => Tcons t (to_typelist ts)
end.

(* Definitions related to bcomposites (struct) *)
Inductive bmember : Type :=
| Member_plain : ident -> BeeTypes.type -> bmember
| Member_bitfield : ident -> intsize -> signedness -> attr -> Z -> bool -> bmember.

Open Scope Z_scope.

Record bcomposite : Type := Build_bcomposite
  { co_su : struct_or_union;
    co_members : list bmember;
    co_attr : attr;
    co_sizeof : Z;
    co_alignof : Z;
    co_rank : nat;
    co_sizeof_pos : (co_sizeof >= 0)%Z;
    co_alignof_two_p : exists n : nat, co_alignof = two_power_nat n;
    co_sizeof_alignof : (co_alignof | co_sizeof) }.

(* Reserved ident for option type conversion *)
Definition option_tag : ident := $"option_tag".
Definition option_val : ident := $"option_val".                     

Section translate_types.

Variable transBeePL_type : BeeTypes.type -> Ctypes.type.

(* Translates a list of BeePL types to list of Clight types *) 
Fixpoint transBeePL_types (ts : list BeeTypes.type) : Ctypes.typelist :=
match ts with 
| nil => Tnil
| t :: ts => (Tcons (transBeePL_type t) (transBeePL_types ts))
end.

End translate_types.

Definition mem_ident : ident := $"mem_ident".
Definition bytes_t : ident := $"bytes_t".

Fixpoint transBeePL_type (t : BeeTypes.type) : Ctypes.type :=
match t with
  | Utype => Ctypes.Tvoid
  | Vtype vt => match vt with  
                | Tbool => (Ctypes.Tint I8 Unsigned noattr)
                | Tint sz s a => (Ctypes.Tint sz s a)
                | Tlong s a => (Ctypes.Tlong s a)
                end
  | Ptrtype pt => (transBeePL_ptr_type pt)
  | Stype s a => (Tstruct s a) 
  | Ftype ts ef t' =>
      let cts := transBeePL_types transBeePL_type ts in 
      let ct := transBeePL_type t' in 
      (Tfunction cts ct
        {| cc_vararg := Some (Z.of_nat (length ts));
           cc_unproto := false;
           cc_structret := false |})
  (*| Bytes => (Tstruct bytes_t noattr)*)
  end
with transBeePL_ptr_type (pt : ptr_type) : Ctypes.type :=
  match pt with 
  | Reftype h bt a =>  
      match bt with 
      | Bprim Tbool => Ctypes.Tpointer (Ctypes.Tint I8 Unsigned noattr) noattr
      | Bprim (Tint sz s a') => Ctypes.Tpointer (Ctypes.Tint sz s a') a
      | Bprim (Tlong s a') => Ctypes.Tpointer (Ctypes.Tlong s a') a
      | Bstruct s a' => Ctypes.Tpointer (Tstruct s a') a
      end
  | Vptype pt => match pt with 
                 | Tbool => Ctypes.Tpointer (Ctypes.Tint I8 Unsigned noattr) noattr
                 | (Tint sz s a') => Ctypes.Tpointer (Ctypes.Tint sz s a') a'
                 | (Tlong s a') => Ctypes.Tpointer (Ctypes.Tlong s a') a'
                 end
  | Otype t => (transBeePL_ptr_type t)
  | Fptype ts ef t =>
      let cts := transBeePL_types transBeePL_type ts in 
      let ct := transBeePL_type t in 
      (Ctypes.Tpointer
        (Tfunction cts ct 
          {| cc_vararg := None;
             cc_unproto := false;
             cc_structret := false |})
        noattr)
  | Sptype s a => (Ctypes.Tpointer (Tstruct s a) a)
end.

Lemma transBeePL_types_length : forall ts cts,
  transBeePL_types transBeePL_type ts = cts ->
  length ts = length (from_typelist cts).
Proof.
  induction ts; intros.
  - inversion H. subst. reflexivity.
  - admit.
Admitted.


(*** Composite Definitions related to BeePL ***)
Definition bmember_cmember (b : bmember) : member :=
match b with 
| Member_plain h t => Ctypes.Member_plain h (transBeePL_type t)
| Member_bitfield h sz s a z b => Ctypes.Member_bitfield h sz s a z b
end. 

Fixpoint bmembers_cmembers (bs : list bmember) : members :=
match bs with 
| nil => nil
| b :: bs => bmember_cmember b :: bmembers_cmembers bs
end.


Definition member_is_padding (m: bmember) : bool :=
  match m with
  | Member_plain _ _ => false
  | Member_bitfield _ _ _ _ _ p => p
  end.

Inductive bcomposite_definition : Type :=  
| Bcomposite : ident -> struct_or_union -> list bmember -> attr -> bcomposite_definition.

Definition bcomposite_ccomposite_definition (bd : bcomposite_definition) : composite_definition :=
match bd with 
| Bcomposite h s bs a => (Composite h s (bmembers_cmembers bs) a)
end.

Definition bcomposite_ccomposite (b : bcomposite) : Ctypes.composite :=
{| Ctypes.co_su := b.(co_su);
   Ctypes.co_members := bmembers_cmembers b.(co_members);
   Ctypes.co_attr :=  b.(co_attr);
   Ctypes.co_sizeof := b.(co_sizeof);
   Ctypes.co_alignof := b.(co_alignof); 
   Ctypes.co_rank := b.(co_rank);
   Ctypes.co_sizeof_pos := b.(@co_sizeof_pos);
   Ctypes.co_alignof_two_p := b.(co_alignof_two_p);
   Ctypes.co_sizeof_alignof := b.(co_sizeof_alignof)|}.

Definition bcomposite_env := PTree.t bcomposite.

Definition bcomposite_composite_env (benv : bcomposite_env) : composite_env :=
  PTree.fold
    (fun (acc : composite_env) id (b : bcomposite) =>
       PTree.set id (bcomposite_ccomposite b) acc)
    benv
    (PTree.empty composite).

Program Definition bcomposite_of_def
     (env: bcomposite_env) (id: ident) (su: struct_or_union) (m: list bmember) (a: attr)
     : res bcomposite :=
  match env!id, complete_members (bcomposite_composite_env env) (bmembers_cmembers m) return _ with
  | Some _, _ =>
      Error (MSG "Multiple definitions of struct or union " :: CTX id :: nil)
  | None, false =>
      Error (MSG "Incomplete struct or union " :: CTX id :: nil)
  | None, true =>
      let al := align_attr a (alignof_composite (bcomposite_composite_env env) (bmembers_cmembers m)) in
      OK {| co_su := su;
            co_members := m;
            co_attr := a;
            co_sizeof := Coqlib.align (sizeof_composite (bcomposite_composite_env env) su (bmembers_cmembers m)) al;
            co_alignof := al;
            co_rank := rank_members (bcomposite_composite_env env) (bmembers_cmembers m);
            co_sizeof_pos := _;
            co_alignof_two_p := _;
            co_sizeof_alignof := _ |}
  end.
Next Obligation.
  apply Z.le_ge. eapply Z.le_trans. eapply sizeof_composite_pos.
  apply Coqlib.align_le; apply alignof_composite_pos.
Defined.
Next Obligation.
  apply align_attr_two_p. apply alignof_composite_two_p.
Defined.
Next Obligation.
  apply Coqlib.align_divides. apply alignof_composite_pos.
Defined.

(** The composite environment for a program is obtained by entering
  its composite definitions in sequence.  The definitions are assumed
  to be listed in dependency order: the definition of a composite
  must precede all uses of this composite, unless the use is under
  a pointer or function type. *)
Fixpoint add_bcomposite_definitions (env: bcomposite_env) (defs: list bcomposite_definition) : res bcomposite_env :=
  match defs with
  | nil => OK env
  | Bcomposite id su m a :: defs =>
      do co <- bcomposite_of_def env id su m a;
      add_bcomposite_definitions (PTree.set id co env) defs
  end.

Definition build_bcomposite_env (defs: list bcomposite_definition) :=
  add_bcomposite_definitions (PTree.empty _) defs.


Definition wf_bcomposites (types: list bcomposite_definition) : Prop :=
  match build_bcomposite_env types with OK _ => True | Error _ => False end.

Definition build_bcomposite_env' (types: list bcomposite_definition)
                                (WF: wf_bcomposites types)
                             : { ce | build_bcomposite_env types  = OK ce }.
Proof.
  revert WF. unfold wf_bcomposites. case (build_bcomposite_env types); intros.
- exists b; reflexivity.
- contradiction.
Defined.

Definition is_ptrtype (t : type) : bool :=
match t with 
| Utype => false
| Vtype vt => false
| Ptrtype pt => true 
| Ftype es ef t => false
| Stype x a => false
end. 

Definition is_ref_ptr_type (pt : ptr_type) : bool :=
match pt with 
| Reftype _ _ _ => true 
| _ => false
end.

Definition is_option_ptr_type (t : ptr_type) : bool :=
match t with 
| Otype t => true
| _ => false
end. 

Definition is_stype (t : type) : bool :=
match t with 
| Utype => false
| Vtype vt => false
| Ptrtype pt => false 
| Ftype es ef t => false
| Stype x a => true
end. 

Definition is_utype (t : type) : bool :=
match t with 
| Utype => true
| Vtype vt => false
| Ptrtype pt => false 
| Ftype es ef t => false
| Stype x a => false
end. 

Definition is_funtype (t : type) : bool :=
match t with 
| Ftype ts ef t => true 
| _ => false
end.

Definition is_vtype (t : type) : bool :=
match t with 
| Vtype vt => true 
| _ => false
end.

Definition is_primint (t : type) : bool :=
match t with 
| Vtype p => match p with 
             | Tbool => false
             | Tint _ _ _ => true 
             | Tlong _ _ => false
             end
| _ => false
end.

Definition is_primint32 (t : type) : bool :=
match t with 
| Vtype p => match p with 
             | Tbool => false
             | Tint I32 _ _ => true 
             | Tlong _ _ => false
             | _ => false
             end
| _ => false
end.

Definition is_primunsigned_int_long (t1 t2 : type) : bool :=
match t1, t2 with 
| Vtype p1, Vtype p2 => match p1, p2 with 
                        | Tbool, Tbool => false
                        | Tint sz1 s1 a1, Tint sz2 s2 a2 => if intsize_eq sz1 sz2 
                                                               && signedness_eq s1 s2 
                                                               && signedness_eq s1 Unsigned 
                                                               && attr_eq a1 a2 
                                                            then true else false
                        | Tlong s1 a1, Tlong s2 a2 => if signedness_eq s1 s2 
                                                         && signedness_eq s1 Unsigned 
                                                         && attr_eq a1 a2
                                                      then true else false
                        | _, _ => false
                        end
| _, _ => false
end.

Definition is_primlong (t : type) : bool :=
match t with 
| Vtype p => match p with 
             | Tbool => false
             | Tint _ _ _ => false 
             | Tlong _ _ => true
             end
| _ => false
end.

Definition is_primbool (t : type) : bool :=
match t with 
| Vtype p => match p with 
             | Tbool => true 
             | _ => false
             end
| _ => false
end.

Definition is_vtype_notunit (t : type) : Prop :=
is_vtype t /\ (not (is_utype t)).

Definition signedness_of_primitive (pt : primitive_type) : option signedness :=
  match pt with
  | Tbool => None
  | Tint _ s _ => Some s
  | Tlong s _ => Some s
  end.

Definition signedness_of_basic (bt : basic_type) : option signedness :=
  match bt with
  | Bprim pt => signedness_of_primitive pt
  | Bstruct _ _ => None
  end.

Fixpoint signedness_of_type (t : type) : option signedness :=
  match t with
  | Utype => None
  | Vtype pt => signedness_of_primitive pt
  | Ptrtype pt => signedness_of_ptr_type pt
  | Stype _ _ => None
  | Ftype _ _ _ => None
  end
with signedness_of_ptr_type (pt : ptr_type) : option signedness :=
  match pt with
  | Reftype _ bt _ => signedness_of_basic bt
  | Vptype pt => signedness_of_primitive pt
  | Otype pt' => signedness_of_ptr_type pt'
  | Fptype _ _ _=> None
  | Sptype _ _ => None
  end.


Definition wtype_of_primitive (pt : primitive_type) : wtype :=
  match pt with
  | Tbool => Twbool
  | Tint _ _ _ => Twint
  | Tlong _ _ => Twlong
  end.

Definition wtype_of_ptr_type (pt : ptr_type) : wtype :=
  match pt with
  | Reftype _ bt _ =>
      match bt with
      | Bprim _ => Twref
      | Bstruct _ _ => Twpst
      end
  | Vptype _ => Twpv
  | Otype _ => Twot
  | Fptype _ _ _ => Twfunptr
  | Sptype _ _ => Twptr
  end.

Fixpoint wtype_of_type (t : type) : wtype :=
  match t with
  | Utype => Twunit
  | Vtype pt => wtype_of_primitive pt
  | Ptrtype pt => wtype_of_ptr_type pt
  | Stype _ _ => Twst
  | Ftype _ _ _ => Twfun
  end.

Fixpoint wtypes_of_types (t : list type) : list wtype :=
match t with 
| nil => nil
| x :: xs => wtype_of_type x :: wtypes_of_types xs
end.

Definition eq_effect_label (e1 e2 : effect_label) : bool :=
match e1, e2 with 
| Panic, Panic => true 
| Divergence, Divergence => true 
| Read id1, Read id2 => (id1 =? id2)%positive
| Write id1, Write id2 => (id1 =? id2)%positive
| Alloc id1, Alloc id2 => (id1 =? id2)%positive
| Hstate id1, Hstate id2 => (id1 =? id2)%positive
| _, _ => false
end.

Fixpoint eq_effect (es1 es2 : effect) : bool :=
match es1, es2 with 
| nil, nil => true 
| e :: es, e' :: es' => eq_effect_label e e' && eq_effect es es'
| _, _ => false
end.

Fixpoint in_effect (ef : effect_label) (efs : effect) : bool :=
match efs with
| nil => false
| ef' :: efs' => if eq_effect_label ef ef' then true else in_effect ef efs'
end.

Fixpoint sub_effect (s1 s2 : effect) : bool := 
if s1 is x :: s1' 
then if s2 is y :: s2' 
     then if eq_effect_label x y 
          then sub_effect s1' s2'
          else sub_effect s1 s2'
     else false
else true.

Fixpoint no_divergence (ef : effect) : bool :=
match ef with 
| nil => true 
| ef :: efs => if eq_effect_label Divergence ef then false else no_divergence efs
end.

Definition eq_primitive_type (p1 p2 : primitive_type) : bool :=
match p1, p2 with 
| Tbool, Tbool => true
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

Inductive bmemory_chunk : Type :=
| BMbool : bmemory_chunk
| BMint8signed : bmemory_chunk
| BMint8unsigned : bmemory_chunk
| BMint16signed : bmemory_chunk
| BMint16unsigned : bmemory_chunk
| BMint32 : bmemory_chunk
| BMint64 : bmemory_chunk.

Definition transl_bchunk_cchunk (b : bmemory_chunk) : memory_chunk :=
match b with 
| BMbool => Mbool
| BMint8signed => Mint8signed
| BMint8unsigned => Mint8unsigned
| BMint16signed => Mint16signed
| BMint16unsigned => Mint16unsigned
| BMint32 => Mint32
| BMint64 => Mint64
end.

Definition wtypeof_chunk (c : bmemory_chunk) : wtype :=
match c with 
| BMbool => Twbool 
| BMint8signed => Twint 
| BMint8unsigned => Twint 
| BMint16signed => Twint 
| BMint16unsigned => Twint 
| BMint32 => Twint 
| BMint64 => Twlong 
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
| Tbool => By_value Mint8signed
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
| Bstruct x a => By_copy
end.

Fixpoint access_mode_type (t : type) : mode :=
  match t with
  | Utype => By_nothing
  | Vtype pt => access_mode_prim pt
  | Ptrtype _ => By_reference
  | Stype _ _ => By_reference
  | Ftype _ _ _ => By_reference
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
| Bstruct x1 a1, Bstruct x2 a2 => (x1 =? x2)%positive && attr_eq a1 a2
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

Fixpoint eq_type (t1 t2 : type) : bool :=
  match t1, t2 with
  | Utype, Utype => true
  | Vtype p1, Vtype p2 => eq_primitive_type p1 p2
  | Ptrtype pt1, Ptrtype pt2 => eq_ptr_type pt1 pt2
  | Stype id1 a1, Stype id2 a2 => (id1 =? id2)%positive && attr_eq a1 a2
  | Ftype ts1 ef1 t1', Ftype ts2 ef2 t2' =>
      eq_types eq_type ts1 ts2 && eq_effect ef1 ef2 && eq_type t1' t2'
  | _, _ => false
  end

with eq_ptr_type (p1 p2 : ptr_type) : bool :=
  match p1, p2 with
  | Reftype h1 b1 a1, Reftype h2 b2 a2 =>
      (h1 =? h2)%positive && eq_basic_type b1 b2 && attr_eq a1 a2
  | Vptype pt1, Vptype pt2 => eq_primitive_type pt1 pt2
  | Otype t1, Otype t2 => eq_ptr_type t1 t2
  | Fptype ts1 ef1 t1, Fptype ts2 ef2 t2 =>
      eq_types eq_type ts1 ts2 && eq_effect ef1 ef2 && eq_type t1 t2
  | Sptype id1 a1, Sptype id2 a2 => (id1 =? id2)%positive && attr_eq a1 a2
  | _, _ => false
  end.

 
Definition eq_wtype (w1 w2 : wtype) : bool :=
  match w1, w2 with
  | Twbool, Twbool => true
  | Twint, Twint => true
  | Twlong, Twlong => true
  | Twunit, Twunit => true
  | Twref, Twref => true
  | Twpv, Twpv => true
  | Twot, Twot => true
  | Twpst, Twpst => true
  | Twfunptr, Twfunptr => true
  | Twst, Twst => true
  | Twf, Twf => true
  | Twv, Twv => true
  | Twptr, Twptr => true
  | Twfun, Twfun => true
  | _, _ => false
  end.

 

Definition sizeof_ptype (t : primitive_type) : Z :=
match t with 
| Tbool => 1
| Tint I8 _ _ => 1
| Tint I16 _ _ => 2
| Tint I32 _ _ => 4
| Tint IBool _ _ => 1
| Tlong _ _ => 4
end.

Definition sizeof_btype (env : bcomposite_env) (t : basic_type) : Z :=
match t with 
| Bprim t => sizeof_ptype t 
| Bstruct x a => match env!x with Some co => co_sizeof co | None => 0 end
end. 

Fixpoint sizeof_type (env : bcomposite_env) (t : type) : Z :=
  match t with
  | Utype => 0
  | Vtype pt => sizeof_ptype pt
  | Ptrtype pt => sizeof_ptr_type env pt
  | Stype x _ => match env!x with Some co => co_sizeof co | None => 0 end
  | Ftype _ _ _ => 1
  end

with sizeof_ptr_type (env : bcomposite_env) (pt : ptr_type) : Z :=
  match pt with
  | Reftype h t  _ => sizeof_btype env t
  | Vptype t => sizeof_ptype t
  | Otype t => sizeof_ptr_type env t
  | Fptype _ _ _ => 1
  | Sptype x a => 1
  end.

(* Used for extracting the correct type for a Ref's fresh variable *)
Definition ref_to_prim (ty : type) : mon type :=
  match ty with
  | Ptrtype (Reftype _ (Bprim pt) _) => ret (Vtype pt)
  | Ptrtype (Reftype _ (Bstruct s a) _) => ret (Stype s a)
  | _ => error (msg "ref_to_prim: expected only reftype")
  end.

(* Typing context *)
Definition ty_context := PTree.t type.

(* To ensure that a location does not contain another location (ref) 
   and only points to basic types like int, bool, unit or pair *)
(* Records the type of the values that we expect to be stored in cell i *)
Definition store_context := PTree.t type.  

Definition empty_context := (PTree.empty type).

Definition extend_context (Gamma : ty_context) (k : ident) (t : type) := PTree.set k t Gamma. 

Definition empty_stcontext := (PTree.empty type).

Definition extend_stcontext (Sigma : store_context) (k : ident) (t : type) := PTree.set k t Sigma. 

(*** Auxillary lemmas related to types and effects ***)
(* Complete Me: Easy *)
Lemma sub_effect_refl : forall ef, 
sub_effect ef ef = true.
Proof.
  induction ef.
  - reflexivity.
  - unfold sub_effect.
    destruct (eq_effect_label a a).
    + apply IHef.
    + destruct a.
Admitted.
  

(* Complete Me: Easy *)
Lemma sub_effect_nil : forall ef, 
sub_effect nil ef = true.
Proof. induction ef; auto. Qed.

(* Complete Me: Easy *)
Lemma sub_effect_trans : forall ef1 ef2 ef3, 
sub_effect ef1 ef2 = true ->
sub_effect ef2 ef3 = true ->
sub_effect ef1 ef3 = true.
Proof.
  intros ef1 ef2 ef3 H1.
  generalize dependent ef3.
  induction ef3; intros H2.
  - induction ef2; auto.
  - admit.
Admitted.

(* Complete Me: Easy *)
Lemma prefix_sub_effect : forall (ef1 ef2 : effect), 
sub_effect ef1 (ef1 ++ ef2)%list = true.
Proof. 
  induction ef1; intros.
  - simpl. apply sub_effect_nil.
  - destruct a; simpl.
    + apply IHef1.
    + apply IHef1.
    + destruct ((i =? i)%positive).
      * apply IHef1.
Admitted.

(* Complete Me: Easy *)
Lemma suffix_sub_effect : forall (ef1 ef2 : effect), 
sub_effect ef2 (ef1 ++ ef2)%list = true.
Proof. 
Admitted.
