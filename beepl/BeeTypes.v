
Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL PeanoNat Coq.NArith.BinNat Ctypes Errors Ctypes Coq.ZArith.Znumtheory Coqlib.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps SimplExpr Coq.Strings.BinaryString  Coq.Numbers.DecimalString.
From mathcomp Require Import all_ssreflect. 
From compcert Require Import Csyntaxdefs Ctyping. 
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
| Io : effect_label                  (* input/output unsafe effect *).

Definition effect := list effect_label.  (* row of effects *)

Definition is_stateful_effectlabel (ef : effect_label) : bool :=
match ef with 
| Panic => false
| Divergence => false
| Read h => true 
| Write h => true 
| Alloc h => true 
| Io => true
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
| Bstruct : ident -> attr -> basic_type
| Barray : primitive_type -> Z -> attr -> basic_type.

Inductive ptr_type : Type :=
| Reftype : ident -> basic_type -> attr -> ptr_type       (* Pointer to primitive types and struct : box - introduced in prog *)
| Vptype : primitive_type -> ptr_type                     (* Pointer to primitve types coming from outside *)
| Otype : ptr_type -> ptr_type                            (* Option type *)          
| Fptype : list type -> effect -> type -> ptr_type        (* function/arrow pointer type *)
| Sptype : ident -> attr -> ptr_type                      (* struct pointer - often used when it comes from helper functions *)
| Aptype : type -> Z -> attr -> ptr_type                  (* array pointer - often used in ebpf structs *)
with type : Type :=
| Utype : type                                            (* Unit type *)
| Vtype : primitive_type -> type                          (* Value types *)
| Ptrtype : ptr_type -> type                              (* pointer type : can be ref, option or function pointer*)
| Stype : ident -> attr -> type                           (* struct type *)
| Atype : type -> Z -> attr -> type                       (* array types ([ty[len]]) *)
| Ftype : list type -> effect -> type -> type             (* function type *)
| Bytes : type                                            (* bytes type of size n *).


Section beepl_type_ind.
Context (Pt : BeeTypes.type -> Prop).
Context (Pts : list BeeTypes.type -> Prop).
Context (Pptr : BeeTypes.ptr_type -> Prop).
Context (Href : forall i bt a, Pptr (Reftype i bt a)).
Context (Hvptr : forall pt, Pptr (Vptype pt)).
Context (Hoptr : forall ptr, Pptr ptr -> Pptr (Otype ptr)).
Context (Hfptr : forall ts e t, Pts ts -> Pt t -> Pptr (Fptype ts e t)).
Context (Hsptr : forall i a, Pptr (Sptype i a)).
Context (Haptr : forall t n a, Pt t -> Pptr (Aptype t n a)).
Context (Hunot : Pt (Utype)).
Context (Hv : forall pt, Pt (Vtype pt)).
Context (Hptr : forall ptr, Pptr ptr -> Pt (Ptrtype ptr)).
Context (Hs : forall i a, Pt (Stype i a)).
Context (Ha : forall t n a, Pt t -> Pt (Atype t n a)).
Context (Hf : forall ts e t, Pts ts -> Pt t -> Pt (Ftype ts e t)).
Context (Hb : Pt Bytes).
Context (Hnil : Pts nil).
Context (Hcons : forall t ts, Pt t -> Pts ts -> Pts (t :: ts)).

Lemma beepl_type_ind_mut : 
  (forall t, Pt t) /\ (forall ts, Pts ts) /\ (forall ptr, Pptr ptr).
Proof.
  assert (forall t, Pt t) as Htype.
  - fix IHt 1.
    destruct t.
    + apply Hunot.
    + apply Hv.
    + apply Hptr.
      revert p.
      fix IHp 1.
      destruct p.
      * apply Href.
      * apply Hvptr.
      * apply Hoptr. apply IHp.
      * apply Hfptr.
        -- revert l.
          fix IHl 1.
          destruct l.
          ++ apply Hnil.
          ++ apply Hcons. apply IHt. apply IHl.
        -- apply IHt.
      * apply Hsptr.
      * apply Haptr. apply IHt.
    + apply Hs.
    + apply Ha. apply IHt.
    + apply Hf.
      * revert l.
        fix IHl 1.
        destruct l.
        -- apply Hnil.
        -- apply Hcons. apply IHt. apply IHl.
      * apply IHt.
    + apply Hb.
  assert (forall ts, Pts ts) as Htypes.
  - fix IHts 1.
    destruct ts.
    + apply Hnil.
    + apply Hcons.
      * apply Htype.
      * apply IHts.
  assert (forall ptr, Pptr ptr) as Hpptr.
  - fix IHp 1.
    destruct ptr.
    + apply Href.
    + apply Hvptr.
    + apply Hoptr. apply IHp.
    + apply Hfptr.
      * apply Htypes.
      * apply Htype.
    + apply Hsptr.
    + apply Haptr. apply Htype.
  split; try split; assumption.
Qed.

End beepl_type_ind.

Definition allowed_cast (t1 t2 : primitive_type) : res primitive_type :=
match t1, t2 with 
| Tbool, _ => OK t2
| Tint sz s a, _ => OK t2
| Tlong s a, Tint sz s' a' => OK t2
| Tlong s a, Tlong s' a' => OK t2
| _, _ => Error (msg "Casting not allowed")
end.

Fixpoint get_data_type (pt : ptr_type) : type :=
match pt with 
| Reftype h bt a => match bt with 
                    | Bprim p => Vtype p
                    | Bstruct s a => Stype s a 
                    | Barray p z a => Atype (Vtype p) z a
                    end
| Vptype pt => Vtype pt
| Otype pt => get_data_type pt
| Fptype ts ef t => Ftype ts ef t
| Sptype s a => Stype s a
| Aptype t z a => Atype t z a
end.

Definition construct_type_btype (bt : basic_type) : type :=
match bt with 
| Bprim pt => Vtype pt
| Bstruct sid a => Stype sid a 
| Barray pt n a => Atype (Vtype pt) n a 
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
| Twpa : wtype
| Twfunptr : wtype
| Twst : wtype
| Twa : wtype
| Twf : wtype
| Twv : wtype
| Twptr : wtype
| Twfun : wtype
| Twbytes : wtype
| Twmap : wtype.

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
| Aptype t z a => a
end.

Definition attr_of_type (t : type) : attr :=
match t with 
| Utype => noattr
| Vtype pt => attr_of_primitive_type pt
| Ptrtype pt => attr_of_ptr_type pt
| Stype x a => a
| Atype t z a => a 
| Ftype ts e t => noattr
| Bytes => noattr
end.

(* Definitions related to bcomposites (struct) *)
Inductive bmember : Type :=
| Member_plain : ident -> BeeTypes.type -> bmember
| Member_bitfield : ident -> intsize -> signedness -> attr -> Z -> bool -> bmember.

Definition type_bmember (m: bmember) : type :=
  match m with
  | Member_plain _ t => t
  | Member_bitfield _ sz sg a w _ =>
      (* An unsigned bitfield of width < size of type reads with a signed type *)
      let sg' := if zlt w (bitsize_intsize sz) then Signed else sg in
      Vtype (Tint sz sg' a)
  end.

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
Fixpoint transBeePL_types (ts : list BeeTypes.type) : list Ctypes.type :=
match ts with 
| nil => nil
| t :: ts => (transBeePL_type t) :: (transBeePL_types ts)
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
  | Atype t z a => (Tarray (transBeePL_type t) z a)
  | Ftype ts ef t' =>
      let cts := transBeePL_types transBeePL_type ts in 
      let ct := transBeePL_type t' in 
      (Tfunction cts ct
        {| cc_vararg := Some (Z.of_nat (length ts));
           cc_unproto := false;
           cc_structret := false |})
  | Bytes => (Tstruct bytes_t noattr)
  end
with transBeePL_ptr_type (pt : ptr_type) : Ctypes.type :=
  match pt with 
  | Reftype h bt a =>  
      match bt with 
      | Bprim Tbool => Ctypes.Tpointer (Ctypes.Tint I8 Unsigned noattr) noattr
      | Bprim (Tint sz s a') => Ctypes.Tpointer (Ctypes.Tint sz s a') a
      | Bprim (Tlong s a') => Ctypes.Tpointer (Ctypes.Tlong s a') a
      | Bstruct s a' => Ctypes.Tpointer (Tstruct s a') a
      | Barray bt z a' =>  match bt with  
                           | Tbool => Ctypes.Tpointer (Tarray (Ctypes.Tint I8 Unsigned noattr) z a') a
                           | Tint sz s ai => Ctypes.Tpointer (Tarray (Ctypes.Tint sz s ai) z a') a
                           | Tlong s al => Ctypes.Tpointer (Tarray (Ctypes.Tlong s al) z a') a
                           end
      end
  | Vptype pt => match pt with 
                 | Tbool => Ctypes.Tpointer (Ctypes.Tint I8 Unsigned noattr) noattr
                 | (Tint sz s a') => Ctypes.Tpointer (Ctypes.Tint sz s a') a'
                 | (Tlong s a') => Ctypes.Tpointer (Ctypes.Tlong s a') a' (*tptr tvoid*)
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
  | Aptype t' z a => (Ctypes.Tpointer (Tarray (transBeePL_type t') z a) a)
  end.

Lemma transBeePL_types_length : forall ts cts,
  transBeePL_types transBeePL_type ts = cts ->
  length ts = length cts.
Proof.
  induction ts; intros.
  - inversion H. subst. reflexivity.
  - simpl in *.
    destruct cts.
    + discriminate.
    + injection H as H.
      simpl.
      f_equal.
      auto.
Qed.

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

(** ** Complete types *)

(** A type is complete if it fully describes an object.
  All struct and union names appearing in the type must be defined,
  unless they occur under a pointer or function type.  [void] and
  function types are incomplete types. *)
Fixpoint bcomplete_type (env: bcomposite_env) (t: type) : bool :=
  match t with
  | Utype => false
  | Vtype pt => true
  | Ptrtype pt => true 
  | Stype s _ => match env!s with Some co => true | None => false end
  | Atype t z a => bcomplete_type env t
  | Ftype _ _ _ => false
  | Bytes => true 
  end.

Definition bcomplete_or_function_type (env: bcomposite_env) (t: type) : bool :=
  match t with
  | Ftype _ _ _ => true
  | _ => bcomplete_type env t
  end.


Fixpoint bcomplete_members (env: bcomposite_env) (ms: list bmember) : bool :=
  match ms with
  | nil => true
  | m :: ms => bcomplete_type env (type_bmember m) && bcomplete_members env ms
  end.

Program Definition bcomposite_of_def
     (env: bcomposite_env) (id: ident) (su: struct_or_union) (m: list bmember) (a: attr)
     : res bcomposite :=
  match env!id, bcomplete_members env m return _ with
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
| Atype t z a => false
| Bytes => false
end. 

Definition is_ptrtype_stype (t : type) : bool :=
match t with 
| Ptrtype (Sptype x a) => true
| _ => false
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

Definition is_option_type (t : type) : bool :=
match t with 
| Ptrtype (Otype t) => true
| _ => false
end. 

Definition is_stype (t : type) : bool :=
match t with 
| Utype => false
| Vtype vt => false
| Ptrtype pt => false 
| Ftype es ef t => false
| Stype x a => true
| Atype t z a => false
| Bytes => false
end. 

Definition is_atype (t : type) : bool :=
match t with 
| Utype => false
| Vtype vt => false
| Ptrtype pt => false 
| Ftype es ef t => false
| Stype x a => false
| Atype t z a => true
| Bytes => false
end.

Definition is_utype (t : type) : bool :=
match t with 
| Utype => true
| Vtype vt => false
| Ptrtype pt => false 
| Ftype es ef t => false
| Stype x a => false
| Atype t z a => false
| Bytes => false
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

Definition is_bytes (t : type) : bool :=
match t with 
| Bytes => true 
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
  | Barray _ _ _ => None
  end.

Fixpoint signedness_of_ptr_type (pt : ptr_type) : option signedness :=
  match pt with
  | Reftype _ bt _ => signedness_of_basic bt
  | Vptype pt => signedness_of_primitive pt
  | Otype pt' => signedness_of_ptr_type pt'
  | Fptype _ _ _=> None
  | Sptype _ _ => None
  | Aptype _ _ _ => None
  end.

Definition signedness_of_type (t : type) : option signedness :=
  match t with
  | Utype => None
  | Vtype pt => signedness_of_primitive pt
  | Ptrtype pt => signedness_of_ptr_type pt
  | Stype _ _ => None
  | Atype t z a => None
  | Ftype _ _ _ => None
  | Bytes => None
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
      | Barray _ _ _ => Twpa
      end
  | Vptype _ => Twpv
  | Otype _ => Twot
  | Fptype _ _ _ => Twfunptr
  | Sptype _ _ => Twptr
  | Aptype _ _ _ => Twpa
  end.

Definition wtype_of_type (t : type) : wtype :=
  match t with
  | Utype => Twunit
  | Vtype pt => wtype_of_primitive pt
  | Ptrtype pt => wtype_of_ptr_type pt
  | Stype _ _ => Twst
  | Atype t z a => Twa
  | Ftype _ _ _ => Twfun
  | Bytes => Twbytes
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
| Io, Io => true
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
| Tbool => By_value Mbool
| Tint I8 Signed _ => By_value Mint8signed
| Tint I8 Unsigned _ => By_value Mint8unsigned
| Tint I16 Signed _ => By_value Mint16signed
| Tint I16 Unsigned _ => By_value Mint16unsigned
| Tint I32 _ _ => By_value Mint32
| Tint IBool _ _ => By_value Mint32
| Tlong _ _ => By_value Mint64
end.

Definition access_mode_basic (t : basic_type) : mode :=
match t with 
| Bprim t => access_mode_prim t
| Bstruct x a => By_reference
| Barray t z a => By_reference
end.

Definition access_mode_type (t : type) : mode :=
  match t with
  | Utype => By_nothing
  | Vtype pt => access_mode_prim pt
  | Ptrtype _ => By_value Mptr
  | Stype _ _ => By_reference
  | Atype t z a => By_reference
  | Ftype _ _ _ => By_reference
  | Bytes => By_reference
  end.


(** The chunk that is appropriate to store and reload a value of
  the given type, without losing information. *)

Definition chunk_of_ptype (ty: primitive_type) :=
match ty with
| Tbool => BMint8signed
| Tint I8 Signed _ => BMint8signed
| Tint I8 Unsigned _ => BMint8unsigned
| Tint I16 Signed _ => BMint16signed
| Tint I16 Unsigned _ => BMint16unsigned
| Tint I32 _ _ => BMint32
| Tint IBool _ _ => BMbool
| Tlong _ _ => BMint64
end.

Definition chunk_of_type (ty : type) : option bmemory_chunk :=
match ty with
| Vtype pt => Some (chunk_of_ptype pt)
| Ptrtype _ => Some BMint64  (* Assuming 64-bit architecture *)
| Bytes => None  (* 16 bytes cannot be assigned i*)
(* Not directly mappable to a single chunk *)
| Stype _ _ => None
| Atype _ _ _ => None
| Ftype _ _ _ => None
| Utype => None
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
| Barray p1 n1 a1, Barray p2 n2 a2 => eq_primitive_type p1 p2 && (n1 =? n2)%Z && attr_eq a1 a2
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
  | Atype t1 z1 a1, Atype t2 z2 a2 => eq_type t1 t2 && (z1 =? z2)%Z && attr_eq a1 a2
  | Ftype ts1 ef1 t1', Ftype ts2 ef2 t2' =>
      eq_types eq_type ts1 ts2 && eq_effect ef1 ef2 && eq_type t1' t2'
  | Bytes, Bytes => true
  | Atype t1 z1 a1, trint8s => true (* special case because of bpf_printk *)
  | trint8s, Atype t2 z2 a2 => true (* special case because of bpf_printk *)
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
  | Otype t1, _ => true   (* we need this special case: all pointer type can be void * *)
  | _, Otype t1 => true   (* we need this special case: all pointer type can be void * *)
  | Aptype t1 z1 a1, Aptype t2 z2 a2 => eq_type t1 t2 && (z1 =? z2)%Z && attr_eq a1 a2
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
  | Twpa, Twpa => true
  | Twfunptr, Twfunptr => true
  | Twst, Twst => true
  | Twa, Twa => true 
  | Twf, Twf => true
  | Twv, Twv => true
  | Twptr, Twptr => true
  | Twfun, Twfun => true
  | Twbytes, Twbytes => true
  | Twmap, Twmap => true
  | _, _ => false
  end.

Definition sizeof_ptype (t : primitive_type) : Z :=
match t with 
| Tbool => 1
| Tint I8 _ _ => 1
| Tint I16 _ _ => 2
| Tint I32 _ _ => 4
| Tint IBool _ _ => 1
| Tlong _ _ => 8
end.

Fixpoint sizeof_type (env : bcomposite_env) (t : BeeTypes.type) : Z :=
  match t with
  | Utype => 0
  | Vtype pt => sizeof_ptype pt
  | Ptrtype pt => if Archi.ptr64 then 8 else 4
  | Stype x _ => match env!x with Some co => co_sizeof co | None => 0 end
  | Atype t' z a => sizeof_type env t' * Z.max 0 z
  | Ftype _ _ _ => 1
  | Bytes => 16
  end.

Fixpoint sizeof_types (env : bcomposite_env) (ts : list type) : Z :=
match ts with 
| nil => 0
| t :: ts => sizeof_type env t + sizeof_types env ts
end.

Definition alignof_ptype (t : primitive_type) : Z :=
match t with 
| Tbool => 1
| Tint I8 _ _ => 1
| Tint I16 _ _ => 2
| Tint I32 _ _ => 4
| Tint IBool _ _ => 1
| Tlong _ _ => Archi.align_int64
end.

Fixpoint alignof_type (env : bcomposite_env) (t : BeeTypes.type) : Z :=
  match t with
  | Utype => 0
  | Vtype pt => alignof_ptype pt
  | Ptrtype pt => if Archi.ptr64 then 8 else 4
  | Stype x _ => match env!x with Some co => co_alignof co | None => 1 end
  | Atype t' z a => alignof_type env t'
  | Ftype _ _ _ => 1
  (* Bytes get translated to a struct in C with two fields of char* *)
  | Bytes => if Archi.ptr64 then 8 else 4
  end.

(* Used for extracting the correct type for a Ref's fresh variable *)
Definition ref_to_prim (ty : type) : mon type :=
  match ty with
  | Ptrtype (Reftype _ (Bprim pt) _) => ret (Vtype pt)
  | Ptrtype (Reftype _ (Bstruct s a) _) => ret (Stype s a)
  | _ => error (msg "ref_to_prim: expected only reftype")
  end.

Fixpoint check_fun_ptr_fun (sts : list type) (ats : list type) : bool :=
match sts, ats with 
| nil, nil => true 
| t :: ts, t' :: ts' => match t, t' with 
                        | Ptrtype (Fptype ts1 ef1 t1), Ftype ts1' ef1' t1' => 
                          if eq_types eq_type ts1 ts1' && eq_type t1 t1' && eq_effect ef1 ef1'
                          then check_fun_ptr_fun ts ts'
                          else false
                        | _, _ => eq_type t t' && check_fun_ptr_fun ts ts'
                        end 
| _, _ => false
end.

Section Trans_ctypes_btypes.

Variable trans_ctype_btype : Ctypes.type -> res BeeTypes.type.

Fixpoint trans_ctypes_btypes (ct : list Ctypes.type) : res (list BeeTypes.type) :=
match ct with 
| nil => OK nil
| ct :: cts => do bt <- trans_ctype_btype ct;
                  do bts <- trans_ctypes_btypes cts;
                  OK (bt :: bts)
end.

End Trans_ctypes_btypes.

Definition trans_ctype_btype (ct : Ctypes.type) : res BeeTypes.type :=
match ct with 
| Ctypes.Tvoid => OK Utype
| Ctypes.Tint sz s a => OK (BeeTypes.Vtype (Tint sz s a))
| Ctypes.Tlong s a => OK (BeeTypes.Vtype (Tlong s a))
| Ctypes.Tfloat _ _ => Error (msg "TYPE ERROR: Float is not supported in BeePL")
| Ctypes.Tpointer t a => match t with 
                  | Ctypes.Tvoid => Error (msg "TYPE ERROR: Void* is not supported in BeePL")
                  | Ctypes.Tint sz s a => OK (Ptrtype (Reftype mem_ident (Bprim (Tint sz s a)) a))
                  | Ctypes.Tlong s a => OK (Ptrtype (Reftype mem_ident (Bprim (Tlong s a)) a))
                  | _ => Error (msg "TYPE ERROR: Not supported in ref type")
                  end 
| Tarray t z a => Error (msg "TYPE ERROR: Array is not supported in BeePL")
| Tfunction ts t cc => Error (msg "TYPE ERROR: Cannot compute the effect, hence translation is not possible from ctype to btype in case of function")
| Tstruct x a => OK (Stype x a)
| Tunion x a => Error (msg "TYPE ERROR: Union is not supported in BeePL")
end.

Fixpoint type_of_members (xs : list (attr * ident)) (m : members) {struct xs} : res (list Ctypes.type) :=
match xs with 
| nil => OK nil
| (a, x) :: xs => do t <- type_of_member a x m;
                  do ts <- type_of_members xs m;
                  OK (t :: ts)
end.

Definition all_eq_types (ts : list type) : bool :=
match ts with
| nil => true
| t1 :: ts' => forallb (fun t => eq_type t1 t) ts'
end. 

Fixpoint construct_list_type (t : type) (n : nat) : list type :=
match n with 
| O => nil
| S n' => t :: construct_list_type t n'
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

Fixpoint extends_context (Gamma : ty_context) (ks : list ident) (ts : list type) := 
match ks, ts with 
| nil, nil => Gamma
| k :: ks, t :: ts => extends_context (extend_context Gamma k t) ks ts
| _, _ => Gamma
end.

Definition construct_ef_gvar (gi : init_data) : res effect := 
match gi with  
| Init_int8 _ => OK (Alloc mem_ident :: Write mem_ident :: nil)
| Init_int16 _ => OK (Alloc mem_ident :: Write mem_ident :: nil)
| Init_int32 _ => OK (Alloc mem_ident :: Write mem_ident :: nil)
| Init_int64 _ => OK (Alloc mem_ident :: Write mem_ident :: nil)
| Init_float32 _ => Error (msg "TYPE ERROR: Float global variable not supported in BeePL")
| Init_float64 _ => Error (msg "TYPE ERROR: Float global variable not supported in BeePL")
| Init_space _ => OK (Alloc mem_ident :: nil)
| Init_addrof _ _ => OK (Alloc mem_ident :: Write mem_ident :: Read mem_ident :: nil)
end.

Fixpoint construct_ef_gvars (gis : list init_data) : res effect :=
match gis with 
| nil => OK nil
| gi :: gis => do ge <- construct_ef_gvar gi;
               do ges <- construct_ef_gvars gis;
               OK (ge ++ ges)%list
end.


