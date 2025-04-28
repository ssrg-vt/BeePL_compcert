Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL PeanoNat Coq.NArith.BinNat Ctypes Errors Ctypes Coq.ZArith.Znumtheory.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps SimplExpr Coq.Strings.BinaryString.
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
| Hstate : ident -> effect_label      (* state heap effect *).

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
| Tunit : primitive_type
| Tbool : primitive_type
| Tint : intsize -> signedness -> attr -> primitive_type
| Tlong : signedness -> attr -> primitive_type.

(* In the future basic_type will include arrays, structs, etc. *)
Inductive basic_type : Type :=  
| Bprim : primitive_type -> basic_type
| Bstruct : ident -> attr -> basic_type                           (* struct type *).

Inductive type : Type :=
| Ptype : primitive_type -> type                          (* primitive types *)
| Reftype : ident -> basic_type -> attr -> type           (* reference type ref<h,int> *)
| Ftype : list type -> effect -> type -> type             (* function/arrow type *)
| Stype : ident -> attr -> type                           (* struct *)
| Otype : type -> type.                                   (* option type : only contains ref *)

Inductive wtype : Type :=
| Twunit : wtype
| Twbool : wtype
| Twint : wtype
| Twlong : wtype
| Twref : wtype
| Twfun : wtype
| Twst : wtype
| Twot : wtype.

Definition attr_of_primitive_type (t : primitive_type) : attr :=
match t with 
| Tunit => noattr 
| Tbool => noattr
| Tint sz s a => a
| Tlong s a => a
end.

Fixpoint attr_of_type (t : type) : attr :=
match t with 
| Ptype t => attr_of_primitive_type t
| Reftype h t a => a
| Ftype ts ef t => noattr
| Stype x a => a
| Otype t => attr_of_type t
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

Fixpoint create_ident_type (t : type) : ident :=
match t with 
| Ptype t => match t with 
             | Tunit => $"option__tunit"
             | Tbool => $"option__tbool"
             | Tint sz s a => match sz with 
                              | I8 => match s with 
                                      | Ctypes.Unsigned => $("option__tint__i8__unsigned")
                                      | Ctypes.Signed => $("option__tint__i8__signed")
                                      end
                              | I16 => match s with 
                                       | Unsigned => $("option__tint__i16__unsigned")
                                       | SIgned => $("option__tint__i16__signed")
                                       end
                              | I32 => match s with 
                                       | Unsigned => $("option__tint__i32__unsigned")
                                       | SIgned => $("option__tint__i32__signed")
                                       end
                             | IBool => match s with 
                                       | Unsigned => $("option__tint__ib__unsigned")
                                       | SIgned => $("option__tint__ib__signed")
                                       end
                             end
             | Tlong s a => match s with 
                            | Signed => $("option__tlong__signed")
                            | Unsigned => $("option__tlong__unsigned")
                            end

             end
| Reftype h bt a => match bt with 
                    | Bprim p => match p with 
                                 | Tunit => $"option__ref__tunit"
                                 | Tbool => $"option__ref__tbool"
                                 | Tint sz s a => match sz with 
                                                  | I8 => match s with 
                                                          | Ctypes.Unsigned => $("option__ref__tint__i8__unsigned")
                                                          | Ctypes.Signed => $("option__ref__tint__i8__signed")
                                                          end
                                                  | I16 => match s with 
                                                           | Unsigned => $("option__ref__tint__i16__unsigned")
                                                           | SIgned => $("option__ref__tint__i16__signed")
                                                           end
                                                  | I32 => match s with 
                                                           | Unsigned => $("option___ref__tint__i32__unsigned")
                                                           | SIgned => $("option__ref__tint__i32__signed")
                                                           end
                                                  | IBool => match s with 
                                                             | Unsigned => $("option__ref__tint__ib__unsigned")
                                                             | SIgned => $("option__ref__tint__ib__signed")
                                                             end
                                                  end
                                 | Tlong s a => match s with 
                                                | Signed => $("option__ref__tlong__signed")
                                                | Unsigned => $("option__ref__tlong__unsigned")
                                                end
                                 end
                     | Bstruct x a => $("option__ref" ++ string_of_ident x)

             end
| Ftype ts ef t => $"option__fun"
| Stype x a => $("option__struct" ++ string_of_ident x)
| Otype t => $("option_o_ption__" ++ string_of_ident (create_ident_type t))
end.

Fixpoint transBeePL_type (t : BeeTypes.type) : Ctypes.type :=
match t with
| Ptype t => match t with  
             | Tunit => Ctypes.Tvoid (* Fix me *)
             | Tbool => (Ctypes.Tint I8 Unsigned noattr)
             | Tint sz s a => (Ctypes.Tint sz s a)
             | Tlong s a => (Ctypes.Tlong s a)
             end
| Reftype h bt a => match bt with 
                    | Bprim Tunit => (Ctypes.Tpointer Ctypes.Tvoid a)
                    | Bprim Tbool => (Ctypes.Tpointer (Ctypes.Tint I8 Unsigned noattr) a)
                    | Bprim (Tint sz s a') => (Ctypes.Tpointer (Ctypes.Tint sz s a') a)
                    | Bprim (Tlong s a') => (Ctypes.Tpointer (Ctypes.Tlong s a') a)
                    | Bstruct x a => (Ctypes.Tpointer (Tstruct x a) a)
                    end
| BeeTypes.Ftype ts ef t => (Tfunction (transBeePL_types transBeePL_type ts) (transBeePL_type t) 
                                       {| cc_vararg := Some (Z.of_nat(length(ts))); 
                                       cc_unproto := false; cc_structret := false |}) (* Fix me *) 
| BeeTypes.Stype x a => (Tstruct x a)
| BeeTypes.Otype t => Ctypes.Tpointer (transBeePL_type t) (attr_of_type t)
end.

(* Custom induction principles for transBeePL_type *)
Lemma transBeePL_type_ind :
forall (P : BeeTypes.type -> Prop),
  (forall (t : primitive_type), P (Ptype t)) ->
  (forall (h : ident) (bt : basic_type) (a : attr), P (Reftype h bt a)) ->
  (forall (ts : list BeeTypes.type) (ef : effect) (t : BeeTypes.type),
    Forall P ts -> P t -> P (Ftype ts ef t)) ->
  (forall (h : ident) (a : attr), P (Stype h a)) ->
  (forall (t : type), P t -> P (Otype t)) ->
forall t : BeeTypes.type, P t.
Proof.
  intros P Hprim Href Hfun Hstruct Hoption.
  fix IH 1.
  intros t.
  destruct t as [p | h bt a | ts ef t | h a | t].
  - apply Hprim.
  - apply Href.
  - apply Hfun.
    + induction ts as [| t' ts' IHts]; constructor; auto.
    + apply IH.
  - apply Hstruct.
  - apply Hoption. apply IH.
Qed.

Lemma transBeePL_type_typelist_ind_mut:
  forall (Pt : BeeTypes.type -> Prop) (Pts : list BeeTypes.type -> Prop),
    (forall (t : primitive_type), Pt (Ptype t)) ->
    (forall (h : ident) (bt : basic_type) (a : attr), Pt (Reftype h bt a)) ->
    (forall (ts : list BeeTypes.type) (ef : effect) (t : BeeTypes.type),
      Pts ts -> Pt t -> Pt (Ftype ts ef t)) ->
    (forall (h : ident) (a : attr), Pt (Stype h a)) ->
    (forall (t : type), Pt t -> Pt (Otype t)) ->
    (Pts nil) ->
    (forall (t : BeeTypes.type) (ts : list BeeTypes.type),
      Pt t -> Pts ts -> Pts (t :: ts)) ->
    (forall t, Pt t) /\ (forall ts, Pts ts).
Proof.
  intros Pt Pts Hprim Href Hfun Hstruct Hoption Hnil Hcons.
  assert (forall t, Pt t) as Htype.
  { apply transBeePL_type_ind; auto.
    intros ts ef t Hforall HPt.
    apply Hfun; auto.
    induction ts as [|t' ts' IH].
    - assumption.
    - apply Hcons.
      + apply Forall_inv in Hforall. assumption.
      + apply IH. apply Forall_inv_tail in Hforall. assumption.
  }
  assert (forall ts, Pts ts) as Htypes.
  { induction ts as [|t ts' IH].
    - assumption.
    - apply Hcons; auto.
  }
  split; assumption.
Qed.

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

(** To describe the values returned by functions, we use the more precise
    types below. *)

Inductive rettype : Type :=
| Tret (t: type)      (**r like type [t] *)
| Trbool               (**r Boolean value (0 or 1) *)
| Tint8signed         (**r 8-bit signed integer *)
| Tint8unsigned       (**r 8-bit unsigned integer *)
| Tint16signed        (**r 16-bit signed integer *)
| Tint16unsigned      (**r 16-bit unsigned integer *)
| Teunit              (**r no value returned *)
| Testype             (**r struct type **)
| To                  (**r option type **).

Definition is_reftype (t : type) : bool :=
match t with 
| Ptype p => false
| Reftype h bt a => true 
| Ftype es ef t => false
| Stype x a => false
| Otype t => false
end. 

Definition is_optiontype (t : type) : bool :=
match t with 
| Ptype p => false
| Reftype h bt a => false 
| Ftype es ef t => false
| Stype x a => false
| Otype t => true
end. 

Definition is_stype (t : type) : bool :=
match t with 
| Ptype p => false
| Reftype h bt a => false
| Ftype es ef t => false
| Stype x a => true
| Otype t => false
end. 

Definition is_unittype (t : type) : bool :=
match t with 
| Ptype p => match p with 
             | Tunit => true
             | _ => false
             end
| _ => false
end. 

Definition is_funtype (t : type) : bool :=
match t with 
| Ftype ts ef t => true 
| _ => false
end.

Definition is_primtype (t : type) : bool :=
match t with 
| Ptype p => true 
| _ => false
end.

Definition is_primint (t : type) : bool :=
match t with 
| Ptype p => match p with 
             | Tunit => false
             | Tbool => false
             | Tint _ _ _ => true 
             | Tlong _ _ => false
             end
| _ => false
end.

Definition is_primunsigned_int_long (t1 t2 : type) : bool :=
match t1, t2 with 
| Ptype p1, Ptype p2 => match p1, p2 with 
                        | Tunit, Tunit => false
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
| Ptype p => match p with 
             | Tunit => false
             | Tbool => false
             | Tint _ _ _ => false 
             | Tlong _ _ => true
             end
| _ => false
end.

Definition is_primunit (t : type) : bool :=
match t with 
| Ptype p => match p with 
             | Tunit => true 
             | _ => false
             end
| _ => false
end.

Definition is_primbool (t : type) : bool :=
match t with 
| Ptype p => match p with 
             | Tbool => true 
             | _ => false
             end
| _ => false
end.

Definition is_primtype_notunit (t : type) : Prop :=
is_primtype t /\ (not (is_unittype t)).

Definition extract_signedness_type (t : type) : option signedness :=
match t with 
| Ptype p => match p with 
             | Tunit => None
             | Tbool => None
             | Tint sz s a => Some s
             | Tlong s a => Some s
             end
| _ => None 
end.

Definition basic_to_type (b : basic_type) : mon type :=
match b with 
| Bprim p => ret (Ptype p)
| Bstruct x a => error (msg "Struct is not a primitive type")
end.

Definition Twptr := if Archi.ptr64 then Twlong else Twint. 

Definition wtype_of_type (t : type) : wtype :=
match t with 
| Ptype p => match p with
             | Tunit => Twunit 
             | Tbool => Twbool
             | Tint _ _ _ => Twint 
             | Tlong _ _ => Twlong 
             end
| Reftype _ _ _ => Twref 
| Ftype _ _ _ => Twfun
| Stype _ _ => Twst
| Otype _ => Twot
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
| Tunit, Tunit => true 
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
| Tunit =>  By_nothing (* Fix me *)
| Tbool => By_value Mint8unsigned
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

Definition access_mode (t : type) : mode :=
match t with 
| Ptype t => access_mode_prim t
| Reftype h t _ => By_value Mptr
| Ftype ts ef t => By_reference
| Stype x a => By_copy
| Otype t => By_copy
end.


Definition type_is_volatile (t : type) : bool :=
match access_mode t with 
| By_value _ => attr_volatile (attr_of_type t)
| _ => false
end.

(*Definition bchunk_for_volatile_type (t : type) (bf : bitfield) : option bmemory_chunk :=
if type_is_volatile t 
then match access_mode t with 
     | By_value chunk => match bf with 
                         | Full => Some chunk
                         | Bits _ _ _ _ => None 
                         end
     | _ => None 
     end
else None.

chunk_for_volatile_type = 
fun (ty : Ctypes.type) (bf : bitfield) =>
if Ctypes.type_is_volatile ty
then
 match Ctypes.access_mode ty with
 | By_value chunk => match bf with
                     | Full => Some chunk
                     | Bits _ _ _ _ => None
                     end
 | _ => None
 end
else None

Print chunk_for_volatile_type.
chunk_for_volatile_type cty bf*)


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

Fixpoint eq_type (p1 p2 : type) : bool :=
match p1, p2 with 
| Ptype p1, Ptype p2 => eq_primitive_type p1 p2
| Ftype ts1 e1 t1, Ftype ts2 e2 t2 => 
  eq_types eq_type ts1 ts2 && eq_effect e1 e2 && eq_type t1 t2
| Reftype e1 b1 a1, Reftype e2 b2 a2 => if attr_eq a1 a2  
                                        then (e1 =? e2)%positive && eq_basic_type b1 b2
                                        else false
| Stype x1 a1, Stype x2 a2 => if (x1 =?  x2)%positive && attr_eq a1 a2 then true else false
| Otype t1, Otype t2 => eq_type t1 t2
| _, _ => false
end. 

Definition eq_wtype (t1 t2 : wtype) : bool :=
match t1, t2 with 
| Twunit, Twunit => true 
| Twint, Twint => true 
| Twlong, Twlong => true 
| Twref, Twref => true
| Twfun, Twfun => true
| Twst, Twst => true
| Twot, Twot => true
| _, _ => false
end.  

Definition sizeof_ptype (t : primitive_type) : Z :=
match t with 
| Tunit => 1
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
| Ptype t => sizeof_ptype t 
| Reftype h t _ => sizeof_btype env t
| Ftype ts e t => 1
| Stype x a => match env!x with Some co => co_sizeof co | None => 0 end
| Otype t => sizeof_type env t (* fix me *)
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
