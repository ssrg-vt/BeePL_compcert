Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import compcert.common.Errors BeePL_auxlemmas.

(***** Correctness proof for the Clight generation from BeePL using 
       composition of BeePL and CompCert compiler *****)

(***** Specification for types *****) 
Inductive rel_prim_type : BeeTypes.primitive_type -> Ctypes.type -> Prop :=
| rel_tunit : rel_prim_type Tunit (Ctypes.Tvoid)
| rel_tint : forall sz s, 
             rel_prim_type (Tint sz s) (Ctypes.Tint (transBeePL_isize_cisize sz) (transBeePL_sign_csign s)
                                        {| attr_volatile := false; attr_alignas := Some (compute_align sz) |}) 
| rel_tbool : rel_prim_type Tbool (Ctypes.Tint Ctypes.I8 Ctypes.Unsigned {| attr_volatile := false; attr_alignas := Some 1%N |}).

Inductive rel_basic_type : BeeTypes.basic_type -> Ctypes.type -> Prop :=
| rel_btype : forall tp ct,
              rel_prim_type tp ct ->
              rel_basic_type (Bprim tp) ct.

Inductive rel_type : BeeTypes.type -> Ctypes.type -> Prop :=
| rel_ptype : forall pt ct, 
              rel_prim_type pt ct ->
              rel_type (Ptype pt) ct
| rel_reftype : forall h bt ct, 
                rel_basic_type bt ct ->
                rel_type (Reftype h bt) (Tpointer ct {| attr_volatile := false; attr_alignas := Some 8%N |})
| rel_ftype : forall ts ef t cts ct,
              rel_types ts cts ->
              rel_type t ct -> 
              length ts = length (typelist_list_type cts) ->
              rel_type (Ftype ts ef t) (Tfunction cts ct 
                                        {| cc_vararg := Some (Z.of_nat(length(ts))); cc_unproto := false; cc_structret := false |}) 
with rel_types : list BeeTypes.type -> Ctypes.typelist -> Prop :=
| rel_tnil : rel_types nil Tnil
| rel_tcons : forall bt bts ct cts,
              rel_type bt ct ->
              rel_types bts cts ->
              rel_types (bt :: bts) (Tcons ct cts).

Scheme rel_type_ind2 := Minimality for rel_type Sort Prop
  with rel_typelist_ind2 := Minimality for rel_types Sort Prop.
Combined Scheme rel_type_typelist_ind from rel_type_ind2, rel_typelist_ind2.

(*Scheme rel_beety_ind2 := Minimality for BeeTypes.type Sort Prop
  with rel_beetys_ind2 := Minimality for (list BeeTypes.type) Sort Prop.
Combined Scheme rel_type_typelist_ind from rel_type_ind2, rel_typelist_ind2.*)

Section rel_type_ind.
Variables (Pt :  BeeTypes.type -> Ctypes.type -> Prop)
          (Pts: list BeeTypes.type -> Ctypes.typelist -> Prop).

Definition rel_Ind_tnil : Prop := Pts nil Tnil.
Definition rel_Ind_tcons : Prop := 
forall bt bts ct cts, rel_type bt ct -> Pt bt ct -> rel_types bts cts -> Pts bts cts -> Pts (bt :: bts) (Tcons ct cts).

Hypotheses
    (Hnil: rel_Ind_tnil)
    (Hcons: rel_Ind_tcons).

Definition rel_Ind_ptype : Prop :=
forall pt ct, rel_prim_type pt ct -> Pt (Ptype pt) ct.

Definition rel_Ind_reftype : Prop :=
forall pt h ct, rel_basic_type pt ct -> Pt (Reftype h pt) (Tpointer ct {| attr_volatile := false; attr_alignas := Some 8%N |}).

Definition rel_Ind_ftype : Prop :=
forall pt ct pts cts ef, rel_types pts cts -> Pts pts cts -> rel_type pt ct -> Pt pt ct -> 
                         length pts = length (typelist_list_type cts) -> 
                         Pt (Ftype pts ef pt) (Tfunction cts ct 
                                               {| cc_vararg := Some (Z.of_nat(length(pts))); cc_unproto := false; cc_structret := false |}). 

Hypotheses
    (Hptype: rel_Ind_ptype)
    (Hreftype: rel_Ind_reftype)
    (Hftype: rel_Ind_ftype).

Fixpoint rels_Ind (pts : list BeeTypes.type) (cts : Ctypes.typelist) (s : rel_types pts cts) {struct s} : 
Pts pts cts := 
match s with  
| rel_tnil => Hnil 
| rel_tcons bt bts ct cts ih ihs => Hcons bt bts ct cts ih (@rel_Ind bt ct ih) ihs (@rels_Ind bts cts ihs)
end 
with rel_Ind (pt : BeeTypes.type) (ct : Ctypes.type) (s : rel_type pt ct) {struct s} :
Pt pt ct :=
match s  with 
| rel_ptype pt ct ih => Hptype pt ct ih 
| rel_reftype h pt ct ih => Hreftype pt h ct ih 
| rel_ftype pts ef pt cts ct ihs ih iheq => Hftype pt ct pts cts ef ihs (rels_Ind pts cts ihs) ih (rel_Ind pt ct ih) iheq
end. 
End rel_type_ind. 

(***** Proof for correctness of type transformation *****)
Fixpoint type_translated bt: 
(forall ct, 
transBeePL_type bt = ct ->
rel_type bt ct) /\ (forall bts cts, 
transBeePL_types transBeePL_type bts = cts ->
rel_types bts cts).
Proof.
destruct bt.
+ admit.
+ admit.
+ induction l.
  ++ admit.
  ++ 
Admitted.

From mathcomp Require Import all_ssreflect. 

(****** Proof of correctness for transformation of operators ******)
Lemma transl_notbool_cnotbool: forall v v' m t,
sem_unary_operation Notbool v t = Some v' -> 
Cop.sem_unary_operation (transBeePL_uop_uop Notbool) (transBeePL_value_cvalue v) 
     (transBeePL_type t) m = Some (transBeePL_value_cvalue v'). 
Proof.
intros; simpl. 
generalize dependent (extract_type_notbool v t v' H). intros; subst; simpl.
destruct v; inversion H; subst. destruct b.
+ unfold Cop.sem_notbool, Cop.bool_val; simpl. 
  assert (hneq : Int.eq (Int.repr 1) Int.zero = false).
  ++ apply Int.eq_false; simpl. unfold not. intros. inversion H0.
  ++ rewrite hneq; simpl. unfold Values.Vfalse, Int.zero. reflexivity.
+ unfold Cop.sem_notbool, Cop.bool_val; simpl. 
  assert (hneq : Int.eq (Int.repr 0) Int.zero = true).
  ++ apply Int.eq_true; simpl. 
  ++ rewrite hneq; simpl. unfold Values.Vtrue, Int.zero. reflexivity.
Qed.

Lemma transl_notint_cnotint: forall v v' m t,
sem_unary_operation Notint v t = Some v' -> 
Cop.sem_unary_operation (transBeePL_uop_uop Notint) (transBeePL_value_cvalue v) 
     (transBeePL_type t) m = Some (transBeePL_value_cvalue v'). 
Proof.
intros; simpl.
generalize dependent (extract_type_notint v t v' H). intros; subst; simpl.
destruct H0; subst; destruct H0; subst.
(* Int *)
destruct v; inversion H; subst.
unfold Cop.sem_notint, Int.zero, Int.not, Int.mone; simpl. 
rewrite /transBeePL_isize_cisize. case: x H=> //= _. by case: x0=> //=.
Qed.

Lemma transl_neg_cneg: forall v v' m t,
sem_unary_operation Neg v t = Some v' -> 
Cop.sem_unary_operation (transBeePL_uop_uop Neg) (transBeePL_value_cvalue v) 
     (transBeePL_type t) m = Some (transBeePL_value_cvalue v'). 
Proof.
intros; simpl.
generalize dependent (extract_type_neg v t v' H). intros; subst; simpl.
destruct H0; subst; destruct H0; subst.
(* Int *)
destruct v; inversion H; subst.
unfold Cop.sem_neg, Int.zero, Int.not, Int.mone; simpl. 
rewrite /transBeePL_isize_cisize. case: x H=> //= _. by case: x0=> //=.
Qed.

Lemma transl_uop_cuop : forall op v v' m t,
sem_unary_operation op v t = Some v' -> 
Cop.sem_unary_operation (transBeePL_uop_uop op) (transBeePL_value_cvalue v) (transBeePL_type t) m = 
Some (transBeePL_value_cvalue v').
Proof.
intros. destruct op; simpl; auto; subst.
(* Notbool *)
+ generalize dependent (transl_notbool_cnotbool v v' m t H). intros. apply H0.
(* Notint *)
+ generalize dependent (transl_notint_cnotint v v' m t H). intros. apply H0.
(* Neg *)
+ generalize dependent (transl_neg_cneg v v' m t H). intros. apply H0.
Qed.

Lemma transl_plus_cadd: forall v1 v2 t1 t2 v cenv m,
sem_binary_operation Plus v1 v2 t1 t2 = Some v -> 
Cop.sem_binary_operation cenv (transBeePL_bop_bop Plus) (transBeePL_value_cvalue v1) 
     (transBeePL_type t1) (transBeePL_value_cvalue v2) (transBeePL_type t2) m = 
Some (transBeePL_value_cvalue v). 
Proof.
move=> v1 v2 t1 t2 v cenv m hs. 
have [sz [s ht]] := extract_type_plus1 v1 v2 t1 t2 v hs; subst.
rewrite /sem_binary_operation /sem_plus /= in hs. move: hs.
rewrite /Cop.sem_binary_operation /= /Cop.sem_add /= /transBeePL_isize_cisize /transBeePL_sign_csign.
case: v1=> //=.
+ by case: v2=> //= i. 
+ case: v2=> //= i i'. case: t2=> //= p. case:p=> //= sz' s'.
  move=> [] hv; subst. case: sz=> //=.
  + case: s=> //=.
    + rewrite /Cop.classify_add /= /Cop.sem_binarith /= /Cop.sem_cast /= /Cop.classify_cast /=. 
      case: sz'=> //=. by case: s'=> //=.
    + rewrite /Cop.classify_add /= /Cop.sem_binarith /= /Cop.sem_cast /= /Cop.classify_cast /=. 
      case: sz'=> //=. by case: s'=> //=.
    + rewrite /Cop.classify_add /= /Cop.sem_binarith /= /Cop.sem_cast /= /Cop.classify_cast /=. 
      case: sz'=> //=. by case: s'=> //=.
    + rewrite /Cop.classify_add /= /Cop.sem_binarith /= /Cop.sem_cast /= /Cop.classify_cast /=. 
      case: sz'=> //=. by case: s=> //=.
    rewrite /Cop.classify_add /= /Cop.sem_binarith /= /Cop.sem_cast /= /Cop.classify_cast /=. 
    case: s=> //=. case: s=> //=. by case: s'=> //=.
  by case: v2=> //=.
by case: v2=> //=.
Qed.

Lemma transl_minus_csub: forall v1 v2 t1 t2 v cenv m,
sem_binary_operation Minus v1 v2 t1 t2 = Some v -> 
Cop.sem_binary_operation cenv (transBeePL_bop_bop Minus) (transBeePL_value_cvalue v1) 
     (transBeePL_type t1) (transBeePL_value_cvalue v2) (transBeePL_type t2) m = 
Some (transBeePL_value_cvalue v). 
Proof.
move=> v1 v2 t1 t2 v cenv m hs. 
have [sz [s ht]] := extract_type_minus1 v1 v2 t1 t2 v hs; subst.
rewrite /sem_binary_operation /sem_minus /= in hs. move: hs.
rewrite /Cop.sem_binary_operation /= /Cop.sem_sub /= /transBeePL_isize_cisize /transBeePL_sign_csign.
case: v1=> //=.
+ by case: v2=> //= i. 
+ case: v2=> //= i i'. case: t2=> //= p. case:p=> //= sz' s'.
  move=> [] hv; subst. case: sz=> //=.
  + case: s=> //=.
    + rewrite /Cop.classify_add /= /Cop.sem_binarith /= /Cop.sem_cast /= /Cop.classify_cast /=. 
      case: sz'=> //=. by case: s'=> //=.
    + rewrite /Cop.classify_add /= /Cop.sem_binarith /= /Cop.sem_cast /= /Cop.classify_cast /=. 
      case: sz'=> //=. by case: s'=> //=.
    + rewrite /Cop.classify_add /= /Cop.sem_binarith /= /Cop.sem_cast /= /Cop.classify_cast /=. 
      case: sz'=> //=. by case: s'=> //=.
    + rewrite /Cop.classify_add /= /Cop.sem_binarith /= /Cop.sem_cast /= /Cop.classify_cast /=. 
      case: sz'=> //=. by case: s=> //=.
    rewrite /Cop.classify_add /= /Cop.sem_binarith /= /Cop.sem_cast /= /Cop.classify_cast /=. 
    case: s=> //=. case: s=> //=. by case: s'=> //=.
  by case: v2=> //=.
by case: v2=> //=.
Qed.

Lemma transl_mult_cmul: forall v1 v2 t1 t2 v cenv m,
sem_binary_operation Mult v1 v2 t1 t2 = Some v -> 
Cop.sem_binary_operation cenv (transBeePL_bop_bop Mult) (transBeePL_value_cvalue v1) 
     (transBeePL_type t1) (transBeePL_value_cvalue v2) (transBeePL_type t2) m = 
Some (transBeePL_value_cvalue v). 
Proof.
move=> v1 v2 t1 t2 v cenv m hs. 
have [sz [s ht]] := extract_type_mult1 v1 v2 t1 t2 v hs; subst.
rewrite /sem_binary_operation /sem_mult /= in hs. move: hs.
rewrite /Cop.sem_binary_operation /= /Cop.sem_mul /= /transBeePL_isize_cisize /transBeePL_sign_csign.
case: v1=> //=.
+ by case: v2=> //= i. 
+ case: v2=> //= i i'. case: t2=> //= p. case:p=> //= sz' s'.
  move=> [] hv; subst. case: sz=> //=.
  + case: s=> //=.
    + rewrite /Cop.classify_add /= /Cop.sem_binarith /= /Cop.sem_cast /= /Cop.classify_cast /=. 
      case: sz'=> //=. by case: s'=> //=.
    + rewrite /Cop.classify_add /= /Cop.sem_binarith /= /Cop.sem_cast /= /Cop.classify_cast /=. 
      case: sz'=> //=. by case: s'=> //=.
    + rewrite /Cop.classify_add /= /Cop.sem_binarith /= /Cop.sem_cast /= /Cop.classify_cast /=. 
      case: sz'=> //=. by case: s'=> //=.
    + rewrite /Cop.classify_add /= /Cop.sem_binarith /= /Cop.sem_cast /= /Cop.classify_cast /=. 
      case: sz'=> //=. by case: s=> //=.
    rewrite /Cop.classify_add /= /Cop.sem_binarith /= /Cop.sem_cast /= /Cop.classify_cast /=. 
    case: s=> //=. case: s=> //=. by case: s'=> //=.
  by case: v2=> //=.
by case: v2=> //=.
Qed.

Lemma is_signed : forall s,
eq_signedness s Signed ->
s = Signed.
Proof.
move=> s. by case: s=> //=.
Qed.

Lemma is_unsigned : forall s,
eq_signedness s Unsigned ->
s = Unsigned.
Proof.
move=> s. by case: s=> //=.
Qed.

Lemma transl_div_cdiv: forall v1 v2 t1 t2 v cenv m,
sem_binary_operation Div v1 v2 t1 t2 = Some v -> 
Cop.sem_binary_operation cenv (transBeePL_bop_bop Div) (transBeePL_value_cvalue v1) 
     (transBeePL_type t1) (transBeePL_value_cvalue v2) (transBeePL_type t2) m = 
Some (transBeePL_value_cvalue v). 
Proof.
(*move=> v1 v2 t1 t2 v cenv m hs. 
have [sz [s ht]] := extract_type_div1 v1 v2 t1 t2 v hs; subst.
have [sz' [s' ht]] := extract_type_div2 v1 v2 (Ptype (Tint sz s)) t2 v hs; subst.
inversion hs; subst. case: v1 hs H0=> //=.
+ by case: v2=> //=.
+ case: v2=> //= i i'. case: ifP=> //=.
  + move=> /andP [] /andP [] hs hs' h [] hv [] hv' /=; subst.
    have hvs := is_signed s hs; subst; rewrite /=.
    have hvs' := is_signed s' hs'; subst; rewrite /=.
    rewrite /Cop.sem_div /= /Cop.sem_binarith /Cop.sem_cast /=.
    case: sz=> //=.
    + case: sz'=> //=.
      + case: ifP=> //= hi'.
        + case: ifP=> //= hi.
          + case: ifP=> //=. move=> he. by rewrite he in h.
          case: ifP=> //=. move=> h'. by rewrite h' in h.
        case: ifP=> //= hi. + case: ifP=> //=. move=> h'. by rewrite h' in h.
        case: ifP=> //=. move=> h'. by rewrite h' in h.
      case: ifP=> //= hi'.
      + case: ifP=> //= hi.
        + case: ifP=> //=. move=> h'. by rewrite h' in h.
        case: ifP=> //=. move=> h'. by rewrite h' in h.
      case: ifP=> //= hi. 
      + case: ifP=> //=. move=> h'. by rewrite h' in h.
        case: ifP=> //=. move=> h'. by rewrite h' in h.
      case: ifP=> //= hi'.
      + case: ifP=> //= hi. + case: ifP=> //=. move=> h'. by rewrite h' in h.
        case: ifP=> //=. move=> h'. by rewrite h' in h.
      case: ifP=> //= hi. + case: ifP=> //=. move=> h'. by rewrite h' in h.
      case: ifP=> //=. move=> h'. by rewrite h' in h.
     case: ifP=> //= hi'. + case:ifP=> //= hi. + case: sz'=> //=. 
     + case: ifP=> //=. move=> h'. by rewrite h' in h.
     case: ifP=> //=. move=> h'. by rewrite h' in h.
    case: ifP=> //=. move=> h'. by rewrite h' in h.
   case: sz'=> //=. + case: ifP=> //=. move=> h'. by rewrite h' in h.
   case: ifP=> //=. move=> h'. by rewrite h' in h.
   case: ifP=> //=. move=> h'. by rewrite h' in h.
   case: sz'=> //=. + case: ifP=> //= hi. + case: ifP=> //=. move=> h'. by rewrite h' in h.
   case: ifP=> //=. move=> h'. by rewrite h' in h.
   case: ifP=> //=. move=> h'. by rewrite h' in h.
   case: ifP=> //=. move=> h'. by rewrite h' in h.
   case: ifP=> //=. move=> h'. by rewrite h' in h.
   case: ifP=> //=. move=> h'. by rewrite h' in h.
   case: ifP=> //= hi'. case: ifP=> //=. move=> h'. by rewrite h' in h.
   case: sz'=> //=. + case: ifP=> //=. move=> h'. by rewrite h' in h.
   case: ifP=> //=. move=> h'. by rewrite h' in h.
   case: ifP=> //=. move=> h'. by rewrite h' in h.
   case: sz'=> //=. + case: ifP=> //= hi. + case: ifP=> //=. move=> h'. by rewrite h' in h.
   case: ifP=> //=. move=> h'. by rewrite h' in h.
   case: ifP=> //=. move=> h'. by rewrite h' in h.
   case: ifP=> //=. move=> h'. by rewrite h' in h.
   case: ifP=> //=. move=> h'. by rewrite h' in h.
   case: ifP=> //=. move=> h'. by rewrite h' in h.
 move=> /andP h. case: ifP=> //= /andP [] /andP [] h1 h2 h3 [] hv [] hv'; subst.  
 have hvs := is_unsigned s h1; subst; rewrite /=.
 have hvs' := is_unsigned s' h2; subst; rewrite /=. rewrite /= /negb /= in h.
 move: h. case: ifP=> //=.
 + move=> h hf. rewrite /Cop.sem_div /= /Cop.sem_binarith /Cop.sem_cast /=.
   case: ifP=> //= hi'. + case: ifP=> //= hi.
   + by rewrite hi in h3.
   case: sz=> //=. + case: sz'=> //=. 
   + case: ifP=> //=. move=>he. rewrite he /= in h. rewrite hi /= in he.
     move: he. move=> /andP [] h1' h2'. apply Int.same_if_eq in hi'.
     apply Int.same_if_eq in h1'. by rewrite h1' in hi'.
   rewrite hi /= in h. move: h. move=> /andP [] h4 h5.
   apply Int.same_if_eq in h4. apply Int.same_if_eq in hi'. by rewrite h4 in hi'.
  rewrite hi /= in h. move: h. move=> /andP [] h4 h5.
  apply Int.same_if_eq in h4. apply Int.same_if_eq in hi'. by rewrite h4 in hi'.
  rewrite hi /= in h. move: h. move=> /andP [] h4 h5.
  apply Int.same_if_eq in h4. apply Int.same_if_eq in hi'. by rewrite h4 in hi'.
  rewrite hi /= in h. move: h. move=> /andP [] h4 h5.
  apply Int.same_if_eq in h4. apply Int.same_if_eq in hi'. by rewrite h4 in hi'.
  rewrite hi /= in h. move: h. move=> /andP [] h4 h5.
  apply Int.same_if_eq in h4. apply Int.same_if_eq in hi'. by rewrite h4 in hi'.
  case: sz=> //=. + case: sz'=> //=.
  + case: ifP=> //= hi. by rewrite hi in h3.
    rewrite hi /= in h. move: h. move=> /andP [] h4 h5.
    case: ifP=> //= he; subst. rewrite hi /=  h4 /= in he.
    apply Int.same_if_eq in h4. apply Int.same_if_eq in hi'. by rewrite h4 in hi'.
+ by case: v2=> //=.
by case: v2=> //=.*)
Admitted.


Lemma transl_or_cor: forall v1 v2 t1 t2 v cenv m,
sem_binary_operation Or v1 v2 t1 t2 = Some v -> 
Cop.sem_binary_operation cenv (transBeePL_bop_bop Or) (transBeePL_value_cvalue v1) 
     (transBeePL_type t1) (transBeePL_value_cvalue v2) (transBeePL_type t2) m = 
Some (transBeePL_value_cvalue v). 
Proof.
move=> v1 v2 t1 t2 v cenv m /= ha. case: v1 ha=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. by case: p=> //=.
+ case: v2=> //= i i'. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. by case: p=> //=.
+ case: v2=> //= b b'. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. case: p=> //= [] [] hv; subst; rewrite /=.
  rewrite /Cop.sem_or /Cop.sem_binarith /Cop.sem_cast /=.
  case: Archi.ptr64=> //=.
  + case: b'=> //=. by case: b=> //=.
  by case: b=> //=.
  case: (intsize_eq Ctypes.I32 Ctypes.I32) => //= heq.  
  case: b'=> //=. + by case: b=> //=.
  + by case: b=> //=.
case:v2=> //= p p'. case: t1=> //= i b. case: b=> //= p''.
case: p''=> //=. case: t2=> //= i' b. case:b=> //= p''. 
by case:p''=> //=.
Qed.

Lemma transl_xor_cxor: forall v1 v2 t1 t2 v cenv m,
sem_binary_operation Xor v1 v2 t1 t2 = Some v -> 
Cop.sem_binary_operation cenv (transBeePL_bop_bop Xor) (transBeePL_value_cvalue v1) 
     (transBeePL_type t1) (transBeePL_value_cvalue v2) (transBeePL_type t2) m = 
Some (transBeePL_value_cvalue v). 
Proof.
move=> v1 v2 t1 t2 v cenv m /= ha. case: v1 ha=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. by case: p=> //=.
+ case: v2=> //= i i'. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. by case: p=> //=.
+ case: v2=> //= b b'. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. case: p=> //= [] [] hv; subst; rewrite /=.
  rewrite /Cop.sem_or /Cop.sem_binarith /Cop.sem_cast /=.
  case: Archi.ptr64=> //=.
  + case: b'=> //=. by case: b=> //=.
  by case: b=> //=.
  case: (intsize_eq Ctypes.I32 Ctypes.I32) => //= heq.  
  case: b'=> //=. + by case: b=> //=.
  + by case: b=> //=.
case:v2=> //= p p'. case: t1=> //= i b. case: b=> //= p''.
case: p''=> //=. case: t2=> //= i' b. case:b=> //= p''. 
by case:p''=> //=.
Qed.

Lemma transl_shl_cshl: forall v1 v2 t1 t2 v cenv m,
sem_binary_operation Shl v1 v2 t1 t2 = Some v -> 
Cop.sem_binary_operation cenv (transBeePL_bop_bop Shl) (transBeePL_value_cvalue v1) 
     (transBeePL_type t1) (transBeePL_value_cvalue v2) (transBeePL_type t2) m = 
Some (transBeePL_value_cvalue v). 
Proof.
Admitted.

Lemma transl_shr_cshr: forall v1 v2 t1 t2 v cenv m,
sem_binary_operation Shr v1 v2 t1 t2 = Some v -> 
Cop.sem_binary_operation cenv (transBeePL_bop_bop Shr) (transBeePL_value_cvalue v1) 
     (transBeePL_type t1) (transBeePL_value_cvalue v2) (transBeePL_type t2) m = 
Some (transBeePL_value_cvalue v). 
Proof.
(*move=> v1 v2 t1 t2 v cenv m /= ha. case: v1 ha=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. by case: p=> //=.
+ case: v2=> //= i i'. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. case: p=> //= [] [] heq /=; subst.
  rewrite /Cop.sem_shr /Cop.sem_shift /=. case: ifP=> //= hi.
  + move: heq. by case:ifP=> //= hi' [] hv /=; subst; rewrite /=.
  by rewrite hi in heq.
+ case: v2=> //= i i'. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. case: p=> //= [] [] heq /=; subst.
  rewrite /Cop.sem_shr /Cop.sem_shift /=. case: ifP=> //= hi.
  + move: heq. by case:ifP=> //= hi' [] hv /=; subst; rewrite /=.
  by rewrite hi in heq.
+ case: v2=> //= b b'. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. by case:p=> //= p. 
case: v2=> //= p1 p2.
case: t1=> //= i b. case: b=> //= p. case: p=> //=.
case: t2=> //= i' b. case: b=> //= p. by case: p=> //=.
Qed.*) Admitted.

Lemma transl_eq_ceq: forall v1 v2 t1 t2 v cenv m,
sem_binary_operation Eq v1 v2 t1 t2 = Some v -> 
Cop.sem_binary_operation cenv (transBeePL_bop_bop Eq) (transBeePL_value_cvalue v1) 
     (transBeePL_type t1) (transBeePL_value_cvalue v2) (transBeePL_type t2) m = 
Some (transBeePL_value_cvalue v). 
Proof.
move=> v1 v2 t1 t2 v cenv m /= ha. case: v1 ha=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. case: p=> //= [] [] hv; subst; rewrite /=.
  rewrite /Cop.sem_cmp /Cop.sem_binarith /Cop.sem_cast /=. 
  by case: (Archi.ptr64)=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. case: p=> //= i i' [] hv; subst; rewrite /=.
  rewrite /Cop.sem_cmp /Cop.sem_binarith /Cop.sem_cast /=.
  case: (Archi.ptr64)=> //=. rewrite /Values.Val.of_bool /bool_to_int /=.
  by case: ifP=> //=.
+ case: (intsize_eq I32 I32)=> //= heq.
  rewrite /Values.Val.of_bool /bool_to_int /=. by case: ifP=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. case: p=> //= i i' [] hv; subst; rewrite /=.
  rewrite /Cop.sem_cmp /Cop.sem_binarith /Cop.sem_cast /=.
  case: (Archi.ptr64)=> //=. rewrite /Values.Val.of_bool /bool_to_int /=.
  by case: ifP=> //=.
+ case: (intsize_eq I32 I32)=> //= heq.
  rewrite /Values.Val.of_bool /bool_to_int /=. by case: ifP=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //= b b'.
  case: t2=> //= p. case: p=> //= [] [] hv; subst; rewrite /=.
  rewrite /Cop.sem_cmp /Cop.sem_binarith /Cop.sem_cast /=.
  case: (Archi.ptr64)=> //=. 
  + rewrite /Values.Val.of_bool /bool_to_int /=. case: ifP=> //=.
    + case: ifP=> //= hb'.
      + by case: ifP=> //=.
      by case: ifP=> //=.
    case: ifP=> //= hb'.
    + by case: ifP=> //=.
    by case: ifP=> //=.
  case: (intsize_eq I32 I32)=> //= heq.
  rewrite /Values.Val.of_bool /bool_to_int /=.
  case: ifP=> //=.
  + case: ifP=> //= hb'.
    + by case: ifP=> //=.
    by case: ifP=> //=.
  case: ifP=> //= hb'.
  + case: ifP=> //=. by case: ifP=> //=.
admit. (* Pointer equality: FIX ME *)
Admitted.

Lemma transl_neq_cneq: forall v1 v2 t1 t2 v cenv m,
sem_binary_operation Neq v1 v2 t1 t2 = Some v -> 
Cop.sem_binary_operation cenv (transBeePL_bop_bop Neq) (transBeePL_value_cvalue v1) 
     (transBeePL_type t1) (transBeePL_value_cvalue v2) (transBeePL_type t2) m = 
Some (transBeePL_value_cvalue v). 
Proof.
move=> v1 v2 t1 t2 v cenv m /= ha. case: v1 ha=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. case: p=> //= [] [] hv; subst; rewrite /=.
  rewrite /Cop.sem_cmp /Cop.sem_binarith /Cop.sem_cast /=.
  by case: (Archi.ptr64)=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. case: p=> //= i i' [] hv; subst; rewrite /=.
  rewrite /Cop.sem_cmp /Cop.sem_binarith /Cop.sem_cast /=.
  case: (Archi.ptr64)=> //=. rewrite /Values.Val.of_bool /bool_to_int /=.
  by case: ifP=> //=.
+ case: (intsize_eq I32 I32)=> //= heq.
  rewrite /Values.Val.of_bool /bool_to_int /=. by case: ifP=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. case: p=> //= i i' [] hv; subst; rewrite /=.
  rewrite /Cop.sem_cmp /Cop.sem_binarith /Cop.sem_cast /=.
  case: (Archi.ptr64)=> //=. rewrite /Values.Val.of_bool /bool_to_int /=.
  by case: ifP=> //=.
+ case: (intsize_eq I32 I32)=> //= heq.
  rewrite /Values.Val.of_bool /bool_to_int /=. by case: ifP=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //= b b'.
  case: t2=> //= p. case: p=> //= [] [] hv; subst; rewrite /=.
  rewrite /Cop.sem_cmp /Cop.sem_binarith /Cop.sem_cast /=.
  case: (Archi.ptr64)=> //=. 
  + rewrite /Values.Val.of_bool /bool_to_int /=. case: ifP=> //=.
    + case: ifP=> //= hb'.
      + by case: ifP=> //=.
      by case: ifP=> //=.
    case: ifP=> //= hb'.
    + by case: ifP=> //=.
    by case: ifP=> //=.
  case: (intsize_eq I32 I32)=> //= heq.
  rewrite /Values.Val.of_bool /bool_to_int /=.
  case: ifP=> //=.
  + case: ifP=> //= hb'.
    + by case: ifP=> //=.
    by case: ifP=> //=.
  case: ifP=> //= hb'.
  + case: ifP=> //=. by case: ifP=> //=.
admit. (* Pointer equality: FIX ME *)
Admitted.

Lemma transl_lt_clt: forall v1 v2 t1 t2 v cenv m,
sem_binary_operation Lt v1 v2 t1 t2 = Some v -> 
Cop.sem_binary_operation cenv (transBeePL_bop_bop Lt) (transBeePL_value_cvalue v1) 
     (transBeePL_type t1) (transBeePL_value_cvalue v2) (transBeePL_type t2) m = 
Some (transBeePL_value_cvalue v). 
Proof.
move=> v1 v2 t1 t2 v cenv m /= ha. case: v1 ha=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. case: p=> //= [] [] hv; subst; rewrite /=.
  rewrite /Cop.sem_cmp /Cop.sem_binarith /Cop.sem_cast /=.
  case: (Archi.ptr64)=> //=. 
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. case: p=> //= i i' [] hv; subst; rewrite /=.
  rewrite /Cop.sem_cmp /Cop.sem_binarith /Cop.sem_cast /=.
  case: (Archi.ptr64)=> //=. rewrite /Values.Val.of_bool /bool_to_int /=.
  by case: ifP=> //=.
+ case: (intsize_eq I32 I32)=> //= heq.
  rewrite /Values.Val.of_bool /bool_to_int /=. by case: ifP=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. case: p=> //= i i' [] hv; subst; rewrite /=.
  rewrite /Cop.sem_cmp /Cop.sem_binarith /Cop.sem_cast /=.
  case: (Archi.ptr64)=> //=. rewrite /Values.Val.of_bool /bool_to_int /=.
  by case: ifP=> //=.
+ case: (intsize_eq I32 I32)=> //= heq.
  rewrite /Values.Val.of_bool /bool_to_int /=. by case: ifP=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //= b b'.
  case: t2=> //= p. case: p=> //= [] [] hv; subst; rewrite /=.
  case: v2=> //= p p'. case: t1=> //= i b. case:b=> //= p''.
  case: p''=> //=. case: t2=> //= i' b'. case: b'=> //= p1.
  by case: p1=> //=.
Qed.

Lemma transl_gt_cgt: forall v1 v2 t1 t2 v cenv m,
sem_binary_operation Gt v1 v2 t1 t2 = Some v -> 
Cop.sem_binary_operation cenv (transBeePL_bop_bop Gt) (transBeePL_value_cvalue v1) 
     (transBeePL_type t1) (transBeePL_value_cvalue v2) (transBeePL_type t2) m = 
Some (transBeePL_value_cvalue v). 
Proof.
move=> v1 v2 t1 t2 v cenv m /= ha. case: v1 ha=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. case: p=> //= [] [] hv; subst; rewrite /=.
  rewrite /Cop.sem_cmp /Cop.sem_binarith /Cop.sem_cast /=.
  case: (Archi.ptr64)=> //=. 
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. case: p=> //= i i' [] hv; subst; rewrite /=.
  rewrite /Cop.sem_cmp /Cop.sem_binarith /Cop.sem_cast /=.
  case: (Archi.ptr64)=> //=. rewrite /Values.Val.of_bool /bool_to_int /=.
  by case: ifP=> //=.
+ case: (intsize_eq I32 I32)=> //= heq.
  rewrite /Values.Val.of_bool /bool_to_int /=. by case: ifP=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. case: p=> //= i i' [] hv; subst; rewrite /=.
  rewrite /Cop.sem_cmp /Cop.sem_binarith /Cop.sem_cast /=.
  case: (Archi.ptr64)=> //=. rewrite /Values.Val.of_bool /bool_to_int /=.
  by case: ifP=> //=.
+ case: (intsize_eq I32 I32)=> //= heq.
  rewrite /Values.Val.of_bool /bool_to_int /=. by case: ifP=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //= b b'.
  case: t2=> //= p. case: p=> //= [] [] hv; subst; rewrite /=.
  case: v2=> //= p p'. case: t1=> //= i b. case:b=> //= p''.
  case: p''=> //=. case: t2=> //= i' b'. case: b'=> //= p1.
  by case: p1=> //=.
Qed.

Lemma transl_lte_cle: forall v1 v2 t1 t2 v cenv m,
sem_binary_operation Lte v1 v2 t1 t2 = Some v -> 
Cop.sem_binary_operation cenv (transBeePL_bop_bop Lte) (transBeePL_value_cvalue v1) 
     (transBeePL_type t1) (transBeePL_value_cvalue v2) (transBeePL_type t2) m = 
Some (transBeePL_value_cvalue v). 
Proof.
move=> v1 v2 t1 t2 v cenv m /= ha. case: v1 ha=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. case: p=> //= [] [] hv; subst; rewrite /=.
  rewrite /Cop.sem_cmp /Cop.sem_binarith /Cop.sem_cast /=.
  by case: (Archi.ptr64)=> //=. 
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. case: p=> //= i i' [] hv; subst; rewrite /=.
  rewrite /Cop.sem_cmp /Cop.sem_binarith /Cop.sem_cast /=.
  case: (Archi.ptr64)=> //=. rewrite /Values.Val.of_bool /bool_to_int /=.
  by case: ifP=> //=.
+ case: (intsize_eq I32 I32)=> //= heq.
  rewrite /Values.Val.of_bool /bool_to_int /=. by case: ifP=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. case: p=> //= i i' [] hv; subst; rewrite /=.
  rewrite /Cop.sem_cmp /Cop.sem_binarith /Cop.sem_cast /=.
  case: (Archi.ptr64)=> //=. rewrite /Values.Val.of_bool /bool_to_int /=.
  by case: ifP=> //=.
+ case: (intsize_eq I32 I32)=> //= heq.
  rewrite /Values.Val.of_bool /bool_to_int /=. by case: ifP=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //= b b'.
  case: t2=> //= p. case: p=> //= [] [] hv; subst; rewrite /=.
  rewrite /Cop.sem_cmp /Cop.sem_binarith /Cop.sem_cast /=.
  case: (Archi.ptr64)=> //=. rewrite Int.not_lt /Values.Val.of_bool /=.
  case: ifP=> //= hb. move: hv. case: ifP=> //= hb' [] <- /=. by rewrite hb'.
  move: hv. case: ifP=> //= hb' [] hv /=; subst. rewrite hb' /=.
  rewrite orb_lazy_alt in hb. move: hb. case: ifP=> //= h1 h2. 
  rewrite /bool_to_int /= in h2. move: h2. case: ifP=> //= hb.
  + case: b hb' h1=> //= hb' h1 h. by case: b' hb hb' h1=> //=.
  subst; rewrite /=. by case: b h1 hb'=> //=.
+ move: hv. case: ifP=> //= hb [] <-; rewrite /=.
  case: (intsize_eq I32 I32)=> //= heq.
  rewrite /Values.Val.of_bool /bool_to_int /=. case: ifP=> //=.
  + case: ifP=> //= hb'; subst.
    + case: ifP=> //= hb'' hi; subst; rewrite /=. by case: b hb hb'=> //=.
    by case: b' hb=> //=.
  case: b hb=> //=.
  + by case: b'=> //=.
  by case: b'=> //=.
case: v2=> //=. case: t1=> //= i bt p p'. case: bt=> //= p''.
case: p''=> //=. case: t2=> //= i' b. case:b=> //= p2. by case:p2=> //=. 
Qed.


Lemma transl_gte_cge: forall v1 v2 t1 t2 v cenv m,
sem_binary_operation Gte v1 v2 t1 t2 = Some v -> 
Cop.sem_binary_operation cenv (transBeePL_bop_bop Gte) (transBeePL_value_cvalue v1) 
     (transBeePL_type t1) (transBeePL_value_cvalue v2) (transBeePL_type t2) m = 
Some (transBeePL_value_cvalue v). 
Proof.
move=> v1 v2 t1 t2 v cenv m /= ha. case: v1 ha=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. case: p=> //= [] [] hv; subst; rewrite /=.
  rewrite /Cop.sem_cmp /Cop.sem_binarith /Cop.sem_cast /=.
  by case: (Archi.ptr64)=> //=. 
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. case: p=> //= i i' [] hv; subst; rewrite /=.
  rewrite /Cop.sem_cmp /Cop.sem_binarith /Cop.sem_cast /=.
  case: (Archi.ptr64)=> //=. rewrite /Values.Val.of_bool /bool_to_int /=.
  by case: ifP=> //=.
+ case: (intsize_eq I32 I32)=> //= heq.
  rewrite /Values.Val.of_bool /bool_to_int /=. by case: ifP=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //=.
  case: t2=> //= p. case: p=> //= i i' [] hv; subst; rewrite /=.
  rewrite /Cop.sem_cmp /Cop.sem_binarith /Cop.sem_cast /=.
  case: (Archi.ptr64)=> //=. rewrite /Values.Val.of_bool /bool_to_int /=.
  by case: ifP=> //=.
+ case: (intsize_eq I32 I32)=> //= heq.
  rewrite /Values.Val.of_bool /bool_to_int /=. by case: ifP=> //=.
+ case: v2=> //=. case: t1=> //= p. case: p=> //= b b'.
  case: t2=> //= p. case: p=> //= [] [] hv; subst; rewrite /=.
  rewrite /Cop.sem_cmp /Cop.sem_binarith /Cop.sem_cast /=.
  case: (Archi.ptr64)=> //=. rewrite Int.not_lt /Values.Val.of_bool /=.
  case: ifP=> //= hb. move: hv. case: ifP=> //= hb' [] <- /=. by rewrite hb'.
  move: hv. case: ifP=> //= hb' [] hv /=; subst. rewrite hb' /=.
  rewrite orb_lazy_alt in hb. move: hb. case: ifP=> //= h1 h2. 
  rewrite /bool_to_int /= in h2. move: h2. case: ifP=> //= hb.
  + case: b' hb' h1=> //= hb' h1 h. by case: b hb hb' h1=> //=.
  subst; rewrite /=. by case: b' h1 hb'=> //=.
+ move: hv. case: ifP=> //= hb [] <-; rewrite /=.
  case: (intsize_eq I32 I32)=> //= heq.
  rewrite /Values.Val.of_bool /bool_to_int /=. case: ifP=> //=.
  + case: ifP=> //= hb'; subst.
    + case: ifP=> //= hb'' hi; subst; rewrite /=. by case: b' hb hb'=> //=.
    by case: b hb=> //=.
  case: b hb=> //=.
  + by case: b'=> //=.
  by case: b'=> //=.
case: v2=> //=. case: t1=> //= i bt p p'. case: bt=> //= p''.
case: p''=> //=. case: t2=> //= i' b. case:b=> //= p2. by case:p2=> //=. 
Qed.

Lemma transl_bop_cbop : forall cenv op v1 v2 t1 t2 v m,
sem_binary_operation op v1 v2 t1 t2 = Some v -> 
Cop.sem_binary_operation cenv (transBeePL_bop_bop op) (transBeePL_value_cvalue v1) 
   (transBeePL_type t1) (transBeePL_value_cvalue v2) (transBeePL_type t2) m = Some (transBeePL_value_cvalue v).
Proof.
intros. destruct op; simpl; auto; subst.
(* Add *)
+ by have := (transl_plus_cadd v1 v2 t1 t2 v cenv m H).
(* Sub *)
+ by have := (transl_minus_csub v1 v2 t1 t2 v cenv m H).
(* Mult *)
+ by have := (transl_mult_cmul v1 v2 t1 t2 v cenv m H).
(* Div *)
+ by have := (transl_div_cdiv v1 v2 t1 t2 v cenv m H).
(* And *)
+ by have := (transl_and_cand v1 v2 t1 t2 v cenv m H).
(* Or *)
+ by have := (transl_or_cor v1 v2 t1 t2 v cenv m H).
(* Xor *)
+ by have := (transl_xor_cxor v1 v2 t1 t2 v cenv m H).
(* Shl *)
+ by have := (transl_shl_cshl v1 v2 t1 t2 v cenv m H).
(* Shr *)
+ by have := (transl_shr_cshr v1 v2 t1 t2 v cenv m H).
(* Eq *)
+ by have := (transl_eq_ceq v1 v2 t1 t2 v cenv m H).
(* Ne *)
+ by have := (transl_neq_cneq v1 v2 t1 t2 v cenv m H).
(* Lt *)
+ by have := (transl_lt_clt v1 v2 t1 t2 v cenv m H).
(* Le *)
+ by have := (transl_lte_cle v1 v2 t1 t2 v cenv m H).
(* Gt *)
+ by have := (transl_gt_cgt v1 v2 t1 t2 v cenv m H).
(* Ge *)
by have := (transl_gte_cge v1 v2 t1 t2 v cenv m H).
Qed.




