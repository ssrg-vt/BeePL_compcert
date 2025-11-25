Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import BeePL BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import compcert.common.Errors Initializersproof Cstrategy Coqlib Errors.

From mathcomp Require Import all_ssreflect. 

(***** Correctness proof for type transformation from BeePL to Ctypes *****)

(* Easy *)
Lemma transBeePL_type_int : forall t sz s a,
transBeePL_type t = (Ctypes.Tint sz s a) ->
t = Vtype (Tint sz s a) \/ t = Vtype Tbool.
Proof.
move=> [].
+ move=> p sz s /=. by case: p=> //= sz' s' a' [] h1 h2 h3 h4; subst.
+ move=> [].
  + move=> sz s a /= [] h1 h2 h3; subst. by right.
  + move=> sz s a sz' s' a' /= [] h1 h2 h3; subst. by left.
  by move=> s a sz s' a' //=.
Admitted.

(* Easy *)
Lemma transBeePL_type_long : forall t s a,
transBeePL_type t = Ctypes.Tlong s a ->
t = Vtype (Tlong s a).
Proof. 
Admitted.

(* Easy *)
Lemma transBeePL_type_void : forall t,
transBeePL_type t = Tvoid->
t = Utype.
Proof.
Admitted.

(* Easy *)
Lemma transBeePL_ptr_ref_bool : forall h bt a,
transBeePL_ptr_type (Reftype h bt a) = Ctypes.Tpointer (Ctypes.Tint I8 Unsigned noattr) noattr ->
bt = Bprim Tbool.
Proof.
Admitted.

(* Easy *)
Lemma transBeePL_ptr_ref_int : forall h bt sz s a a',
transBeePL_ptr_type (Reftype h bt a) = Ctypes.Tpointer (Ctypes.Tint sz s a') a ->
bt = Bprim (Tint sz s a').
Proof.
Admitted.

(* Easy *)
Lemma transBeePL_ptr_ref_long : forall h bt s a a',
transBeePL_ptr_type (Reftype h bt a) = Ctypes.Tpointer (Ctypes.Tlong s a') a ->
bt = Bprim (Tlong s a').
Proof.
Admitted.

(* Easy *)
Lemma transBeePL_ptr_ref_struct : forall h bt s a a',
transBeePL_ptr_type (Reftype h bt a) = Ctypes.Tpointer (Ctypes.Tstruct s a') a ->
bt = Bstruct s a'.
Proof.
Admitted.

(* Easy *)
Lemma transBeePL_ptr_ref_array : forall h bt bt' z a a',
transBeePL_ptr_type (Reftype h bt a) = Ctypes.Tpointer (Ctypes.Tarray (transBeePL_type (Vtype bt')) z a') a ->
bt = Barray bt' z a'.
Proof.
Admitted.

(* Easy *)
Lemma transBeePL_type_pfunction : forall t cts ct c,
transBeePL_ptr_type t = (Tfunction cts ct c) ->
exists bts bef brt, t = Fptype bts bef brt /\ transBeePL_types transBeePL_type bts = cts /\ transBeePL_type brt = ct. 
Proof.
Admitted.

(* Easy *)
Lemma transBeePL_type_ptr : forall t pt,
transBeePL_type t = transBeePL_ptr_type pt ->
t = Ptrtype pt.
Proof.
Admitted.

(* Easy *)
Lemma transBeePL_type_stype : forall t s a,
transBeePL_type t = Tstruct s a ->
t = Stype s a.
Proof.
Admitted.

(* Easy *)
Lemma transBeePL_type_function : forall t cts ct c,
transBeePL_type t = (Tfunction cts ct c) ->
exists bts bef brt, t = Ftype bts bef brt /\ transBeePL_types transBeePL_type bts = cts /\ transBeePL_type t = ct. 
Proof.
Admitted.

(* Easy *)
Lemma transBeePL_type_bytes : forall t,
transBeePL_type t = Tstruct bytes_t noattr ->
t = Bytes.
Proof.
Admitted.

Lemma no_bptype_to_float : forall pt f a,
transBeePL_ptr_type pt <> Tfloat f a.
Proof.
move=> pt. elim: pt=> //= h b. elim: b=> //=.
+ by move=> [] //=.
by move=> [] //=.
Qed.

Lemma no_btype_to_float : forall t f a ,
transBeePL_type t <> (Tfloat f a).
Proof.
move=> t f a /=. case: t=> //=.
+ by move=> p; case: p=> //=.
+ move=> [] //=.
  + move=> h [] //=. by move=> [] //=.
  by move=> [] //=.
move=> p. by apply no_bptype_to_float.
Qed.

Lemma no_bptype_to_union : forall pt f a,
transBeePL_ptr_type pt <> Tunion f a.
Proof.
move=> pt. elim: pt=> //= h b. elim: b=> //=.
+ by move=> [] //=.
by move=> [] //=.
Qed.

Lemma no_btype_to_union : forall t f a ,
transBeePL_type t <> (Tunion f a).
Proof.
move=> t f a /=. case: t=> //=.
+ by move=> p; case: p=> //=.
+ move=> [] //=.
  + move=> h [] //=. by move=> [] //=.
  by move=> [] //=.
move=> p. by apply no_bptype_to_union.
Qed.

Lemma access_mode_preserved : forall ty cty md, 
access_mode_type ty = md ->
transBeePL_type ty =  cty ->
Ctypes.access_mode cty = md.
Proof.
Admitted.

Lemma non_volatile_type_preserved : forall ty cty b,
type_is_volatile (transBeePL_type ty) = b ->
transBeePL_type ty = cty ->
Ctypes.type_is_volatile cty = b.
Proof.
Admitted.

(* Lemma typec_expr : forall e ct ce g' g'' i',
transBeePL_type (typeof_expr e) = ct ->
transBeePL_expr_expr e  g' = Res ce g'' i' ->
ct = Csyntax.typeof ce.
Proof.
Admitted. *)

Lemma bv_cv_reflex : forall v' v,
trans_cvalue_bvalue v' = OK v ->
trans_bvalue_cvalue v = v'.
Proof.
Admitted.

Lemma bc_cv_comp : forall v,
trans_cvalue_bvalue (trans_bvalue_cvalue v) = OK v.
Proof.
Admitted.

(* Since translation of types does not depend on the generator, it 
   should produce the same result irrespective of them *)
(* Coqlib.v has lot of lemmas related to Ple *)
Lemma type_preserved_generator : forall t r r' ,
transBeePL_type t = r ->
transBeePL_type t = r'->
r = r'.
Proof. (* use inductive principle proved in BeeTypes.v *)
Admitted.

Lemma eq_type_trans : forall t t' t'',
eq_type t t' ->
transBeePL_type t' = t'' ->
t'' = transBeePL_type t. 
Proof.
Admitted.

(*** Auxillary lemmas related to types and effects ***)
(* Complete Me: Easy *)
Lemma sub_effect_refl : forall ef, 
sub_effect ef ef = true.
Proof.
Admitted.

(* Complete Me: Easy *)
Lemma sub_effect_nil : forall ef, 
sub_effect nil ef = true.
Proof.
Admitted.

(* Complete Me: Easy *)
Lemma sub_effect_trans : forall ef1 ef2 ef3, 
sub_effect ef1 ef2 = true ->
sub_effect ef2 ef3 = true ->
sub_effect ef1 ef3 = true.
Proof.
Admitted.

(* Complete Me: Easy *)
Lemma prefix_sub_effect : forall (ef1 ef2 : effect), 
sub_effect ef1 (ef1 ++ ef2)%list = true.
Proof. 
Admitted.

(* Complete Me: Easy *)
Lemma suffix_sub_effect : forall (ef1 ef2 : effect), 
sub_effect ef2 (ef1 ++ ef2)%list = true.
Proof. 
Admitted.

(* Complete Me: Easy *)
Lemma sub_effect_concat : forall ef1 ef2 ef1' ef2',
sub_effect ef1 ef1' ->
sub_effect ef2 ef2' ->
sub_effect (ef1 ++ ef2) (ef1' ++ ef2').
Proof.
Admitted.

(* Complete Me: Easy *)
Lemma no_divergence_concat : forall ef ef',
no_divergence ef ->
no_divergence ef' ->
no_divergence (ef ++ ef').
Proof.
Admitted. 


Lemma ptr_eq_trans : forall p p0, 
eq_ptr_type p p0 -> 
transBeePL_ptr_type p0 = transBeePL_ptr_type p.
Proof.
move=> [].
+ move=> h b a [] //=.
  + move=> h' [] //=.
    + move=> [] //=.
      + move=> a' /=. case: b=> //=.
        + move=> [] //=.
          + by move=> i s a1 /andP [] /andP [] h1 //=.
          by move=> s a1 /andP [] /andP [] h1 //=.
        by move=> i a1 /andP [] /andP [] h1 //=.
      move=> [] //=.
      + by move=> z a1 /andP [] /andP [] h1 //=.
      + by move=> i s a1 z a2 /andP [] /andP [] h1 //=.
      by move=> s a1 z a2 /andP [] /andP [] h1 //=.
    case: b=> //=.
    + move=> [] //=.
      + by move=> i s a1 a2 /andP [] /andP [] h1 //=.
      + move=> sz s a1 sz' s' a2 a3 /andP. case: ifP=> //=.
        + case: ifP=> //=.
          + case: ifP=> //=.
            + move=> ha hs hsz [] hh ha'. admit. (* provable *)
            by move=> ha hs hsz [] /andP [] h1 //=.
          by move=> hs hsz [] /andP [] hh //=. 
        by move=> hsz [] /andP [] hh //=.
      by move=> s a1 i s' a2 a3 /andP [] /andP [] hh //=.
    by move=> h1 a1 i1 s a3 a4 /andP [] /andP [] hh //=.
  move=> [].
  + by move=> z a1 i s a2 a3 /andP [] /andP [] hh //=.
  + by move=> sz s a' z a1 i'' s' a2 a3 /andP [] /andP [] hh //=.
  + by move=> s a1 z a2 i s' a3 a4 /andP [] /andP [] hh //=.
  + case: b=> //=.
    + move=> [] //=.
      + by move=> s a1 a2 /andP [] /andP [] hh //=.
      by move=> sz s a1 s' a2 a3 /andP [] /andP [] hh //=.
    move=> s a1 s' a2 a3 /andP. case: ifP=> //=.
    + case: ifP=> //=.
      + move=> ha hs [] hh ha'. admit. (* provable *)
      by move=> ha hs [] /andP [] h1 //=.
    by move=> hs [] /andP [] hh //=. 
  by move=> h1 a1 s a3 a4 /andP [] /andP [] hh //=.
 + by move=> p z a1 s a2 a3 /andP [] /andP [] hh //=. 
 + case: b=> //=.
   + move=> [].
     + by move=> h1 a1 a2 /andP [] /andP [] hh //=.
     + by move=> sz a' a1 i1 a2 a3 /andP [] /andP [] hh //=.
     by move=> s a1 i a2 a3 /andP [] /andP [] hh //=.
   move=> i a1 i1 a2 a3 /andP [] /andP [] hh /andP [] h1 h2 h3. admit. (* provable *)
 + move=> [] //=.
   + by move=> z a1 i a2 a3 /andP [] /andP [] hh //=.
   + by move=> sz a1 a1' z a2 a3 a4 a5 /andP [] /andP [] hh //=.
   by move=> s a1 z a2 i a3 a4 /andP [] /andP [] hh //=.
 + move=> [] //=.
   + case: b=> //=.
     + by move=> p z a1 a2 /andP [] /andP [] hh //=.
     + by move=> i a1 z a2 a3 /andP [] /andP [] hh //=.
     move=> [] //=.
     + move=> z a1 z2 a2 a3 /andP [] /andP [] hh /andP [] hz ha1 ha2. admit. (* provable *)
     + by move=> sz s a1 z a2 z' a3 a4 /andP [] /andP [] hh //=.
     by move=> s a1 z a2 z' a3 a4 /andP [] /andP [] hh //=.
   + case: b=> //=.
     + by move=> p i s a1 z a2 a3 /andP [] /andP [] hh //=.
     by move=> i a' i'' s a1 z a2 a3 /andP [] /andP [] hh //=.
   + move=> [] //=.
     + by move=> z a1 sz s a1' z' a2 a3 /andP [] /andP [] hh //=.
     move=> sz a1 a2 z a3 sz' a4 a5 z'' a6 a7. case: ifP=> //=.
     + case: ifP=> //=.
       + case: ifP=> //=.
         + move=> ha hs hsz /andP [] /andP [] hh /andP [] hz ha1 ha2. admit. (* provable *)
         by move=> ha hs hsz /andP [] /andP [] hh //=.
       by move=> hs hsz /andP [] /andP [] hh //=.
     by move=> hsz /andP [] /andP [] hh //=.
   by move=> s a1 z a2 i s' a3 z' a4 a5 /andP [] /andP [] hh //=.
  + case: b=> //=.
    + by move=> p s a1 z a2 a3 /andP [] /andP [] hh //=.
    + by move=> h1 a1 s a2 z a3 a4 /andP [] /andP [] hh //=.
    move=> [] //=.
    + by move=> z a1 s a2 z' a3 a4 /andP [] /andP [] hh //=.
    + by move=> sz a' a1 z a2 s' a3 z' a4 a5 /andP [] /andP [] hh //=.
  move=> s a1 z a2 s' a3 z1 a4 a5. case: ifP=> //=.
  + case: ifP=> /=.
    + move=> ha hs /andP [] /andP [] hh /andP [] hz ha1 ha2. admit. (* provable *)
    by move=> ha hs /andP [] /andP [] hh //=.
  by move=> hs /andP [] /andP [] hh //=.
+ move=> [] //=.
  + move=> h [] //=.
    + move=> p a [] //= p0. case: p0=> //=.
      move=> h' [] //=.
      + move=> [] //=.
        + case: p=> //=.
          + by move=> sz a' a1 a2 /andP [] /andP [] hh //=.
          by move=> s a1 a2 /andP [] /andP [] hh //=.
        case: p=> //=.
        + by move=> sz s a1 a2 /andP [] /andP [] hh //=.
        move=> sz a' a1 sz' s' a2 a3. case: ifP=> //=.
        + case: ifP=> //=.
          + case: ifP=> //=.
            + move=> ha hs hsz /andP [] /andP [] hh _ ha1. admit. (* provable *)
          by move=> ha1 hs1 hsz1 /andP [] /andP [] hh //=.
        by move=> hs hsz /andP [] /andP [] hh //=.
      by move=> hsz /andP [] /andP [] hh //=.
    by move=> s a1 i a' a2 a3 /andP [] /andP [] hh //=.
  + case: p=> //=.
    + by move=> s a1 a2 /andP [] /andP [] hh //=.
    + by move=> sz a'' a1 a' a2 a3 /andP [] /andP [] hh //=.
    + move=> s a1 a' a2 a3. case: ifP=> //=.
      + case: ifP=> //=.
        + admit. (* provable *)
        by move=> ha hs /andP [] /andP [] hh //=.
      by move=> hs /andP [] /andP [] hh //=.
    + by move=> h1 a1 a2 /andP [] /andP [] hh //=.
    + by move=> p1 z a1 a2 /andP [] /andP [] hh //=.
    + move=> h1 a1 a2 [].
      + by move=> h2 b a //=.
      + move=> [] //= h3 [] //=. 
        + by move=> p a /andP [] /andP [] hh //=.
        + move=> h4 a3 a4 /andP [] /andP [] hh1 hh2 ha. admit. (* provable *)
        by move=> p z a3 a4 /andP [] /andP [] hh //=.
      by move=> es e t //=.
    + move=> p z a1 a2 p0. case: p0=> //=. move=> [] //=.
      move=> h1 [] //=.  
      + by move=> p' a /andP [] /andP [] hh //=.
      + by move=> h2 a3 a4 /andP [] /andP [] hh //=.
      case: p=> //=.
      + move=> [] //=.
        + admit. (* provable *)
        + by move=> sz a a' z' a3 a4 /andP [] /andP [] hh //=.
        by move=> s a z1 a4 a5 /andP [] /andP [] hh //=.
      move=> sz s a [] //=.
      + by move=> z1 a4 a5 /andP [] /andP [] hh //=.
      + move=> sz1 s1 a3 z1 a4 a5. case: ifP=> //=.
        + case: ifP=> //=.
          + case: ifP=> //=.
            + admit. (* provable *)
            by move=> ha1 hs1 hsz1 /andP [] /andP [] hh1 //=.
          by move=> hs hsz /andP  [] /andP [] hh1 //=.
        by move=> hsz /andP [] /andP [] hh //=.
      by move=> s1 a3 z1 a4 a5 /andP [] /andP [] hh //=.
Admitted.


Lemma ptr_t_eq_trans : forall t p,
eq_type t (Ptrtype p) ->
transBeePL_ptr_type p = transBeePL_type t.
Proof.
move=> [].
+ move=> [].
  + by move=> h b a //=.
  + by move=> [] h b //=.
  by move=> es e t //=.
+ by move=> [] //=.
+ move=> p1 p2 hp /=. by have hp' := ptr_eq_trans p1 p2 hp.
+ by move=> h a p //=.
+ by move=> t z a p /= //=.
+ by move=> es e t p /=.
by move=> p /=.     
Qed.







