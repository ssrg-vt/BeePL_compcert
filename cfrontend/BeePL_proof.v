Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import compcert.common.Errors Initializersproof Cstrategy BeePL_auxlemmas.

From mathcomp Require Import all_ssreflect. 

(***** Correctness proof for the Csyntax generation from BeePL using BeePL compiler *****)

(***** Specification for types *****) 
Inductive rel_ptype : BeeTypes.primitive_type -> Ctypes.type -> Prop :=
| rel_tunit : rel_ptype Tunit (Ctypes.Tvoid) (* Fix me *)
| rel_tint : forall sz s a, 
             rel_ptype (Tint sz s a) (Ctypes.Tint sz s a)
| rel_tlong : forall s a, 
              rel_ptype (Tlong s a) (Ctypes.Tlong s a). 

Inductive rel_btype : BeeTypes.basic_type -> Ctypes.type -> Prop :=
| rel_bt : forall p ct,
           rel_ptype p ct ->
           rel_btype (Bprim p) ct.

Inductive rel_type : BeeTypes.type -> Ctypes.type -> Prop :=
| rel_pt : forall p ct, 
           rel_ptype p ct ->
           rel_type (Ptype p) ct
| rel_reftype : forall h bt ct a, 
                rel_btype bt ct ->
                rel_type (Reftype h bt a) (Tpointer ct a)
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

Scheme rel_type_ind_mut := Induction for rel_type Sort Prop
  with rel_typelist_ind_mut := Induction for rel_types Sort Prop.
Combined Scheme rel_type_typelist_ind_mut from rel_type_ind_mut, rel_typelist_ind_mut.

Section rel_type_ind.
Context (Rts : list BeeTypes.type -> Ctypes.typelist -> Prop).
Context (Rt : BeeTypes.type -> Ctypes.type -> Prop).
Context (Rpt : BeeTypes.primitive_type -> Ctypes.type -> Prop).
Context (Rbt : BeeTypes.basic_type -> Ctypes.type -> Prop).
Context (Rtunit : Rpt Tunit (Ctypes.Tvoid)).
Context (Rtint : forall sz s a, Rpt (Tint sz s a) (Ctypes.Tint sz s a)).
Context (Rtlong : forall s a, Rpt (Tlong s a) (Ctypes.Tlong s a)).
Context (Rbth : forall p ct, Rpt p ct -> Rbt (Bprim p) ct).
Context (Rpth : forall p ct, Rpt p ct -> Rt (Ptype p) ct).
Context (Rreft : forall h bt a ct, Rbt bt ct -> Rt (Reftype h bt a) (Tpointer ct a)). 
Context (Rfunt : forall ts ef t cts ct, Rts ts cts -> Rt t ct -> 
                 Rt (Ftype ts ef t) (Tfunction cts ct 
                                     {| cc_vararg := Some (Z.of_nat(length(ts))); cc_unproto := false; cc_structret := false |})).
Context (Rnil : Rts nil Tnil).
Context (Rcons : forall t ct ts cts, Rt t ct -> Rts ts cts -> Rts (t :: ts) (Tcons ct cts)).

Lemma rel_type_indP : 
(forall t ct, rel_type t ct -> Rt t ct) /\
(forall ts cts, rel_types ts cts -> Rts ts cts).
Proof. 
apply rel_type_typelist_ind_mut=> //=.
+ move=> p ct /= hr. apply Rpth. case: p hr=> //=.
  + case: ct=> //=.
    + by move=> i s a hr;inversion hr.
    + by move=> s a hr;inversion hr.
    + by move=> f a hr; inversion hr.
    + by move=> t a hr; inversion hr.
    + by move=> t z a hr; inversion hr.
    + by move=> ts t c hr; inversion hr.
    + by move=> i a hr; inversion hr.
    by move=> i a hr; inversion hr.
  + move=> i s a hr. case: ct hr=> //=.
    + by move=> hr; inversion hr.
    + by move=> sz' s' a' hr; inversion hr; subst.
    + by move=> s' a' hr; inversion hr; subst.
    + by move=> f a' hr; inversion hr.
    + by move=> t a' hr; inversion hr.
    + by move=> t z a' hr; inversion hr.
    + by move=> t t' c hr; inversion hr.
    + by move=> i' a' hr; inversion hr.
    by move=> i' a' hr; inversion hr.
  + case: ct=> //=.
    + by move=> s a hr; inversion hr.
    + by move=> sz s a s' a' hr; inversion hr; subst.
    + by move=> s a s' a' hr; inversion hr; subst.
    + by move=> f a s a' hr; inversion hr; subst.
    + by move=> t a s a' hr; inversion hr.
    + by move=> t z a s a' hr; inversion hr.
    + by move=> ts t c s a hr; inversion hr.
    + by move=> i a s a' hr; inversion hr.
    by move=> i a s a' hr; inversion hr.
+ move=> h bt ct a hr; inversion hr; subst.
  apply Rreft. apply Rbth. case: p hr H=> //=.
  + case: ct=> //=.
    + by move=> i s a' hr H; inversion H; subst.
    + by move=> s a' hr H; inversion H; subst.
    + by move=> f a' hr H; inversion H.
    + by move=> t a' hr H; inversion H.
    + by move=> t z a' hr H; inversion H.
    + by move=> ts t c hr H; inversion H.
    + by move=> i a' hr H; inversion H.
    + by move=> i a' hr H; inversion H.
    + by move=> u s a' hr H; inversion H.
    by move=> s a' hr H; inversion H.
+ move=> ts ef t cts ct hrs hts hr ht hd.
  by move: (Rfunt ts ef t cts ct hts ht).
move=> bt bts ct cts hr ht hrs hts. 
by move: (Rcons bt ct bts cts ht hts).
Qed. 

End rel_type_ind.

(***** Proof for correctness of type transformation *****)
Lemma type_translated: 
(forall bt ct, 
transBeePL_type bt = OK ct ->
rel_type bt ct) /\ 
(forall bts cts, 
transBeePL_types transBeePL_type bts = OK cts ->
rel_types bts cts).
Proof.
Admitted.

Section specifications.

(* Relates global variables of BeePL and Csyntax *)
Inductive match_globvar : BeePL.globvar -> AST.globvar Ctypes.type -> Prop :=
| match_globvar_intro : forall t init t' init' rd vo,
  transBeePL_type t = OK t' ->
  rel_type t t' ->
  transBeePL_init_datas_init_datas init = init' ->
  match_globvar (mkglobvar t init rd vo) (AST.mkglobvar t' init' rd vo).

(* Relates the function definition of BeePL and Csyntax *)
(* Fix me: Add external function rel later *)
Inductive match_function : BeePL.function -> Csyntax.function -> Prop :=
| match_fun : forall bf cf,
  transBeePL_function_function bf = OK cf ->
  match_function bf cf.

(* Relates the fundef of BeePL and Csyntax *)
(* Fix me: Add external function rel later *)
Inductive match_fundef : BeePL.fundef -> Csyntax.fundef -> Prop :=
| match_fundef_internal : forall f cf,
  transBeePL_fundef_fundef (Internal f) = OK (Ctypes.Internal cf) ->
  match_fundef (Internal f) (Ctypes.Internal cf).

(* Relates the global definitions of BeePL and Csyntax *) 
Inductive match_globdef : BeePL.globdef -> AST.globdef Csyntax.fundef Ctypes.type -> Prop :=
| match_gfun : forall f cf,
  match_fundef f cf ->
  match_globdef (Gfun f) (AST.Gfun cf)
| match_gvar : forall g cg,
  match_globvar g cg ->
  match_globdef (Gvar g) (AST.Gvar cg).

End specifications.

Section semantic_preservation.

Variable beePLprog : BeePL.program.

Variable cprog : Csyntax.program.

End semantic_preservation.



