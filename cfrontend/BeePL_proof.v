Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import compcert.common.Errors.

(***** Correctness proof for the Clight generation from BeePL using 
       composition of BeePL and CompCert compiler *****)

(***** Specification for types *****) 
Inductive rel_prim_type : BeeTypes.primitive_type -> Ctypes.type -> Prop :=
| rel_tunit : rel_prim_type Tunit (Ctypes.Tvoid)
| rel_tint : rel_prim_type Tint (Ctypes.Tint I32 Signed 
                                {| attr_volatile := false; attr_alignas := Some 4%N |})
| rel_tuint : rel_prim_type Tuint (Ctypes.Tint I32 Unsigned 
                                  {| attr_volatile := false; attr_alignas := Some 4%N |})
| rel_tbool : rel_prim_type Tbool (Ctypes.Tint I8 Unsigned {| attr_volatile := false; attr_alignas := Some 1%N |}).

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
Lemma type_translated: forall bt ct, 
transBeePL_type(bt) = ct ->
rel_type bt ct.
Proof.
Admitted.

(****** Proof for correctness of transformation of operators ******)
Lemma transl_notbool_cnotbool: forall v v' m t v'',
sem_unary_operation Notbool v = Some v' -> 
transBeePL_uop_uop Notbool = Cop.Onotbool ->
Cop.sem_unary_operation Cop.Onotbool (transBeePL_value_cvalue v) t m = Some v'' ->
v'' = transBeePL_value_cvalue v'.
Proof.
Admitted.

Lemma transl_notbool_cnotbool': forall v v' m t,
sem_unary_operation Notbool v = Some v' -> 
transBeePL_uop_uop Notbool = Cop.Onotbool ->
exists v'' : Values.val, Cop.sem_unary_operation Cop.Onotbool (transBeePL_value_cvalue v) t m = Some v'' 
/\ v'' = transBeePL_value_cvalue v'.
Proof.
Admitted.
     

Lemma transl_uop_cuop : forall op cop v v' m t,
sem_unary_operation op v = Some v' -> 
transBeePL_uop_uop op = cop ->
exists v'', Cop.sem_unary_operation cop (transBeePL_value_cvalue v) t m = Some v'' /\ 
v'' = (transBeePL_value_cvalue v').
Proof.
Admitted.


