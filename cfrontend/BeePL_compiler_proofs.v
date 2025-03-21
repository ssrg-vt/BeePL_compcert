Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Csem Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import Initializersproof Cstrategy BeePL_auxlemmas Coqlib Errors BeePL_values.

From mathcomp Require Import all_ssreflect. 

(***** Correctness proof for the Csyntax generation from BeePL using BeePL compiler *****)

Section specifications.

(* Simpler specification for expressions translations *) 
Inductive sim_bexpr_cexpr : vmap -> BeePL.expr -> Csyntax.expr -> Prop :=
| sim_val : forall le v t ct g g' i, 
            transBeePL_type t g = Res ct g' i->
            sim_bexpr_cexpr le (BeePL.Val v t) (Csyntax.Eval (transBeePL_value_cvalue v) ct)
(*| sim_valof : forall le e t ct ce g g' i,
              transBeePL_type t g = Res ct g' i ->
              sim_bexpr_cexpr le e ce ->
              sim_bexpr_cexpr le (BeePL.Valof e t) (Csyntax.Evalof ce ct)*)
| sim_var : forall (le:BeePL.vmap) (le':Csem.env) x t ct g g' i,
            transBeePL_type t g = Res ct g' i ->
            (forall le' id, if isSome (le ! id) 
                            then (forall l, le ! id = Some (l, t) /\ le' ! id = Some (l, ct)) 
                            else le ! id = None /\ le' ! id = None) ->
            sim_bexpr_cexpr le (BeePL.Var x t) (Csyntax.Evar x ct)
| sim_const_int : forall le i t ct g g' i',
                  transBeePL_type t g = Res ct g' i' ->
                  sim_bexpr_cexpr le (BeePL.Const (ConsInt i) t) (Csyntax.Eval (Values.Vint i) ct)
| sim_const_long : forall le i t ct g g' i',
                   transBeePL_type t g = Res ct g' i' ->
                   sim_bexpr_cexpr le (BeePL.Const (ConsLong i) t) (Csyntax.Eval (Values.Vlong i) ct)
| sim_const_unit : forall le cv ct g g' i', (* Fix me *)
                   transBeePL_value_cvalue Vunit = cv ->
                   transBeePL_type (Ptype Tunit) g = Res ct g' i' ->
                   sim_bexpr_cexpr le (BeePL.Const ConsUnit (Ptype Tunit)) (Csyntax.Eval cv ct)
| sim_prim_ref : forall le e t ct ce g g' i', 
                 transBeePL_type t g = Res ct g' i' ->
                 sim_bexpr_cexpr le e ce ->
                 sim_bexpr_cexpr le (BeePL.Prim Ref (e :: nil) t) (Csyntax.Eaddrof ce ct)
| sim_prim_deref : forall le e t ct ce g g' i',
                   transBeePL_type t g = Res ct g' i' ->
                   sim_bexpr_cexpr le e ce ->
                   sim_bexpr_cexpr le (BeePL.Prim Deref (e :: nil) t) (Csyntax.Ederef ce ct)
| sim_prim_massgn : forall le e1 e2 t ce1 ce2 ct g g' i,
                    transBeePL_type t g = Res ct g' i ->
                    sim_bexpr_cexpr le e1 ce1 ->
                    sim_bexpr_cexpr le e2 ce2 ->
                    sim_bexpr_cexpr le (BeePL.Prim Massgn (e1 :: e2 :: nil) t) (Csyntax.Eassign ce1 ce2 ct)
| sim_prim_uop : forall le o e1 t ct ce1 g g' i', 
                transBeePL_type t g = Res ct g' i' ->
                sim_bexpr_cexpr le e1 ce1 ->
                sim_bexpr_cexpr le (BeePL.Prim (Uop o) (e1 :: nil) t) (Csyntax.Eunop o ce1 ct)
| sim_prim_bop : forall le o e1 e2 t ct ce1 ce2 g g' i',
                 transBeePL_type t g = Res ct g' i' ->
                 sim_bexpr_cexpr le e1 ce1 ->
                 sim_bexpr_cexpr le e2 ce2 ->
                 sim_bexpr_cexpr le (BeePL.Prim (Bop o) (e1 :: e2 :: nil) t) (Csyntax.Ebinop o ce1 ce2 ct)
| sim_prim_run : forall le h t,
                 sim_bexpr_cexpr le (BeePL.Prim (Run h) nil t) (Eval (Values.Vundef) Tvoid) (* Fix me *)
| sim_bind : forall le x t e e' t' ct ct' ce ce' g g' g'' i i', (* Fix me *)
             transBeePL_type t g = Res ct g' i ->
             transBeePL_type t' g' = Res ct' g'' i' ->
             sim_bexpr_cexpr le e ce ->
             sim_bexpr_cexpr le e' ce' ->
             sim_bexpr_cexpr le (BeePL.Bind x t e e' t') (Csyntax.Ecomma (Eassign (Csyntax.Evar x ct) ce ct) ce' ct')
| sim_cond : forall le e1 e2 e3 t ct ce1 ce2 ce3 g g' i,
             transBeePL_type t g = Res ct g' i ->
             sim_bexpr_cexpr le e1 ce1 ->
             sim_bexpr_cexpr le e2 ce2 ->
             sim_bexpr_cexpr le e3 ce3 ->
             sim_bexpr_cexpr le (BeePL.Cond e1 e2 e3 t) (Csyntax.Econdition ce1 ce2 ce3 ct)
| sim_unit : forall le t ct g g' i', (* Fix me *)
             transBeePL_type t g = Res ct g' i' ->
             sim_bexpr_cexpr le (BeePL.Unit t) (Csyntax.Eval (transBeePL_value_cvalue Vunit) ct)
| sim_addr : forall le l ofs t ct g g' i',
             transBeePL_type t g = Res ct g' i' ->
             sim_bexpr_cexpr le (BeePL.Addr l ofs t) (Csyntax.Eloc l.(lname) ofs l.(lbitfield) ct)
| sim_hexpr : forall le h e t, (* Fix me *)
              sim_bexpr_cexpr le (BeePL.Hexpr h e t) (Eval (Values.Vundef) Tvoid).
 

(* Complete me *)  
Inductive sim_bexpr_cstmt : vmap -> BeePL.expr -> Csyntax.statement -> Prop :=
| sim_val_st : forall le v t ct cv g g' i',
               transBeePL_type t g = Res ct g' i' ->
               transBeePL_value_cvalue v = cv ->
               sim_bexpr_cstmt le (BeePL.Val v t) 
                                  (Csyntax.Sreturn (Some (Eval (transBeePL_value_cvalue v) ct)))
(*| sim_valof_st : forall le e t ct ce g g' i',
                 transBeePL_type t g = Res ct g' i' ->
                 sim_bexpr_cexpr le e ce ->
                 sim_bexpr_cstmt le (BeePL.Valof e t)
                                    (Csyntax.Sreturn (Some (Evalof ce ct)))*)
| sim_var_st : forall (le:BeePL.vmap) (le':Csem.env) x t ct g g' i',
                   transBeePL_type t g = Res ct g' i' ->
                  (forall le' id, if isSome (le ! id) 
                                  then (forall l, le ! id = Some (l, t) /\ le' ! id = Some (l, ct)) 
                                  else le ! id = None /\ le' ! id = None) ->
                sim_bexpr_cstmt le (BeePL.Var x t) (Csyntax.Sreturn (Some (Evalof (Csyntax.Evar x ct) ct)))
| sim_const_int_st : forall le i t ct g g' i',
                     transBeePL_type t g = Res ct g' i' ->
                     sim_bexpr_cstmt le (BeePL.Const (ConsInt i) t) 
                                        (Csyntax.Sreturn (Some (Evalof (Csyntax.Eval (Values.Vint i) ct) ct)))
| sim_const_long_st : forall le i t ct g g' i',
                      transBeePL_type t g = Res ct g' i' ->
                      sim_bexpr_cstmt le (BeePL.Const (ConsLong i) t) 
                                        (Csyntax.Sreturn (Some (Evalof (Csyntax.Eval (Values.Vlong i) ct) ct)))
| sim_const_uint_st : forall le cv ct g g' i',
                      transBeePL_value_cvalue Vunit = cv ->
                      transBeePL_type (Ptype Tunit) g = Res ct g' i' ->
                      sim_bexpr_cstmt le (BeePL.Const ConsUnit (Ptype Tunit))
                                        (Csyntax.Sreturn (Some (Evalof (Csyntax.Eval cv ct) ct)))
| sim_prim_ref_st : forall le e t ct ce g g' i', 
                    transBeePL_type t g = Res ct g' i' ->
                    sim_bexpr_cexpr le e ce ->
                    sim_bexpr_cstmt le (BeePL.Prim Ref (e :: nil) t) (Sdo (Csyntax.Eaddrof ce ct))
| sim_prim_deref_st : forall le e t ct ce g g' i',
                      transBeePL_type t g = Res ct g' i' ->
                      sim_bexpr_cexpr le e ce ->
                      sim_bexpr_cstmt le (BeePL.Prim Deref (e :: nil) t) (Sdo (Csyntax.Ederef ce ct))
| sim_prim_massgn_st : forall le e1 e2 t ce1 ce2 ct g g' i',
                       transBeePL_type t g = Res ct g' i' ->
                       sim_bexpr_cexpr le e1 ce1 ->
                       sim_bexpr_cexpr le e2 ce2 ->
                       sim_bexpr_cstmt le (BeePL.Prim Massgn (e1 :: e2 :: nil) t) (Sdo (Csyntax.Eassign ce1 ce2 ct))
| sim_prim_uop_st : forall le o e1 t ct ce1 g g' i', 
                    transBeePL_type t g = Res ct g' i' ->
                    sim_bexpr_cexpr le e1 ce1 ->
                    sim_bexpr_cstmt le (BeePL.Prim (Uop o) (e1 :: nil) t) (Sdo (Csyntax.Eunop o ce1 ct))
| sim_prim_bop_st : forall le o e1 e2 t ct ce1 ce2 g g' i',
                    transBeePL_type t g = Res ct g' i' ->
                    sim_bexpr_cexpr le e1 ce1 ->
                    sim_bexpr_cexpr le e2 ce2 ->
                    sim_bexpr_cstmt le (BeePL.Prim (Bop o) (e1 :: e2 :: nil) t) (Sdo (Csyntax.Ebinop o ce1 ce2 ct))
| sim_prim_run_st : forall le h t,
                    sim_bexpr_cstmt le (BeePL.Prim (Run h) nil t) (Sdo (Eval (Values.Vundef) Tvoid)) (* Fix me *)
| sim_bind_var_st : forall le x t e x' t' ct ct' ce ce' g g' i', 
                     transBeePL_type t g = Res ct g' i' ->
                     transBeePL_type t' = ret ct' ->
                     sim_bexpr_cexpr le e ce ->
                     sim_bexpr_cexpr le (Var x' t) ce' ->
                     sim_bexpr_cstmt le (BeePL.Bind x t e (Var x' t') t') 
                                        (Csyntax.Ssequence (Sdo (Eassign (Csyntax.Evar x ct) ce Tvoid)) (Csyntax.Sreturn (Some (Evalof ce' ct'))))
| sim_bind_const_st : forall le x t e c t' ct ct' ce ce' g g' g'' i' i'', 
                     transBeePL_type t g = Res ct g' i' ->
                     transBeePL_type t' g' = Res ct' g'' i'' ->
                     sim_bexpr_cexpr le e ce ->
                     sim_bexpr_cexpr le (Const c t') ce' ->
                     sim_bexpr_cstmt le (BeePL.Bind x t e (Const c t') t') 
                                        (Csyntax.Ssequence (Sdo (Eassign (Csyntax.Evar x ct) ce Tvoid)) (Csyntax.Sreturn (Some (Evalof ce' ct'))))
| sim_bind_st : forall le x t e e' t' ct ct' ce ce' g g' g'' i' i'', (* Fix me *)
                transBeePL_type t g = Res ct g' i' ->
                transBeePL_type t' g' = Res ct' g'' i'' ->
                sim_bexpr_cexpr le e ce ->
                sim_bexpr_cexpr le e' ce' ->
                sim_bexpr_cstmt le (BeePL.Bind x t e e' t') 
                                   (Csyntax.Ssequence (Sdo (Eassign (Csyntax.Evar x ct) ce Tvoid)) (Csyntax.Sreturn (Some (Evalof ce' ct'))))
| sim_cond_vars_st : forall le e1 e2 e3 t ct ce1 ce2 ce3 g g' i',
                     transBeePL_type t g = Res ct g' i' ->
                     sim_bexpr_cexpr le e1 ce1 ->
                     sim_bexpr_cexpr le e2 ce2 ->
                     sim_bexpr_cexpr le e3 ce3 ->
                     check_var_const e2 ->
                     check_var_const e3 ->
                     sim_bexpr_cstmt le (BeePL.Cond e1 e2 e3 t) 
                                        (Csyntax.Sifthenelse ce1 (Csyntax.Sreturn (Some (Evalof ce2 ct))) (Csyntax.Sreturn (Some (Evalof ce3 ct))))
| sim_cond_var1_st : forall le e1 e2 e3 t ct ce1 ce2 ce3,
                     transBeePL_type t = ret ct ->
                     sim_bexpr_cexpr le e1 ce1 ->
                     sim_bexpr_cexpr le e2 ce2 ->
                     sim_bexpr_cexpr le e3 ce3 ->
                     check_var_const e2 ->
                     sim_bexpr_cstmt le (BeePL.Cond e1 e2 e3 t) 
                                        (Csyntax.Sifthenelse ce1 (Csyntax.Sreturn (Some (Evalof ce2 ct))) (Csyntax.Sdo ce3))
| sim_cond_var2_st : forall le e1 e2 e3 t ct ce1 ce2 ce3,
                     transBeePL_type t = ret ct ->
                     sim_bexpr_cexpr le e1 ce1 ->
                     sim_bexpr_cexpr le e2 ce2 ->
                     sim_bexpr_cexpr le e3 ce3 ->
                     check_var_const e3 ->
                     sim_bexpr_cstmt le (BeePL.Cond e1 e2 e3 t) 
                                        (Csyntax.Sifthenelse ce1 (Csyntax.Sdo ce2) (Csyntax.Sreturn (Some (Evalof ce2 ct))))
| sim_cond_st : forall le e1 e2 e3 t ct ce1 ce2 ce3,
                transBeePL_type t = ret ct ->
                sim_bexpr_cexpr le e1 ce1 ->
                sim_bexpr_cexpr le e2 ce2 ->
                sim_bexpr_cexpr le e3 ce3 ->
                sim_bexpr_cstmt le (BeePL.Cond e1 e2 e3 t) 
                                   (Csyntax.Sifthenelse ce1 (Csyntax.Sdo ce2) (Csyntax.Sdo ce3))
| sim_unit_st : forall le t ct g g' i', (* Fix me *)
                transBeePL_type t g = Res ct g' i' ->
                sim_bexpr_cstmt le (BeePL.Unit t) (Csyntax.Sreturn (Some (Csyntax.Evalof (Csyntax.Eval (transBeePL_value_cvalue Vunit) ct) ct)))
| sim_addr_st : forall le l ofs t ct g g' i',
                transBeePL_type t g = Res ct g' i' ->
                sim_bexpr_cstmt le (BeePL.Addr l ofs t) (Csyntax.Sdo (Csyntax.Eloc l.(lname) ofs l.(lbitfield) ct))
| sim_hexpr_st : forall le h e t, (* Fix me *)
                 sim_bexpr_cstmt le (BeePL.Hexpr h e t) (Sdo (Eval (Values.Vundef) Tvoid)).


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
              length ts = length (from_typelist cts) ->
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
(forall bt ct g g' i, 
transBeePL_type bt g = Res ct g' i ->
rel_type bt ct) /\ 
(forall bts cts g g' i, 
transBeePL_types transBeePL_type bts g = Res cts g' i ->
rel_types bts cts).
Proof.
Admitted.

Lemma transBeePL_type_int : forall t g g' i sz s a,
transBeePL_type t g = Res (Ctypes.Tint sz s a) g' i ->
t = Ptype (Tint sz s a).
Proof.
move=> [].
+ move=> p g g' i sz s a /=. by case: p=> //= sz' s' a' [] h1 h2 h3 h4; subst.
+ by move=> h b a g g' i' sz a' a'' /=;case: b=> //= p; case: p=> //=.
move=> es e t g g' i sz s a /=. rewrite /SimplExpr.bind /=.
case hts: (transBeePL_types transBeePL_type es g)=> [errs | cts gs igs] //=.
by case ht: (transBeePL_type t gs)=> [er | ct1 g1 i1] //=.
Qed.

Lemma transBeePL_type_long : forall t g g' i s a,
transBeePL_type t g = Res (Ctypes.Tlong s a) g' i ->
t = Ptype (Tlong s a).
Proof.
move=> [].
+ move=> p g g' i s a /=. by case: p=> //= s' a' [] h1 h2 h3; subst.  
+ by move=> h b a g g' i' a' a'' /=;case: b=> //= p; case: p=> //=.
move=> es e t g g' i sz s /=. rewrite /SimplExpr.bind /=.
case hts: (transBeePL_types transBeePL_type es g)=> [errs | cts gs igs] //=.
by case ht: (transBeePL_type t gs)=> [er | ct1 g1 i1] //=.
Qed.

Lemma transBeePL_type_void : forall t g g' i,
transBeePL_type t g = Res Tvoid g' i ->
t = Ptype Tunit.
Proof.
move=> [].
+ by move=> p g g' i /=; case: p=> //=.
+ by move=> h b a g g' i /=; case: b=> //= p; case: p=> //=.
move=> es ef t g g' i /=. rewrite /SimplExpr.bind /=.
case hts: (transBeePL_types transBeePL_type es g)=> [errs | cts gs igs] //=.
by case ht: (transBeePL_type t gs)=> [er | ct1 g1 i1] //=.
Qed.

Lemma transBeePL_type_function : forall t ts t1 ct g g' i,
transBeePL_type t g = Res (Tfunction ts t1 ct) g' i ->
exists bts bef brt, t = Ftype bts bef brt. 
Proof.
move=> [].
+ by move=> p ts t1 ct g g' i /=; case: p=> //=.
+ by move=> h b a ts t1 ct g g' i' /=; case: b=> //=; move=> p; case: p=> //=.
move=> es ef t ts t1 ct g g' i /=. rewrite /SimplExpr.bind /=.
case hts: (transBeePL_types transBeePL_type es g)=> [errs | cts gs igs] //=.
case ht: (transBeePL_type t gs)=> [er | ct1 g1 i1] //=. move=> [] h1 h2 h3 h4; subst.
exists es. exists ef. by exists t.
Qed.

Lemma transBeePL_type_ref : forall t t' a' g g' i,
transBeePL_type t g = Res (Tpointer t' a') g' i ->
exists h bt a, t = Reftype h bt a. 
Proof.
move=> [].
+ by move=> p t' a' g g' i; case: p=> //=.
+ move=> h b a t' a' g g' i' /=; case: b=> //= p; case: p=> //=.
  + move=> [] h1 h2 h3; subst. exists h. exists (Bprim Tunit). by exists a'.
  + move=> sz s a'' [] h1 h2 h3; subst. exists h. exists (Bprim (Tint sz s a'')). by exists a'.
  move=> s a'' [] h1 h2 h3; subst. exists h. exists (Bprim (Tlong s a'')). by exists a'.
move=> es e t t' a' g g' i /=. rewrite /SimplExpr.bind /=.
case hts: (transBeePL_types transBeePL_type es g)=> [errs | cts gs igs] //=.
by case ht: (transBeePL_type t gs)=> [er | ct1 g1 i1] //=.
Qed.

(*** Complete Me ***)
(*** Write more such lemmas for all available BeePL and C types ***)

Lemma no_btype_to_float : forall t g f a g' i,
transBeePL_type t g <> Res (Tfloat f a) g' i.
Proof.
move=> t g f a g' i /=. case: t=> //=.
+ by move=> p; case: p=> //=.
+ by move=> h b a';case: b=> //= p;case: p=> //=.
move=> es ef t. rewrite /SimplExpr.bind /=.
case hts: (transBeePL_types transBeePL_type es g)=> [errs | cts gs igs] //=.
by case ht: (transBeePL_type t gs)=> [er | ct1 g1 i1] //=.
Qed.

Lemma no_btype_to_array : forall t t' z a g g' i,
transBeePL_type t g <> Res (Tarray t' z a) g' i.
Proof.
move=> t t' z a g g' i /=. case: t=> //=.
+ by move=> p; case: p=> //=.
+ by move=> h b a';case: b=> //= p;case: p=> //=.
move=> es ef t. rewrite /SimplExpr.bind /=.
case hts: (transBeePL_types transBeePL_type es g)=> [errs | cts gs igs] //=.
by case ht: (transBeePL_type t gs)=> [er | ct1 g1 i1] //=.
Qed.

(* not valid once we add struct data type in BeePL *)
Lemma no_btype_to_struct : forall t s a g g' i,
transBeePL_type t g <> Res (Tstruct s a) g' i.
Proof.
move=> t s a g g' i /=. case: t=> //=.
+ by move=> p; case: p=> //=.
+ by move=> h b a';case: b=> //= p;case: p=> //=.
move=> es ef t. rewrite /SimplExpr.bind /=.
case hts: (transBeePL_types transBeePL_type es g)=> [errs | cts gs igs] //=.
by case ht: (transBeePL_type t gs)=> [er | ct1 g1 i1] //=.
Qed.

Lemma no_btype_to_union : forall t s a g g' i,
transBeePL_type t g <> Res (Tunion s a) g' i.
Proof.
move=> t s a g g' i /=. case: t=> //=.
+ by move=> p; case: p=> //=.
+ by move=> h b a';case: b=> //= p;case: p=> //=.
move=> es ef t. rewrite /SimplExpr.bind /=.
case hts: (transBeePL_types transBeePL_type es g)=> [errs | cts gs igs] //=.
by case ht: (transBeePL_type t gs)=> [er | ct1 g1 i1] //=.
Qed.


(*** Complete Me ***)
(*** Write more such lemmas for all available C types that are not allowed in BeePL ***)

(***** End of Proof for correctness of type transformation *****)


Lemma tranBeePL_expr_expr_spec: forall vm e ce g g' i,
transBeePL_expr_expr e g = Res ce g' i ->
sim_bexpr_cexpr vm e ce.
Proof.
move=> vm e ce ht. elim: e ht=> //=.
Admitted.

Lemma tranBeePL_expr_stmt_spec: forall vm e ce g g' i,
transBeePL_expr_st e g = Res ce g' i ->
sim_bexpr_cstmt vm e ce.
Proof.
Admitted.

(* Relates global variables of BeePL and Csyntax *)
Inductive match_globvar : BeePL.globvar type -> AST.globvar Ctypes.type -> Prop :=
| match_globvar_intro : forall t init t' init' rd vo g g' i,
  transBeePL_type t g = Res t' g' i ->
  rel_type t t' ->
  match_globvar (mkglobvar t init rd vo) (AST.mkglobvar t' init' rd vo).

(* Relates the function definition of BeePL and Csyntax *)
Inductive match_function : BeePL.function -> Csyntax.function -> Prop :=
| match_fun : forall vm bf cf,
  transBeePL_type (BeePL.fn_return bf) = ret (Csyntax.fn_return cf) ->
  BeePL.fn_callconv bf = Csyntax.fn_callconv cf ->
  unzip1 (BeePL.fn_args bf) = unzip1 (Csyntax.fn_params cf) ->
  transBeePL_types transBeePL_type (unzip2 (BeePL.fn_args bf)) = 
  ret (to_typelist (unzip2 (Csyntax.fn_params cf))) ->
  unzip1 (BeePL.fn_vars bf) = unzip1 (Csyntax.fn_vars cf) ->
  transBeePL_types transBeePL_type (unzip2 (BeePL.fn_vars bf)) = 
  ret (to_typelist (unzip2 (Csyntax.fn_vars cf))) ->
  sim_bexpr_cstmt vm (BeePL.fn_body bf) (Csyntax.fn_body cf) ->
  match_function bf cf.

Lemma tranBeePL_function_spec: forall bf cf,
transBeePL_function_function bf = OK cf ->
match_function bf cf.
Proof.
Admitted.

(* Relates the fundef of BeePL and Csyntax *)
(* Fix me: Add external function rel later *) 
Inductive match_fundef : BeePL.fundef -> Csyntax.fundef -> Prop :=
| match_fundef_internal : forall f cf,
  match_function f cf -> 
  match_fundef (Internal f) (Ctypes.Internal cf)
| match_fundef_external : forall ef cef ts cts t ct cc gs gs' i'' g g' i' gf gf' if',
  transBeePL_types transBeePL_type ts gs = Res cts gs' i'' ->
  transBeePL_type t g = Res ct g' i' ->
  befunction_to_cefunction ef gf = Res cef gf' if' ->
  match_fundef (External ef ts t cc) (Ctypes.External cef cts ct cc).

Lemma transBeePL_fundef_spec : forall f cf, 
transBeePL_fundef_fundef (Internal f) = OK (Ctypes.Internal cf) ->
match_fundef (Internal f) (Ctypes.Internal cf).
Proof.
rewrite /transBeePL_fundef_fundef /= /transBeePL_function_function /=. 
move=> f cf h. monadInv h. move: EQ.
case ht: (transBeePL_type (BeePL.fn_return f) (initial_generator tt))=> [er | r g i]//=. 
case hts : (transBeePL_types transBeePL_type (BeePL_aux.unzip2 (fn_args f))
      (initial_generator tt))=> [er' | r' g' i'] //=.
case hts' : (transBeePL_types transBeePL_type (BeePL_aux.unzip2 (BeePL.fn_vars f)) (initial_generator tt))=> [er1 | r1 g1 i1] //=.
case hes : (transBeePL_expr_st (BeePL.fn_body f) (initial_generator tt))=> [er2 | r2 g2 i2] //=.
move=> [] <- /=.
apply match_fundef_internal; rewrite /=; auto. 
apply tranBeePL_function_spec; auto.
by rewrite /transBeePL_function_function /= ht hts hts' hes /=. 
Qed.

(* Relates the global definitions of BeePL and Csyntax *) 
Inductive match_globdef : BeePL.globdef BeePL.fundef type -> AST.globdef Csyntax.fundef Ctypes.type -> Prop :=
| match_gfun : forall f cf,
  match_fundef f cf ->
  match_globdef (AST.Gfun f) (AST.Gfun cf)
| match_gvar : forall g cg,
  match_globvar g cg ->
  match_globdef (Gvar g) (AST.Gvar cg).

Definition match_ident_globdef (igd1 : ident * BeePL.globdef BeePL.fundef type) 
  (igd2 : ident *  AST.globdef Csyntax.fundef Ctypes.type) : Prop :=
fst igd1 = fst igd2 /\ match_globdef (snd igd1) (snd igd2).

Definition match_program_gen (p1 : BeePL.program) (p2 : Csyntax.program) : Prop :=
  list_forall2 (match_ident_globdef) p1.(prog_defs) p2.(AST.prog_defs)
  /\ p2.(AST.prog_main) = p1.(prog_main)
  /\ p2.(AST.prog_public) = p1.(prog_public).

Definition match_prog (p1: BeePL.program) (p2: Csyntax.program) :=
    match_program_gen p1 p2
 /\ prog_types p1 = Ctypes.prog_types p2. 

Lemma transf_program_match:
forall p cp, BeePL_compcert p = OK cp -> match_prog p cp.
Proof.
rewrite /BeePL_compcert /=. move=> p cp H. monadInv H.
split; auto; rewrite /match_program_gen /=; split; auto.
move: x EQ. elim: (prog_defs p)=> //=.
(* nil *)
+ move=> xs [] eq /=; subst. by apply list_forall2_nil.
(* cons *)
move=> [] id gd gds ih /= xs h. monadInv h.
move: (ih x0 EQ1)=> hl. apply list_forall2_cons; auto.
rewrite /match_ident_globdef /=; split; auto.
rewrite /transBeePL_globdef_globdef in EQ. case: gd EQ=> //=.
+ move=> fd h. monadInv h. apply match_gfun. rewrite /transBeePL_fundef_fundef in EQ.
  case: fd EQ=> //= f h. monadInv h. apply match_fundef_internal.
  by apply tranBeePL_function_spec.
+ move=> t cc. case hef: (befunction_to_cefunction f (initial_generator tt))=> [er | cef g1 i1] //=.
  case hts: (transBeePL_types transBeePL_type h (initial_generator tt))=> [er1 | cts g3 i3] //=.
  case ht: (transBeePL_type t (initial_generator tt))=> [er2 | ct g4 i4] //=.
  move=> [] heq; subst. by apply match_fundef_external with (initial_generator tt) g3 i3 
  (initial_generator tt) g4 i4 (initial_generator tt) g1 i1; auto. 
move=> gv h. monadInv h. apply match_gvar. case: gv EQ=> //= gi i r v.
case: x1=> //= gi' i' r' v'. rewrite /transBeePLglobvar_globvar /=. move=> h.
move: h. case ht: (transBeePL_type gi (initial_generator tt))=> [er | r1 g1 i1] //=.
move=> [] h1 h2 h3 h4; subst. apply match_globvar_intro with (initial_generator tt) g1 i1; auto.
have [h1 h2] := type_translated. by move: (h1 gi gi' (initial_generator tt) g1 i1 ht).
Qed.

(* Relation between BeePL vmap and Csyntax local env *)
Record match_env (vm : BeePL.vmap) (cvm : env) : Prop :=
mk_match_env {
 local_match: forall id b t ct g g' i,
              vm!id = Some (b, t) ->
              transBeePL_type t g = Res ct g' i ->
              cvm!id = Some (b, ct);
 global_match: forall id,
               vm!id = None ->
               cvm!id = None }.

End specifications.

Section semantic_preservation.

Variable bprog : BeePL.program.

Variable cprog : Csyntax.program.

Hypothesis TRANSBPL: match_prog bprog cprog.

Let bge := BeePL.globalenv bprog.

Let cge := Csem.globalenv cprog.

Variable benv : BeePL.vmap.

Variable cenv : Csem.env.

(* Preservation of composite env *) 
Lemma comp_env_preserved :
Csem.genv_cenv cge = BeePL.genv_cenv bge. 
Proof.
rewrite /=. case: TRANSBPL=> //= h1 h2.
have /= := prog_comp_env_eq bprog. rewrite h2 /=.
generalize (prog_comp_env_eq bprog) (compcert.cfrontend.Ctypes.prog_comp_env_eq cprog). 
congruence.
Qed.

(* Complete Me *)
(* Preservation of symbols *) 
Lemma symbols_preserved : forall (id : ident), 
Genv.find_symbol (Csem.genv_genv cge) id = Genv.find_symbol bge id.
Proof.
Admitted.

(* Complete Me *)
(* Preservation of symbol env *)
Lemma senv_preserved : Senv.equiv bge (Csem.genv_genv cge).
Proof.
Admitted.

(* Equivalence between vmaps benv and cenv *)
Lemma equiv_global_benv_cenv : forall vi, 
match_env benv cenv ->
benv ! vi = None ->
cenv ! vi = None.
Proof.
move=> vi h hm. case hb: (cenv ! vi)=> [ [l t] | ] //=.
case h=> //= h' h''. move: (h'' vi hm)=> hc. by rewrite hc in hb.
Qed.

Lemma equiv_local_benv_cenv : forall vi l t ct g g' i, 
match_env benv cenv ->
transBeePL_type t g = Res ct g' i ->
benv ! vi = Some (l, t) ->
cenv ! vi = Some (l, ct).
Proof.
move=> vi l t ct g g' i h ht hm. 
case h=> //= h' h''. by move: (h' vi l t ct g g' i hm ht). 
Qed.

(* Complete Me *)
(* Preservation of function ptr *) 
Lemma function_ptr_translated : forall v f,
Genv.find_funct_ptr bge v = Some f ->
exists tf, Genv.find_funct_ptr (Csem.genv_genv cge) v = Some tf /\ match_fundef f tf. 
Proof.
Admitted.

(* Complete Me *)
(* Preservation of function *)
Lemma functions_translated: forall v f,
Genv.find_funct bge v = Some f ->
exists tf, Genv.find_funct (Csem.genv_genv cge) v = Some tf /\ match_fundef f tf.
Proof.
Admitted.

(* Complete me *)
(* Preservation of function returns *)
Lemma function_return_preserved : forall f tf g g' i,
match_function f tf ->
transBeePL_type (BeePL.fn_return f) g = Res (Csyntax.fn_return tf) g' i.
Proof.
Admitted.

(* Preservation of deref_addr between BeePL and Csyntax *) 
Lemma deref_addr_translated:  forall ty m addr ofs bf v cty cv g g' i,
deref_addr bge ty m addr ofs bf v ->
transBeePL_type ty g = Res cty g' i ->
transBeePL_value_cvalue v = cv ->
match chunk_for_volatile_type cty bf with 
| None => Csem.deref_loc cge cty m addr ofs bf Events.E0 cv
| Some chunk => exists tr, bf = Full /\ 
                Events.volatile_load (Csem.genv_genv cge) chunk m addr ofs tr cv
end.
Proof.
move=> ty m addr ofs bf v cty cv g g' i hd ht hv. 
rewrite /chunk_for_volatile_type /=. inversion hd; subst.
(* by value *)
+ have hcty := non_volatile_type_preserved ty cty g g' i false H0 ht. rewrite hcty /=.
  apply Csem.deref_loc_value with (transl_bchunk_cchunk chunk); auto.
  + by have := BeePL_auxlemmas.access_mode_preserved ty cty (By_value (transl_bchunk_cchunk chunk)) 
               g g' i H ht.
  rewrite /transBeePL_value_cvalue in H1. by have -> := bv_cv_reflex v0 v H2. 
(* by value, volatile *)
+ have -> /= := non_volatile_type_preserved ty cty g g' i true H0 ht. 
  have -> /= := access_mode_preserved ty cty (By_value (transl_bchunk_cchunk chunk)) g g' i H ht.
  exists tr. split=> //=. have -> := bv_cv_reflex v0 v H2. have hequiv := senv_preserved. 
  rewrite /Csem.genv_genv /= in hequiv.
  by have := @Events.volatile_load_preserved bge (Genv.globalenv cprog) (transl_bchunk_cchunk chunk)
           m addr ofs tr v0 hequiv H1.
(* by reference *)
have h /= := BeePL_auxlemmas.access_mode_preserved ty cty By_reference g g' i H ht. 
case: ifP=> //= hc. 
+ rewrite h /=. by apply Csem.deref_loc_reference.
by apply Csem.deref_loc_reference.
Qed.

(* Complete Me *)
(* Preservation of assign_addr between BeePL and Csyntax *)
Lemma assign_addr_translated: forall ty m addr ofs bf v m' cty cv v' cv' g g' i,
assign_addr bge ty m addr ofs bf v m' v' ->
transBeePL_type ty g = Res cty g' i ->
transBeePL_value_cvalue v = cv ->
transBeePL_value_cvalue v' = cv' ->
match chunk_for_volatile_type cty bf with 
| None => Csem.assign_loc cge cty m addr ofs bf cv Events.E0 m' cv
| Some chunk => exists tr, bf = Full /\ 
                Events.volatile_store (Csem.genv_genv cge) chunk m addr ofs cv tr m'
end.
Admitted.

(* Big step semantics with rvalue *) 
(* If an expression evaluates to a value then in the c semantics if the expression is 
   evaluated in RV position then it should also produce the same value 
   If an expression evaluates to a value then in the c semantics if the expression is 
   evaluated in LV position then it should produce a location (deref, var)*)
Lemma bsem_cexpr_lsimple : forall m e l ofs ce g g' i, 
bsem_expr_slv bge benv m e l ofs ->
transBeePL_expr_expr e g = Res ce g' i ->
match_env benv cenv ->
eval_simple_lvalue cge cenv m ce l.(lname) ofs l.(lbitfield). 
Proof.
move=> m e l ofs ce g g' i hl /= hte henv. induction hl => //=.
(* lvar *)
+ rewrite /transBeePL_expr_expr /SimplExpr.bind in hte. 
  case htt: (transBeePL_type t g) hte=> [er | r g'' i'] //=.
  move=> [] h1 h2; subst. 
  apply esl_var_local. by have := equiv_local_benv_cenv x l (Reftype h t' a) r g g' i' henv htt H.
(* gvar *)
+ rewrite /transBeePL_expr_expr /SimplExpr.bind in hte. 
  case hte': (transBeePL_type t g) hte=> [er | r g'' i'] //=.
  move=> [] h1 h2; subst.
  apply esl_var_global.
  + by have := equiv_global_benv_cenv x henv H. 
  by have := symbols_preserved x=> ->. 
(* Loc *) 
rewrite /transBeePL_expr_expr /SimplExpr.bind in hte. 
case ht: (transBeePL_type t g) hte=> [er | r g'' i'] //=.
move=> [] h1 h2; subst. by apply esl_loc.
Qed.

Lemma bsem_cexpr_rsimple : forall m e v ce g g' i, 
bsem_expr_srv bge benv m e v ->
transBeePL_expr_expr e g = Res ce g' i ->
match_env benv cenv ->
eval_simple_rvalue cge cenv m ce (transBeePL_value_cvalue v).
Proof.
move=> m e v ce g g' i hr. move: ce g g' i. induction hr=> //=.
(* val *)
+ move=> ce g g' i ht henv /=. 
  rewrite /SimplExpr.bind in ht. 
  case ht: (transBeePL_type t g) ht=> [er | r g'' i'] //=.
  move=> [] h1 h2; subst. by apply esr_val. 
(* deref *)
+ move=> ce g g' i' hte henv /=.
  rewrite /transBeePL_expr_exprs /SimplExpr.bind in hte.
  case he1:(transBeePL_expr_expr e g) hte=> [er | r g'' i''] //=.
  case he2: (transBeePL_type t g'')=> [er1 | r1 g1 i1] //=.
  move=> [] h1 h2; subst. apply esr_rvalof with l.(lname) ofs l.(lbitfield).
    + by have := bsem_cexpr_lsimple hm e l ofs r g g'' i'' H he1 henv.
    + have h := transBeePL_expr_expr_type_equiv e r g g'' i'' he1. 
      by have := type_preserved_generator (typeof_expr e) r1 (Csyntax.typeof r) g'' g' g g'' i1 i''
              i1 i'' he2 h. 
    + by have := non_volatile_type_preserved (typeof_expr e) r1 g'' g' i1 false H2 he2. 
   have := deref_addr_translated (typeof_expr e) hm l.(lname) ofs l.(lbitfield) v r1
           (transBeePL_value_cvalue v) g'' g' i1 H0 he2 refl_equal. 
   have hc := non_volatile_type_preserved (typeof_expr e) r1 g'' g' i1 false H2 he2.
   by rewrite /chunk_for_volatile_type /= hc /=. 
(* uop *)
+ move=> ce g1 g2 i1 /= hte /= henv.
  rewrite /transBeePL_expr_exprs /SimplExpr.bind in hte. 
  case he1: (transBeePL_expr_expr e g1) hte=> [er | r1 g1' i1'] //=.
  case ht1: (transBeePL_type t g1')=> [er' | r2 g2' i2'] //=.
  move=> [] h1 h2; subst; rewrite /=. rewrite /exprlist_list_expr /=. 
  apply esr_unop with (transBeePL_value_cvalue v).
  + by move: (IHhr r1 g1 g1' i1' he1 henv).
  have heq := bv_cv_reflex v' v'' H2; subst.
  have ht' := transBeePL_expr_expr_type_equiv e r1 g1 g1' i1' he1.
  have heq1 := type_preserved_generator (typeof_expr e) (Csyntax.typeof r1) r2 
               g1 g1' g1' g2 i1' i2' i1' i2' ht' ht1.
  rewrite -heq1 in ht1.
  by have heq' := type_preserved_generator (typeof_expr e) (Csyntax.typeof r1) ct g1' g2 g g' i2' i
          i2' i ht1 H; subst.
(* Bop *)
+ move=> ce g1 g2 i1 /= hte henv. rewrite /SimplExpr.bind in hte. 
  case hte1 : (transBeePL_expr_expr e1 g1) hte=> [er1 | re1 ge1 ie1] //=.
  case hte2 : (transBeePL_expr_expr e2 ge1)=> [er2 | re2 ge2 ie2] //=.
  case ht : (transBeePL_type t ge2)=> [ert | rt gt it] //=.
  move=> [] h1 h2; subst. rewrite /exprlist_list_expr /=. 
  apply esr_binop with (transBeePL_value_cvalue v1) (transBeePL_value_cvalue v2).
  + by move: (IHhr1 re1 g1 ge1 ie1 hte1 henv).
  + by move: (IHhr2 re2 ge1 ge2 ie2 hte2 henv).
  have hv1 := bv_cv_reflex v v' H3.
  have ht1' := transBeePL_expr_expr_type_equiv e1 re1 g1 ge1 ie1 hte1. case: H1=> [] h1 h2; subst.
  have heq := type_preserved_generator (typeof_expr e1) ct1 rt g g' ge2 g2 i it i it H ht; subst.
  have heq' := type_preserved_generator (typeof_expr e1) (Csyntax.typeof re1) rt g1 ge1 ge2 g2 ie1
               it ie1 it ht1' ht; subst.
  have ht2' := transBeePL_expr_expr_type_equiv e2 re2 ge1 ge2 ie2 hte2. 
  have heq'' := type_preserved_generator (typeof_expr e2) ct2 (Csyntax.typeof re2) g' g'' ge1 ge2 
                i' ie2 i' ie2 H0 ht2'; subst. by have -> := comp_env_preserved.
(* Unit *)
move=> ce g g' i /=. rewrite /SimplExpr.bind /=.
move=> [] h1 h2 henv /=; subst. by apply esr_val.
Qed.

(* A final state does not step forward *)
Lemma final_state_no_step : forall s s',
BeePL.final_state s ->
~ (bstep bge s s').
Proof.
move=> s s'. elim: s=> //=.
+ move=> f e k vm m hf. by inversion hf.
+ move=> fd args k m hf. by inversion hf.
+ move=> res m hf. move=> h. by inversion h.
move=> hf. by inversion hf.
Qed.

Lemma decompose_expr: forall f e k m,
BeePL.safe bge (BeePL.ExprState f e k benv m) -> 
is_simple_expr e \/ exists S, bstep bge (BeePL.ExprState f e k benv m) S.
Proof.
move=> f e. move: f. elim: e=> //=.
(* val *)
+ move=> v t f k m hs. by left.
(* var *)
+ move=> v f k m hs. by left.
(* const *)
+ move=> c t f k m hs. by left.
(* app *)
+ move=> e hi es t f k m hs. right.
  inversion hs; subst.
  + by inversion H.
  move: H. move=> [] s' he. by exists s'.
(* builtin *)
+ move=> [] /=.
  (* ref *)
  + move=> [] //=.
    + move=> t f k m he. inversion he; subst. + by inversion H.
      move: H. move=> [] s' href. inversion href; subst. by inversion H5.
    move=> e es t f k m hs. elim: es hs=> //=.
    + move=> hs. rewrite /BeePL.safe in hs. inversion hs.
      + by inversion H.
      move: H. move=> [] s' href. right. by exists s'.
    move=> e' es hi hs. rewrite /BeePL.safe in hs.
    inversion hs; subst.
    + by inversion H.
    move: H. move=> [] s' he. inversion he; subst. by inversion H5.
  (* deref *)
  + move=> [] //=.
    + move=> t f k m hs. rewrite /BeePL.safe in hs.
      inversion hs; subst.
      + by inversion H.
      move: H. move=> [] s' he. inversion he; subst. by inversion H5.
    move=> e es t f k m hs. elim: es hs=> //=.
    + move=> hs. rewrite /BeePL.safe in hs. inversion hs; subst.
      + by inversion H.
      move: H. move=> [] s' he. right. by exists s'.
    move=> e' es hi hs. rewrite /BeePL.safe in hs.
    inversion hs; subst.
    + by inversion H.
    move: H. move=> [] s' he. inversion he; subst. by inversion H5.
  (* massgn *)
  + move=> [] //=.
    + move=> t f k m hs. inversion hs; subst.
      + by inversion H.
      move: H. move=> [] s' he. inversion he; subst. by inversion H5.
    move=> e es t f k m hs. elim: es hs=> //=.
    + move=> hs. rewrite /BeePL.safe in hs. inversion hs; subst.
      + by inversion H.
      move: H. move=> [] s' he. right. by exists s'.
    move=> e' es hi hs. rewrite /BeePL.safe in hs.
    inversion hs; subst.
    + by inversion H.
    move: H. move=> [] s' he. inversion he; subst. by inversion H5.
    right. exists (BeePL.ExprState f (Val v' (typeof_expr e)) k benv m').
    by apply step_prim_massgn with ct1 ct2 l ofs v g1 g2 g3 i i'.
  (* unary *)
  + move=> u [] //=.
    + move=> t f k m hs. inversion hs; subst.
      + by inversion H. move: H. move=> [] s' he. inversion he; subst. by inversion H5.
    move=> e es t f k m hs. elim: es hs=> //=.
    + move=> hs. inversion hs; subst.
      + by inversion H.
      move: H. move=> [] s' he. right. by exists s'.
    move=> e' es hi hs. rewrite /BeePL.safe in hs.
    inversion hs; subst.
    + by inversion H.
    move: H. move=> [] s' he. inversion he; subst. by inversion H5.
  (* binary *)
  + move=> b [] //=.
    + move=> t f k m hs. inversion hs; subst.
      + by inversion H. move: H. move=> [] s' he. inversion he; subst. by inversion H5.
    move=> e es t f k m hs. elim: es hs=> //=.
    + move=> hs. inversion hs; subst.
      + by inversion H.
      move: H. move=> [] s' he. right. by exists s'.
    move=> e' es hi hs. rewrite /BeePL.safe in hs.
    inversion hs; subst.
    + by inversion H.
    move: H. move=> [] s' he. inversion he; subst. inversion H5; subst.
    right. exists (BeePL.ExprState f (Val v (typeof_expr (Prim (Bop b) [:: e; e'] t))) k benv m).
    apply BeePL.step_expr; auto. 
  (* run *) (* fix me *)
  move=> m es t f k m' hs. inversion hs; subst.
  + by inversion H.
  move: H. move=> [] s' H. inversion H; subst. by inversion H6.
(* bind *)
+ move=> i t e hi e' hi' t' f k m hs. inversion hs; subst.
  + by inversion H.
  move: H. move=> [] s' he. right. by exists s'.
(* cond *)
+ move=> e hi e1 hi1 e2 hi2 t f k m hs. inversion hs; subst.
  + by inversion H.
  move: H. move=> [] s' H. right. by exists s'.
(* unit *)
+ move=> t f k m hs. by left.
(* addr *)
+ move=> l i f k m hs. by left.
(* hexpr *) (* fix me *)
+ move=> m e hi t f k m' hs. inversion hs; subst.
  + by inversion H.
  move: H. move=> [] s' he. right. by exists s'.
(* eapp *)
move=> e ts es t f k m hs. inversion hs; subst.
+ by inversion H.
move: H. move=> [] s' he. right. by exists s'.
Qed.
  
(* Progress for expression state: A safe expression state always make progress except the val *)
(* Need to add well formedness about store *)
Lemma expr_state_can_step: forall f e k m,
BeePL.safe bge (BeePL.ExprState f e k benv m) ->
exists S, bstep bge (BeePL.ExprState f e k benv m) S.
Proof.
move=> f e k m hs. move: f k benv m hs. elim: e=> //=.
(* Val *)
+ move=> v t f k benv' m hs. inversion hs; subst.
  + by inversion H.
  move: H. move=> [] s' he. by exists s'. 
(* Var *)
+ admit.
(* Const *)
Admitted.  

Lemma safe_steps: forall s s',
BeePL.safe bge s -> 
bstep bge s s' -> 
BeePL.safe bge s'.
Proof.
move=> s. elim: s=> //=.
Admitted.

Lemma bsem_expr_srv_safe: forall C e v m k f,
bsem_expr_srv bge benv m e v ->
BeePL.leftcontext RV RV C -> 
BeePL.safe bge (BeePL.ExprState f (C e) k benv m) ->
BeePL.safe bge (BeePL.ExprState f (C (Val v (typeof_expr e))) k benv m).
Proof.
Admitted.

(*Lemma simple_can_eval:
  forall e from C,
  simple e = true -> leftcontext from RV C -> safe (BeePL.ExprState f (C e) k benv m) ->
  match from with
  | LV => exists b ofs bf, eval_simple_lvalue e m a b ofs bf
  | RV => exists v, eval_simple_rvalue e m a v
  end.
Proof.*)

Lemma bsem_cexpr_list :
forall m es tes vs cts ces g g' i, 
bsem_expr_srvs bge benv m es vs ->
transBeePL_expr_exprs transBeePL_expr_expr es g = Res ces g' i ->
typeof_exprs es = tes ->
transBeePL_types transBeePL_type tes g = Res cts g' i ->
match_env benv cenv ->
eval_simple_list cge cenv m ces cts (transBeePL_values_cvalues vs).
Proof.
Admitted.

(* Complete Me *)
(* Preservation of allocation of variables between BeePL and Csyntax *)
Lemma alloc_variables_preserved: forall m m' benv' vrs cvrs cvrs' cvrs'' cts g g' i,
BeePL.alloc_variables benv m vrs benv' m' ->
unzip1 vrs = cvrs ->
unzip2 vrs = cvrs' ->
transBeePL_types transBeePL_type cvrs' g = Res cvrs'' g' i ->
from_typelist cvrs'' = cts ->
exists cenv', Csem.alloc_variables cge cenv m (zip cvrs cts) cenv' m'.
Proof.
Admitted.

(* Complete Me *)
(* Preservation of bind parameters between BeePL and Csyntax *)
Lemma bind_variables_preserved: forall m m' benv' vrs cvrs cvrs' cvrs'' cts g g' i,
BeePL.bind_variables bge benv m vrs benv' m' ->
unzip1 vrs = cvrs ->
unzip2 vrs = cvrs' ->
transBeePL_types transBeePL_type cvrs' g = Res cvrs'' g' i ->
from_typelist cvrs'' = cts ->
exists cenv', Csem.bind_parameters cge cenv m (zip cvrs cts) cenv' m'.
Proof.
Admitted.

(* Preservation of semantics of expressions in BeePL and expressions in Csyntax *) 
(* Refer: sstep_simulation in SimplExprproof.v *)
(* Equivalence between left reduction top level *)
Lemma equiv_lreduction : forall e m e' m' ce g g' i', 
lreduction bge benv e m e' m' ->
transBeePL_expr_expr e g = Res ce g' i' ->
match_env benv cenv ->
exists ce', Csem.lred cge cenv ce m ce' m' /\ sim_bexpr_cexpr benv e' ce'.
Proof.
move=> e m e' m' ce g g' i' hl. induction hl. 
(* local var *)
+ move=> /= he henv. 
  rewrite /SimplExpr.bind in he.
  case ht: (transBeePL_type t g) he=> [er | r g'' i''] //=.
  move=> [] h1 h2; subst. case: henv=> [hm1 hm2]; subst.
  move: (hm1 x l (Reftype h (Bprim t') a) r g g' i'' H ht)=> H'.
  exists (Eloc l Ptrofs.zero Full r). split=> //=.
  + by apply Csem.red_var_local.
  apply sim_addr with g g' i''; rewrite /=. by case: t' H ht=> //=.
(* global var *)
move=> /= he henv. 
rewrite /SimplExpr.bind in he.
case ht: (transBeePL_type t g) he=> [er | r g'' i''] //=.
move=> [] h1 h2; subst. case: henv=> [hm1 hm2]; subst. 
move: (hm2 x H)=> H'.
exists (Eloc l Ptrofs.zero Full r). split=> //=.
+ apply Csem.red_var_global.
  + by apply H'.
  by have := symbols_preserved x=> ->. 
by apply sim_addr with g g' i''; rewrite /=.
Qed. 

(* Equivalence between right reduction top level *)
Lemma equiv_rreduction : forall e m e' m' ce g g' i',
rreduction bge benv e m e' m' ->
transBeePL_expr_expr e g = Res ce g' i' ->
exists ce' t, Csem.rred cge ce m t ce' m' /\ sim_bexpr_cexpr benv e' ce'.
Proof.
move=> e m e' m' ce g g' i' hr. induction hr; subst; rewrite /=.
(* deref *)
+ (*move=> hr. rewrite /SimplExpr.bind in hr.
  case hte: (transBeePL_type (typeof_expr e) g) hr=> [ere | cte ge ie] //=.
  case hte': (transBeePL_type (typeof_expr e) ge )=> [ere' | cte' ge' ie'] //=.
  move=> [] h1 h2; subst.
  exists (Eval (transBeePL_value_cvalue v) cte'). exists Events.E0.
  split=> //=.
  + have heq:= type_preserved_generator (typeof_expr e) cte cte' g ge ge g' ie ie' ie ie'
            hte hte'; subst. apply Csem.red_rvalof.
    have := deref_addr_translated (typeof_expr e) hm l ofs bf v cte' 
            (transBeePL_value_cvalue v) ge g' ie' H hte' refl_equal.
    have hc := non_volatile_type_preserved (typeof_expr e) cte' ge g' ie' false H1 hte'.
    by rewrite /chunk_for_volatile_type /= hc /=.
  by apply sim_val with ge g' ie'.*) admit.
(* ref *) (* Fix me *)
+ admit.
(* uop *)
+ move=> hr. rewrite /SimplExpr.bind in hr.
  case ht: (transBeePL_type t g) hr=> [er | ct1 g1 i1] //=.
  case ht1: (transBeePL_type t g1)=> [er1 | ct2 g2 i2] //=.
  move=> [] h1 h2; subst. 
  exists (Eval v' ct2). exists Events.E0. split=> //=.
  + apply Csem.red_unop. 
    by have heq:= type_preserved_generator t ct ct1 g0 g'0 g g1 i'0 i1 i'0 i1 H ht; subst.
  have <- /= := bv_cv_reflex v' v'' H1. by apply sim_val with g1 g' i2.
(* bop *)
+ move=> hr. rewrite /SimplExpr.bind in hr.
  case ht1: (transBeePL_type t1 g) hr=> [er1 | ct1' g1 i1] //=.
  case ht2: (transBeePL_type t2 g1)=> [er2 | ct2' g2 i2] //=.
  case ht3: ( transBeePL_type t g2)=> [er3 | ct3 g3 i3] //=.
  move=> [] h1 h2; subst.
  exists (Eval v ct3). exists Events.E0. split=> //=.
  + apply Csem.red_binop. have -> := comp_env_preserved.
    have heq1 := type_preserved_generator t1 ct1 ct1' g0 g'0 g g1 i'0 i1 i'0 i1 H ht1; subst.
    by have heq2 := type_preserved_generator t2 ct2 ct2' g'0 g'' g1 g2 i'' i2 i'' i2 H0 ht2; subst.
  have <- /= := bv_cv_reflex v v' H2. by apply sim_val with g2 g' i3.
(* cond *) (* cond steps to Eparen which we don't have in our language *)
+ admit.
(* massgn *) 
+ (*move=> hr. rewrite /SimplExpr.bind in hr.
  case ht: (transBeePL_type t g) hr=> [er | ct1' g1 i1] //=.
  case ht2: (transBeePL_type tv2 g1)=> [er2 | ct2' g2 i1'] //=.
  case ht3: (transBeePL_type t g2)=> [er3 | ct3' g3 i2'] //=.
  move=> [] h1 h2; subst. inversion H2; subst.
  + exists (Eval (transBeePL_value_cvalue v') ct3'). exists Events.E0. split=> //=.
    + have heq1 := type_preserved_generator t ct1 ct1' g0 g'0 g g1 i'0 i1 i'0 i1 H ht; subst.
      have heq1 := type_preserved_generator tv2 ct2 ct2' g'0 g'' g1 g2 i'' i1' i'' i1' H0 ht2; subst.
      have heq1 := type_preserved_generator t ct1' ct3' g g1 g2 g' i1 i2' i1 i2' ht ht3; subst.
      apply Csem.red_assign with (transBeePL_value_cvalue v').
      + by apply H1. 
        have := assign_addr_translated t hm l ofs Full v' hm' ct3'
            (transBeePL_value_cvalue v') v' (transBeePL_value_cvalue v') g2 g' i2' H2 ht3
            refl_equal refl_equal. 
      have hc := non_volatile_type_preserved t ct3' g2 g' i2' false H4 ht3.
      by rewrite /chunk_for_volatile_type /= hc /=. 
    by apply sim_val with g2 g' i2'.
   exists (Eval (transBeePL_value_cvalue v') ct3'). exists tr. split=> //=.
   have heq1 := type_preserved_generator t ct1 ct1' g0 g'0 g g1 i'0 i1 i'0 i1 H ht; subst.
   have heq1 := type_preserved_generator tv2 ct2 ct2' g'0 g'' g1 g2 i'' i1' i'' i1' H0 ht2; subst.
   have heq1 := type_preserved_generator t ct1' ct3' g g1 g2 g' i1 i2' i1 i2' ht ht3; subst.
   apply Csem.red_assign with (transBeePL_value_cvalue v').
   + by apply H1. 
     have := assign_addr_translated t hm l ofs Full v' hm' ct3'
            (transBeePL_value_cvalue v') v' (transBeePL_value_cvalue v') g2 g' i2' H2 ht3
            refl_equal refl_equal. 
     have hc := non_volatile_type_preserved t ct3' g2 g' i2' true H4 ht3.
     rewrite /chunk_for_volatile_type /= hc /=. 
     have -> /= := access_mode_preserved t ct3' (By_value (transl_bchunk_cchunk chunk)) g2 g' i2'
             H3 ht3. move=> [] x [] _ hs. 
     apply Csem.assign_loc_volatile with (transl_bchunk_cchunk chunk).
     by have := access_mode_preserved t ct3' (By_value (transl_bchunk_cchunk chunk)) g2 g' i2'
             H3 ht3. by apply hc. have -> := bv_cv_reflex v0 v' H6.
     have hequiv := senv_preserved. rewrite /cge /Csem.genv_genv /= in hequiv.
     by have := @Events.volatile_store_preserved bge (Genv.globalenv cprog) 
                (transl_bchunk_cchunk chunk) hm l ofs v0 tr hm' hequiv H5. rewrite /Csem.genv_genv /=. 
  by apply sim_val with g2 g' i2'.*) admit.
(* bind *) (* need to think about how bind translates *)
+ admit.
(* unit *)
admit.
Admitted.  
  
(*** Matching between continuations ***) 
Inductive match_bcont_ccont : composite_env -> BeePL.cont -> Csem.cont -> Prop :=
| match_Kstop : match_bcont_ccont bprog.(prog_comp_env) BeePL.Kstop Csem.Kstop
| match_Kdo : forall bc cc,
              match_bcont_ccont bprog.(prog_comp_env) bc cc ->
              match_bcont_ccont bprog.(prog_comp_env) (BeePL.Kdo bc) (Csem.Kdo cc)
| match_Kcall : forall bf cf vm cenv CC bt ct bc cc,
                (* add linking order ?? *)
                transBeePL_function_function bf = OK cf ->
                match_env benv cenv ->
                match_bcont_ccont bprog.(prog_comp_env) bc cc ->
                match_bcont_ccont bprog.(prog_comp_env) (BeePL.Kcall bf vm bt bc) 
                                       (Csem.Kcall cf cenv CC ct cc).

(*** Matching between states ***) 
Inductive match_bstate_cstate : BeePL.state -> Csem.state -> Prop :=
| match_exprstate : forall bf cf be ce bc cc m g g' i,
                    transBeePL_function_function bf = OK cf ->
                    transBeePL_expr_expr be g = Res ce g' i ->
                    sim_bexpr_cexpr benv be ce ->
                    match_env benv cenv ->
                    match_bcont_ccont bprog.(prog_comp_env) bc cc ->
                    match_bstate_cstate (BeePL.ExprState bf be bc benv m) 
                                        (Csem.ExprState cf ce cc cenv m)
| match_state : forall bf cf be cst bc cc m g g' i, (* Fix me *)
                transBeePL_function_function bf = OK cf ->
                transBeePL_expr_st be g = Res cst g' i ->
                sim_bexpr_cstmt benv be cst ->
                match_env benv cenv ->
                match_bcont_ccont bprog.(prog_comp_env) bc cc ->
                match_bstate_cstate (BeePL.ExprState bf be bc benv m) 
                                    (Csem.State cf cst cc cenv m)
| match_callstate : forall bfd bvs bc m cfd cvs cc,
                    transBeePL_fundef_fundef bfd = OK cfd ->
                    transBeePL_values_cvalues bvs = cvs ->
                    match_bcont_ccont bprog.(prog_comp_env) bc cc ->
                    match_bstate_cstate (BeePL.CallState bfd bvs bc m)
                                        (Csem.Callstate cfd cvs cc m)
| match_stuckstate : match_bstate_cstate (BeePL.StuckState) (Csem.Stuckstate).


(* Simulation proof *)
(*         ==
     BS1 ------- CS1
     |          |
     |        + | t
     v          v
     BS2 ------- CS2
           ==                         I
*)

(* Equivalence between resultant state of BeePL big step semantics 
   and Csyntax (Cstrategy) big step semantics *) 
Lemma bstep_estep_simulation: forall bs1 bs2, 
bstep bge bs1 bs2 ->
forall cs1 (MS: match_bstate_cstate bs1 cs1),
exists cs2 t, (star Cstrategy.estep cge cs1 t cs2 (*/\(measure S2 < measure S1)%nat*) 
               \/ Cstrategy.estep cge cs1 t cs2) /\
              match_bstate_cstate bs2 cs2.
Proof.
move=> bs1 bs2 hs cs1 hm. elim: bs1 hs hm=> //=.
+ move=> f e k vm m he hm. elim: e he hm=> //=.
  (* val *)
  + move=> v t he hm. inversion hm; subst.
    inversion H6; subst. rewrite /SimplExpr.bind in H0.
    case ht: (transBeePL_type t g) H0=> [er | ct g'' i''] //=. 
    move=> [] h1 h2; subst. 
    exists (Csem.ExprState cf (Eval (transBeePL_value_cvalue v) ct) cc cenv m).
    exists Events.E0. split=> //=. 
    + admit.
    admit.
  + admit.
  (* Var *)
  + move=> v he hm. inversion hm; subst. 
    inversion H6; subst. 
Admitted.

(* Equivalence between resultant state of BeePL small step semantics 
   and Csytax (Csem) small step semantics *)
Lemma equiv_bstep_cstep : forall bs1 bs2,
BeePL.step bge benv bs1 bs2 ->
forall cs1, match_bstate_cstate bs1 cs1 ->
exists cs2 t, Csem.step cge cs1 t cs2 /\ match_bstate_cstate bs2 cs2.
Proof.
induction 1; intros.
Admitted.

End semantic_preservation.
