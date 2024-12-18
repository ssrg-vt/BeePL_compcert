Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import compcert.common.Errors Initializersproof Cstrategy BeePL_auxlemmas lib.Coqlib Errors.

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
(forall bt ct, 
transBeePL_type bt = OK ct ->
rel_type bt ct) /\ 
(forall bts cts, 
transBeePL_types transBeePL_type bts = OK cts ->
rel_types bts cts).
Proof.
Admitted.

Section specifications.

(* Simpler specification for expressions translations *) 
Inductive tr_expr_expr : BeePL.expr -> Csyntax.expr -> Prop :=
| tr_val_unit : forall t ct, (* Fix me *)
                transBeePL_type t = OK ct ->
                tr_expr_expr (BeePL.Val Vunit t) (Csyntax.Eval (transBeePL_value_cvalue Vunit) ct)
| tr_val_int : forall i t ct,
               transBeePL_type t = OK ct ->
               tr_expr_expr (BeePL.Val (Vint i) t) (Csyntax.Eval (Values.Vint i) ct)
| tr_val_long : forall i t ct,
                tr_expr_expr (BeePL.Val (Vint64 i) t) (Csyntax.Eval (Values.Vlong i) ct)
| tr_val_loc : forall l ofs t ct,
               transBeePL_type t = OK ct ->
               tr_expr_expr (BeePL.Val (Vloc l ofs) t) (Csyntax.Eval (Values.Vptr l ofs) ct)
| tr_var : forall x ct,
           transBeePL_type x.(vtype) = OK ct ->
           tr_expr_expr (BeePL.Var x) (Csyntax.Evar x.(vname) ct)
| tr_const_int : forall i t ct ,
                 transBeePL_type t = OK ct ->
                 tr_expr_expr (BeePL.Const (ConsInt i) t) (Csyntax.Eval (Values.Vint i) ct)
| tr_const_long : forall i t ct,
                  transBeePL_type t = OK ct ->
                  tr_expr_expr (BeePL.Const (ConsLong i) t) (Csyntax.Eval (Values.Vlong i) ct)
| tr_const_unit : forall cv ct, (* Fix me *)
                  transBeePL_value_cvalue Vunit = cv ->
                  transBeePL_type (Ptype Tunit) = OK ct ->
                  tr_expr_expr (BeePL.Const ConsUnit (Ptype Tunit)) (Csyntax.Eval cv ct)
| tr_prim_ref : forall e t ct ce, 
                transBeePL_type t = OK ct ->
                tr_expr_expr e ce ->
                tr_expr_expr (BeePL.Prim Ref (e :: nil) t) (Csyntax.Eaddrof ce ct)
| tr_prim_deref : forall e t ct ce,
                  transBeePL_type t = OK ct ->
                  tr_expr_expr e ce ->
                  tr_expr_expr (BeePL.Prim Deref (e :: nil) t) (Csyntax.Ederef ce ct)
| tr_prim_massgn : forall e1 e2 t ce1 ce2 ct,
                   transBeePL_type t = OK ct ->
                   tr_expr_expr e1 ce1 ->
                   tr_expr_expr e2 ce2 ->
                   tr_expr_expr (BeePL.Prim Massgn (e1 :: e2 :: nil) t) (Csyntax.Eassign ce1 ce2 ct)
| tr_prim_op : forall o e1 t ct ce1, 
               transBeePL_type t = OK ct ->
               tr_expr_expr e1 ce1 ->
               tr_expr_expr (BeePL.Prim (Uop o) (e1 :: nil) t) (Csyntax.Eunop o ce1 ct)
| tr_prim_bop : forall o e1 e2 t ct ce1 ce2,
                transBeePL_type t = OK ct ->
                tr_expr_expr e1 ce1 ->
                tr_expr_expr e2 ce2 ->
                tr_expr_expr (BeePL.Prim (Bop o) (e1 :: e2 :: nil) t) (Csyntax.Ebinop o ce1 ce2 ct)
| tr_prim_run : forall h t,
                tr_expr_expr (BeePL.Prim (Run h) nil t) (Eval (Values.Vundef) Tvoid) (* Fix me *)
| tr_bind : forall x t e e' t' ct ct' ce ce', (* Fix me *)
            transBeePL_type t = OK ct ->
            transBeePL_type t' = OK ct' ->
            tr_expr_expr e ce ->
            tr_expr_expr e' ce' ->
            tr_expr_expr (BeePL.Bind x t e e' t') (Csyntax.Ecomma (Eassign (Csyntax.Evar x ct) ce ct) ce' ct')
| tr_cond : forall e1 e2 e3 t ct ce1 ce2 ce3,
            transBeePL_type t = OK ct ->
            tr_expr_expr e1 ce1 ->
            tr_expr_expr e2 ce2 ->
            tr_expr_expr e3 ce3 ->
            tr_expr_expr (BeePL.Cond e1 e2 e3 t) (Csyntax.Econdition ce1 ce2 ce3 ct)
| tr_unit : forall t ct, (* Fix me *)
            transBeePL_type t = OK ct ->
            tr_expr_expr (BeePL.Unit t) (Csyntax.Eval (transBeePL_value_cvalue Vunit) ct)
| tr_addr : forall l ofs ct,
            transBeePL_type l.(ltype) = OK ct ->
            tr_expr_expr (BeePL.Addr l ofs) (Csyntax.Eloc l.(lname) ofs l.(lbitfield) ct)
| tr_hexpr : forall h e t, (* Fix me *)
             tr_expr_expr (BeePL.Hexpr h e t) (Eval (Values.Vundef) Tvoid). 

(* Complete me *)
Inductive tr_expr_stmt : BeePL.expr -> Csyntax.statement -> Prop :=
| tr_val_st : forall v t ct cv,
              transBeePL_type t = OK ct ->
              transBeePL_value_cvalue v = cv ->
              tr_expr_stmt (BeePL.Val v t) (Csyntax.Sreturn (Some (Eval (transBeePL_value_cvalue v) ct))).

Lemma tranBeePL_expr_expr_spec: forall e ce,
transBeePL_expr_expr e = OK ce ->
tr_expr_expr e ce.
Proof.
move=> e ce ht. elim: e ht=> //=.
(* val *)
+ move=> v t ht. monadInv ht.
  case: v=> //=.
  + by apply tr_val_unit.
  + move=> i. by apply tr_val_int.
  + move=> i. by apply tr_val_long.
  move=> l ofs. by apply tr_val_loc.
(* var *)
+ move=> vi ht. monadInv ht.
  by apply tr_var.
(* const *)
+ move=> [].
Admitted.

Lemma tranBeePL_expr_stmt_spec: forall e ce,
transBeePL_expr_st e = OK ce ->
tr_expr_stmt e ce.
Proof.
Admitted.

(* Relates global variables of BeePL and Csyntax *)
Inductive match_globvar : BeePL.globvar type -> AST.globvar Ctypes.type -> Prop :=
| match_globvar_intro : forall t init t' init' rd vo,
  transBeePL_type t = OK t' ->
  rel_type t t' ->
  match_globvar (mkglobvar t init rd vo) (AST.mkglobvar t' init' rd vo).

(* Relates the function definition of BeePL and Csyntax *)
Inductive match_function : BeePL.function -> Csyntax.function -> Prop :=
| match_fun : forall bf cf,
  transBeePL_type (BeePL.fn_return bf) = OK (Csyntax.fn_return cf) ->
  BeePL.fn_callconv bf = Csyntax.fn_callconv cf ->
  extract_vars_vinfos (BeePL.fn_args bf) = unzip1 (Csyntax.fn_params cf) ->
  transBeePL_types transBeePL_type (extract_types_vinfos (BeePL.fn_args bf)) = 
  OK (to_typelist (unzip2 (Csyntax.fn_params cf))) ->
  extract_vars_vinfos (BeePL.fn_vars bf) = unzip1 (Csyntax.fn_vars cf) ->
  transBeePL_types transBeePL_type (extract_types_vinfos (BeePL.fn_vars bf)) = 
  OK (to_typelist (unzip2 (Csyntax.fn_vars cf))) ->
  tr_expr_stmt (BeePL.fn_body bf) (Csyntax.fn_body cf) ->
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
  match_fundef (Internal f) (Ctypes.Internal cf).

Lemma transBeePL_fundef_spec : forall f cf, 
transBeePL_fundef_fundef (Internal f) = OK (Ctypes.Internal cf) ->
match_fundef (Internal f) (Ctypes.Internal cf).
Proof.
rewrite /transBeePL_fundef_fundef /= /transBeePL_function_function /=. 
move=> f cf h. monadInv h. monadInv EQ.
apply match_fundef_internal; rewrite /=; auto. 
apply tranBeePL_function_spec; auto. 
by rewrite /transBeePL_function_function /= EQ0 /= EQ /= EQ1 /= EQ2 /=; auto.
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
move=> gv h. monadInv h. apply match_gvar. case: gv EQ=> //= gi i r v.
case: x1=> //= gi' i' r' v'. rewrite /transBeePLglobvar_globvar /=. move=> h.
monadInv h. apply match_globvar_intro; auto.
have [h1 h2] := type_translated. by move: (h1 gi gi' EQ).
Qed.

End specifications.

Section Advanced_specifications.

Inductive sim_bexpr_cexpr : vmap -> BeePL.expr -> Csyntax.expr -> Prop :=
| sim_val_unit : forall le t ct, (* Fix me *)
                 transBeePL_type t = OK ct ->
                 sim_bexpr_cexpr le (BeePL.Val Vunit t) (Csyntax.Eval (transBeePL_value_cvalue Vunit) ct)
| sim_val_int : forall le i t ct,
                transBeePL_type t = OK ct ->
                sim_bexpr_cexpr le (BeePL.Val (Vint i) t) (Csyntax.Eval (Values.Vint i) ct)
| sim_val_long : forall le i t ct,
                 sim_bexpr_cexpr le (BeePL.Val (Vint64 i) t) (Csyntax.Eval (Values.Vlong i) ct)
| sim_val_loc : forall le l ofs t ct,
                transBeePL_type t = OK ct ->
                sim_bexpr_cexpr le (BeePL.Val (Vloc l ofs) t) (Csyntax.Eloc l ofs Full ct)
| sim_var_local : forall (le:BeePL.vmap) (le':Csem.env) x ct,
                  transBeePL_type x.(vtype) = OK ct ->
                  (forall le' id, if isSome (le ! id) 
                                    then (forall l, le ! id = Some (l, vtype x) /\ le' ! id = Some (l, ct)) 
                                    else le ! id = None /\ le' ! id = None) ->
                  sim_bexpr_cexpr le (BeePL.Var x) (Csyntax.Evar x.(vname) ct)
| sim_const_int : forall le i t ct,
                  transBeePL_type t = OK ct ->
                  sim_bexpr_cexpr le (BeePL.Const (ConsInt i) t) (Csyntax.Eval (Values.Vint i) ct)
| sim_const_long : forall le i t ct,
                   transBeePL_type t = OK ct ->
                   sim_bexpr_cexpr le (BeePL.Const (ConsLong i) t) (Csyntax.Eval (Values.Vlong i) ct)
| sim_const_unit : forall le cv ct, (* Fix me *)
                   transBeePL_value_cvalue Vunit = cv ->
                   transBeePL_type (Ptype Tunit) = OK ct ->
                   sim_bexpr_cexpr le (BeePL.Const ConsUnit (Ptype Tunit)) (Csyntax.Eval cv ct)
| sim_prim_ref : forall le e t ct ce, 
                 transBeePL_type t = OK ct ->
                 sim_bexpr_cexpr le e ce ->
                 sim_bexpr_cexpr le (BeePL.Prim Ref (e :: nil) t) (Csyntax.Eaddrof ce ct)
| sim_prim_deref : forall le e t ct ce,
                   transBeePL_type t = OK ct ->
                   sim_bexpr_cexpr le e ce ->
                   sim_bexpr_cexpr le (BeePL.Prim Deref (e :: nil) t) (Csyntax.Ederef ce ct)
| sim_prim_massgn : forall le e1 e2 t ce1 ce2 ct,
                    transBeePL_type t = OK ct ->
                    sim_bexpr_cexpr le e1 ce1 ->
                    sim_bexpr_cexpr le e2 ce2 ->
                    sim_bexpr_cexpr le (BeePL.Prim Massgn (e1 :: e2 :: nil) t) (Csyntax.Eassign ce1 ce2 ct)
| sim_prim_op : forall le o e1 t ct ce1, 
                transBeePL_type t = OK ct ->
                sim_bexpr_cexpr le e1 ce1 ->
                sim_bexpr_cexpr le (BeePL.Prim (Uop o) (e1 :: nil) t) (Csyntax.Eunop o ce1 ct)
| sim_prim_bop : forall le o e1 e2 t ct ce1 ce2,
                 transBeePL_type t = OK ct ->
                 sim_bexpr_cexpr le e1 ce1 ->
                 sim_bexpr_cexpr le e2 ce2 ->
                 sim_bexpr_cexpr le (BeePL.Prim (Bop o) (e1 :: e2 :: nil) t) (Csyntax.Ebinop o ce1 ce2 ct)
| sim_prim_run : forall le h t,
                 sim_bexpr_cexpr le (BeePL.Prim (Run h) nil t) (Eval (Values.Vundef) Tvoid) (* Fix me *)
| sim_bind : forall le x t e e' t' ct ct' ce ce', (* Fix me *)
             transBeePL_type t = OK ct ->
             transBeePL_type t' = OK ct' ->
             sim_bexpr_cexpr le e ce ->
             sim_bexpr_cexpr le e' ce' ->
             sim_bexpr_cexpr le (BeePL.Bind x t e e' t') (Csyntax.Ecomma (Eassign (Csyntax.Evar x ct) ce ct) ce' ct')
| sim_cond : forall le e1 e2 e3 t ct ce1 ce2 ce3,
             transBeePL_type t = OK ct ->
             sim_bexpr_cexpr le e1 ce1 ->
             sim_bexpr_cexpr le e2 ce2 ->
             sim_bexpr_cexpr le e3 ce3 ->
             sim_bexpr_cexpr le (BeePL.Cond e1 e2 e3 t) (Csyntax.Econdition ce1 ce2 ce3 ct)
| sim_unit : forall le t ct, (* Fix me *)
             transBeePL_type t = OK ct ->
             sim_bexpr_cexpr le (BeePL.Unit t) (Csyntax.Eval (transBeePL_value_cvalue Vunit) ct)
| sim_addr : forall le l ofs ct,
             transBeePL_type l.(ltype) = OK ct ->
             sim_bexpr_cexpr le (BeePL.Addr l ofs) (Csyntax.Eloc l.(lname) ofs l.(lbitfield) ct)
| sim_hexpr : forall le h e t, (* Fix me *)
              sim_bexpr_cexpr le (BeePL.Hexpr h e t) (Eval (Values.Vundef) Tvoid). 

      
End Advanced_specifications.

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
Admitted.

(* Preservation of symbols *) 
Lemma symbols_preserved : forall (id : ident), 
Genv.find_symbol (Csem.genv_genv cge) id = Genv.find_symbol bge id.
Proof.
Admitted.

(* Preservation of symbol env *)
Lemma senv_preserved : Senv.equiv (Csem.genv_genv cge) bge.
Proof.
Admitted.

(* Preservation of function ptr *) 
Lemma function_ptr_translated : forall v f,
Genv.find_funct_ptr bge v = Some f ->
exists tf, Genv.find_funct_ptr (Csem.genv_genv cge) v = Some tf /\ match_fundef f tf. 
Proof.
Admitted.

(* Preservation of function *)
Lemma functions_translated: forall v f,
Genv.find_funct bge v = Some f ->
exists tf, Genv.find_funct (Csem.genv_genv cge) v = Some tf /\ match_fundef f tf.
Proof.
Admitted.

(* Preservation of function types *)
(* Complete me *)

(* Preservation of function returns *)
Lemma function_return_preserved : forall f tf,
match_function f tf ->
transBeePL_type (BeePL.fn_return f) = OK (Csyntax.fn_return tf).
Proof.
Admitted.

(* Preservation of deref_addr between BeePL and Csyntax *) 
Lemma deref_addr_translated : forall ty m addr ofs bf v cty cv,
deref_addr ty m addr ofs bf v ->
transBeePL_type ty = OK cty ->
transBeePL_value_cvalue v = cv ->
Csem.deref_loc cge cty m addr ofs bf Events.E0 cv.
Proof.
move=> ty m addr ofs bf v cty cv hd ht hv. inversion hd; subst.
+ apply Csem.deref_loc_value with chunk.
  + by have := BeePL_auxlemmas.access_mode_preserved ty cty (By_value chunk) H ht.
  + by have := non_volatile_type_preserved ty cty H0 ht.
  rewrite /transBeePL_value_cvalue in H1. rewrite H1 /=.
  case: v hd H2=> //=.
  + by case: v0 H1=> //=.
  + by case: v0 H1=> //= i H1 i' Hd [] hi; subst.
  + by case: v0 H1=> //= i H1 i' Hd [] hi; subst.
  by case: v0 H1=> //= l i H1 l' i' Hd [] h1 h2; subst.
apply Csem.deref_loc_reference.
by have := BeePL_auxlemmas.access_mode_preserved ty cty By_reference H ht.
Qed.

(* Preservation of assign_addr between BeePL and Csyntax *) 
Lemma assgn_addr_translated : forall ty m addr ofs bf v m' cty tr cv v' cv',
assign_addr ty m addr ofs bf v m' v' ->
transBeePL_type ty = OK cty ->
transBeePL_value_cvalue v = cv ->
transBeePL_value_cvalue v' = cv' ->
Csem.assign_loc cge cty m addr ofs bf cv tr m' cv'.
Proof.
Admitted.

(* Big step semantics with rvalue *) 
Lemma bsem_cexpr_rval : forall e ce m m' v ct,
bsem_expr bge benv m e m' v ->
transBeePL_type (typeof_expr e) = OK ct ->
transBeePL_expr_expr e = OK ce ->
exists tr, eval_expr cge cenv m Csem.RV ce tr m' (Eval (transBeePL_value_cvalue v) ct).
Proof.
Admitted.


(* Big step semantics with rvalue *) 
Lemma bsem_cexpr_lval : forall e ce m m' v ct l ofs bf,
bsem_expr bge benv m e m' v ->
transBeePL_type (typeof_expr e) = OK ct ->
transBeePL_expr_expr e = OK ce ->
exists tr, eval_expr cge cenv m Csem.LV ce tr m' (Eloc l ofs bf ct).
Proof.
Admitted.


(* Big step semantics of BeePL to big step semantics of Cstrategy *) 
Lemma bsem_cexpr_preserve : forall m e m' v ce,
bsem_expr bge benv m e m' v ->
transBeePL_expr_expr e = OK ce ->
sim_bexpr_cexpr benv e ce ->
exists cv tr cm', eval_expression cge cenv m ce tr cm' cv /\
transBeePL_value_cvalue v = cv.
Proof.
move=> m e m' v ce. move: m m' v. elim: e=> //=.
(* Val *)
+ move=> v' t' m m' v he ht hs. monadInv ht; subst; rewrite /=.
  exists (transBeePL_value_cvalue v'). exists Events.E0. exists m. split=> //=.
  + apply eval_expression_intro with (Eval (transBeePL_value_cvalue v') x).
    apply eval_val. by apply esr_val.
  by inversion he; subst.
(* Var *)
+ move=> vi m m' v he ht hs. monadInv ht; subst; rewrite /=.
  inversion he; subst.
  (* local *)
  + admit.
  (* global *)
  admit.
(* Const *)
+ admit.
(* App *)
+ admit.
(* Builtin *)
+ move=> [].   
  (* Ref *)
  + move=> es t m m' v he ht hs. monadInv ht; subst; rewrite /=.
    case: es he hs EQ=> //=.
    + move=> he. by inversion he.
    move=> e es he. inversion he; subst.
    move=> hs ht. monadInv ht; subst.
    rewrite /exprlist_list_expr /=. rewrite /exprlist_list_expr /= in hs.
    have [tr htr] := bsem_cexpr_lval e x1 m m' v0 ct l Ptrofs.zero Full H4 H7 EQ.
    exists (Values.Vptr l Ptrofs.zero). eexists tr. exists m'. split=> //=.
    apply eval_expression_intro with (Csyntax.Eaddrof (Eloc l Ptrofs.zero Full ct) x0).
    + apply eval_addrof. by inversion hs; subst. 
    apply esr_addrof. by apply esl_loc.
  (* Deref *)
  + move=> es t m m' v he ht hs. monadInv ht; subst; rewrite /=.
    case: es he hs EQ=> //=.
    + move=> he. by inversion he.
    move=> e es he. inversion he; subst.
    move=> hs ht. monadInv ht; subst.
    rewrite /exprlist_list_expr /=. rewrite /exprlist_list_expr /= in hs.
    inversion hs; subst; rewrite /=.
    admit.
  (* Massgn *)
  + admit.
  (* Op *)
  + move=> u es t m m' v he ht hs. monadInv ht; subst; rewrite /=.
    inversion hs; subst. inversion he; subst. 
    rewrite /exprlist_list_expr /= in EQ. monadInv EQ; subst; rewrite /=. 
    have [tr h] := bsem_cexpr_rval e1 x1 m m' v0 ct H3 H7 EQ0.
    exists v'. exists tr. exists m'. split=> //=. 
    + apply eval_expression_intro with (Csyntax.Eunop u (Eval (transBeePL_value_cvalue v0) ct) x0). 
      + by apply eval_unop. 
      apply esr_unop with (transBeePL_value_cvalue v0).
      + by apply esr_val.
      by have heq := typec_expr e1 ct x1 H7 EQ0; subst.
    by have := bv_cv_reflex v' v H11.
  (* Bop *)
  + move=> b es t m m' v he ht hs. monadInv ht; subst; rewrite /=.
    case: es he hs EQ=> //=.
    + move=> he. by inversion he.
    move=> e es he. inversion he; subst.
    move=> hs ht. monadInv ht; subst. inversion EQ2. monadInv EQ2; subst; rewrite /=.
    rewrite /exprlist_list_expr /=. rewrite /exprlist_list_expr /= in hs.
    inversion hs; subst; rewrite /=.
    have [tr1 htr1] := bsem_cexpr_rval e x1 m hm' v1 ct1 H3 H7 EQ.
    have [tr2 htr2] := bsem_cexpr_rval e2 x hm' m' v2 ct2 H4 H10 EQ0.
    exists v0. exists (Events.Eapp tr1 tr2). exists m'. split=> //=.
    + apply eval_expression_intro with 
      (Csyntax.Ebinop b (Eval (transBeePL_value_cvalue v1) ct1) 
                        (Eval (transBeePL_value_cvalue v2) ct2) x0).
      + apply eval_binop with hm'.
        + by apply htr1.
        by apply htr2.
      apply esr_binop with (transBeePL_value_cvalue v1) (transBeePL_value_cvalue v2).
      + by apply esr_val.
      by apply esr_val.    
Admitted.


(* Returns true if the expression can be in the position of LV *)
Definition is_lbeepl (e : BeePL.expr) : bool :=
match e with 
| Val v t => false
| Var v => true 
| Const c t => false
| App id e es t => false 
| Prim b es t => match b with 
                 | Ref => false
                 | Deref => true 
                 | Massgn => false 
                 | Uop o => false
                 | Bop o => false
                 | Run h => false (* Fix me *)
                 end
| Bind x t e e' t' => false
| Cond e1 e2 e3 t => false
| Unit t => false
| Addr l ofs => false 
| Hexpr m e t => false (* Fix me *)
end.

Section Is_simples.

Variable is_simple : BeePL.expr -> bool.

Fixpoint is_simples (es : list BeePL.expr) : bool :=
match es with 
| nil => true 
| e :: es => is_simple e && is_simples es
end.

End Is_simples.

(* Return true for simple (non-effectful) expressions *)
Fixpoint is_simple (e : BeePL.expr) : bool :=
match e with 
| Val v t => true
| Var v => true 
| Const c t => true
| App id e es t => false 
| Prim b es t => match b with 
                 | Ref => is_simples is_simple es
                 | Deref => is_simples is_simple es 
                 | Massgn => is_simples is_simple es 
                 | Uop o => is_simples is_simple es
                 | Bop o => is_simples is_simple es
                 | Run h => false (* Fix me *)
                 end
| Bind x t e e' t' => false
| Cond e1 e2 e3 t => false
| Unit t => true
| Addr l ofs => true 
| Hexpr m e t => false (* Fix me *)
end.

Lemma bsem_lexpr_preserve : forall m e m' v ce,
bsem_expr bge benv m e m' v ->
is_lbeepl e = true ->
transBeePL_expr_expr e = OK ce ->
sim_bexpr_cexpr benv e ce ->
exists l ofs bv, eval_simple_lvalue cge cenv m ce l ofs bv. 
Proof.
move=> m e m' v ce he hl ht htr. elim: e he hl ht htr=> //=.
(* Var *)
+ move=> vi he _ ht htr. inversion he; subst.
  (* local *)
  + monadInv ht; subst. inversion htr; subst.
    move: (H5 cenv (vname vi)). case: ifP=> //= h h'.
    exists l, Ptrofs.zero, Full. apply esl_var_local.
    move: (h' l). by move=> [] h1 h2.
  + case: h'=> //= h1 h2. by rewrite H0 in h1.
  (* global *)
  monadInv ht; subst. inversion htr; subst.
  move: (H6 cenv (vname vi)). case: ifP=> //= h h'.
  + by rewrite H0 in h.
  case: h'=> [] h1 h2.
  exists l, Ptrofs.zero, Full. apply esl_var_global.
  + by apply h2.
  by rewrite symbols_preserved.
(* Builtin-deref *)
+ move=> [] //= es t he _ ht htr. monadInv ht.
  inversion htr; subst. rewrite /transBeePL_expr_exprs /= in EQ. 
  monadInv EQ; subst. rewrite /exprlist_list_expr /=. 
  inversion he; subst. exists l, ofs, Full.
  (*by have := eval_Ederef m e m' l ofs x1 x0 H4 EQ0.*) admit.
Admitted.

(* Preservation of expression semantics with respect to small-step semantics *)
(* Tweak lemma to not include cases where the expression take step to another expression *)
Lemma sem_lexpr_preserve : forall m e m' e' ce,
sem_expr bge benv m e m' e' ->
is_lbeepl e = true ->
transBeePL_expr_expr e = OK ce ->
sim_bexpr_cexpr benv e ce ->
exists ce', Csem.lred cge cenv ce m ce' m' /\ sim_bexpr_cexpr benv e' ce'.
Proof.
move=> m e m' e' ce he hl ht hs. elim: e he hl ht hs=> //=.
(* Var *)
+ move=> v he _ ht htr. inversion he; subst. monadInv ht.
  inversion htr; subst. 
  (* local var *)
  + exists (Csyntax.Eloc l Ptrofs.zero Full x). 
    move: (H4 cenv (vname v)). case: ifP=> //= hs h.
    + split=> //=.
      + apply Csem.red_var_local. by move: (h l)=> [].
      by apply sim_val_loc.
    case: h=> //= h1 h2. by rewrite H0 in h1.
  (* global var *)
  monadInv ht. exists (Csyntax.Eloc l Ptrofs.zero Full x). split=> //=.
  + apply Csem.red_var_global. inversion htr; subst.
    move: (H5 cenv (vname v)). case: ifP=> //= h h'.
    + rewrite /isSome in h. by rewrite H0 /= in h.
    by case: h'=> //=.
  + by rewrite symbols_preserved.
  by apply sim_val_loc.
(* Builtin: Deref *)
+ move=> [] //= es t he _ ht htr.
  monadInv ht; subst. inversion he; subst; rewrite /=.
  + rewrite /transBeePL_expr_exprs /= in EQ. monadInv EQ; subst.
    rewrite /exprlist_list_expr /=. inversion htr; subst.  
    admit.
  rewrite /transBeePL_expr_exprs /= in EQ. monadInv EQ; subst.
  rewrite /exprlist_list_expr /=. inversion htr; subst. 
  exists (Eloc l ofs Full x0). split=> //=.
  + monadInv EQ0; subst. rewrite H2 /=. apply Csem.red_deref.
  by apply sim_addr.
Admitted.

Definition is_rbeepl (e : BeePL.expr) : bool :=
match e with 
| Val v t => true
| Var v => false 
| Const c t => true
| App id e es t => false  
| Prim b es t => match b with 
                 | Ref => true
                 | Deref => true 
                 | Massgn => false 
                 | Uop o => true
                 | Bop o => true
                 | Run h => false (* Fix me *)
                 end
| Bind x t e e' t' => false
| Cond e1 e2 e3 t => false
| Unit t => true
| Addr l ofs => false 
| Hexpr m e t => false (* Fix me *)
end.

Lemma sem_rexpr_preserve : forall m e m' e' ce,
sem_expr bge benv m e m' e' ->
is_rbeepl e = true ->
transBeePL_expr_expr e = OK ce ->
sim_bexpr_cexpr benv e ce ->
exists ce' tr, Csem.rred cge ce m tr ce' m' /\ sim_bexpr_cexpr benv e' ce'.
Proof.
Admitted. 

(* Preservation of allocation of variables between BeePL and Csyntax *)
Lemma alloc_variables_preserved: forall m m' benv' vrs cvrs cvrs' cvrs'' cts,
BeePL.alloc_variables benv m vrs benv' m' ->
extract_vars_vinfos vrs = cvrs ->
extract_types_vinfos vrs = cvrs' ->
transBeePL_types transBeePL_type cvrs' = OK cvrs'' ->
from_typelist cvrs'' = cts ->
exists cenv', Csem.alloc_variables cge cenv m (zip cvrs cts) cenv' m'.
Proof.
Admitted.

(* Preservation of bind parameters between BeePL and Csyntax *)
Lemma bind_variables_preserved: forall m m' benv' vrs cvrs cvrs' cvrs'' cts,
BeePL.bind_variables benv m vrs benv' m' ->
extract_vars_vinfos vrs = cvrs ->
extract_types_vinfos vrs = cvrs' ->
transBeePL_types transBeePL_type cvrs' = OK cvrs'' ->
from_typelist cvrs'' = cts ->
exists cenv', Csem.bind_parameters cge cenv m (zip cvrs cts) cenv' m'.
Proof.
Admitted.

(* Preservation of semantics of expressions in BeePL and statements in Csyntax *) 
(* Refer: sstep_simulation in SimplExprproof.v *)

End semantic_preservation.

