Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import Initializersproof Cstrategy BeePL_auxlemmas Coqlib Errors BeePL_typesystem_proofs.

From mathcomp Require Import all_ssreflect. 

(***** Correctness proof for the Csyntax generation from BeePL using BeePL compiler *****)

Section specifications.

(* Simpler specification for expressions translations *) 
Inductive sim_bexpr_cexpr : vmap -> BeePL.expr -> Csyntax.expr -> Prop :=
| sim_val : forall le v t ct g g' i, 
            transBeePL_type t g = Res ct g' i->
            sim_bexpr_cexpr le (BeePL.Val v t) (Csyntax.Eval (transBeePL_value_cvalue v) ct)
| sim_valof : forall le e t ct ce g g' i,
              transBeePL_type t g = Res ct g' i ->
              sim_bexpr_cexpr le e ce ->
              sim_bexpr_cexpr le (BeePL.Valof e t) (Csyntax.Evalof ce ct)
| sim_var : forall (le:BeePL.vmap) (le':Csem.env) x ct g g' i,
            transBeePL_type x.(vtype) g = Res ct g' i ->
                  (forall le' id, if isSome (le ! id) 
                                    then (forall l, le ! id = Some (l, vtype x) /\ le' ! id = Some (l, ct)) 
                                    else le ! id = None /\ le' ! id = None) ->
            sim_bexpr_cexpr le (BeePL.Var x) (Csyntax.Evar x.(vname) ct)
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
| sim_addr : forall le l ofs ct g g' i',
             transBeePL_type l.(ltype) g = Res ct g' i' ->
             sim_bexpr_cexpr le (BeePL.Addr l ofs) (Csyntax.Eloc l.(lname) ofs l.(lbitfield) ct)
| sim_hexpr : forall le h e t, (* Fix me *)
              sim_bexpr_cexpr le (BeePL.Hexpr h e t) (Eval (Values.Vundef) Tvoid).
 

(* Complete me *)  
Inductive sim_bexpr_cstmt : vmap -> BeePL.expr -> Csyntax.statement -> Prop :=
| sim_val_st : forall le v t ct cv g g' i',
               transBeePL_type t g = Res ct g' i' ->
               transBeePL_value_cvalue v = cv ->
               sim_bexpr_cstmt le (BeePL.Val v t) 
                                  (Csyntax.Sreturn (Some (Eval (transBeePL_value_cvalue v) ct)))
| sim_valof_st : forall le e t ct ce g g' i',
                 transBeePL_type t g = Res ct g' i' ->
                 sim_bexpr_cexpr le e ce ->
                 sim_bexpr_cstmt le (BeePL.Valof e t)
                                    (Csyntax.Sreturn (Some (Evalof ce ct)))
| sim_var_st : forall (le:BeePL.vmap) (le':Csem.env) x ct g g' i',
                   transBeePL_type x.(vtype) g = Res ct g' i' ->
                  (forall le' id, if isSome (le ! id) 
                                    then (forall l, le ! id = Some (l, vtype x) /\ le' ! id = Some (l, ct)) 
                                    else le ! id = None /\ le' ! id = None) ->
                sim_bexpr_cstmt le (BeePL.Var x) (Csyntax.Sreturn (Some (Evalof (Csyntax.Evar (vname x) ct) ct)))
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
                     sim_bexpr_cexpr le (Var x') ce' ->
                     sim_bexpr_cstmt le (BeePL.Bind x t e (Var x') t') 
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
| sim_addr_st : forall le l ofs ct g g' i',
                transBeePL_type l.(ltype) g = Res ct g' i' ->
                sim_bexpr_cstmt le (BeePL.Addr l ofs) (Csyntax.Sdo (Csyntax.Eloc l.(lname) ofs l.(lbitfield) ct))
| sim_hexpr_st : forall le h e t, (* Fix me *)
                 sim_bexpr_cstmt le (BeePL.Hexpr h e t) (Sdo (Eval (Values.Vundef) Tvoid)).

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
  extract_vars_vinfos (BeePL.fn_args bf) = unzip1 (Csyntax.fn_params cf) ->
  transBeePL_types transBeePL_type (extract_types_vinfos (BeePL.fn_args bf)) = 
  ret (to_typelist (unzip2 (Csyntax.fn_params cf))) ->
  extract_vars_vinfos (BeePL.fn_vars bf) = unzip1 (Csyntax.fn_vars cf) ->
  transBeePL_types transBeePL_type (extract_types_vinfos (BeePL.fn_vars bf)) = 
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
  match_fundef (Internal f) (Ctypes.Internal cf).

Lemma transBeePL_fundef_spec : forall f cf, 
transBeePL_fundef_fundef (Internal f) = OK (Ctypes.Internal cf) ->
match_fundef (Internal f) (Ctypes.Internal cf).
Proof.
rewrite /transBeePL_fundef_fundef /= /transBeePL_function_function /=. 
move=> f cf h. monadInv h. move: EQ.
case ht: (transBeePL_type (BeePL.fn_return f) (initial_generator tt))=> [er | r g i]//=. 
case hts : (transBeePL_types transBeePL_type (BeePL_aux.unzip2 (extract_list_rvtypes (fn_args f)))
      (initial_generator tt))=> [er' | r' g' i'] //=.
case hts' : (transBeePL_types transBeePL_type (BeePL_aux.unzip2 (extract_list_rvtypes (BeePL.fn_vars f))) (initial_generator tt))=> [er1 | r1 g1 i1] //=.
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

(* Preservation of symbols *) 
Lemma symbols_preserved : forall (id : ident), 
Genv.find_symbol (Csem.genv_genv cge) id = Genv.find_symbol bge id.
Proof.
Admitted.

(* Preservation of symbol env *)
Lemma senv_preserved : Senv.equiv (Csem.genv_genv cge) bge.
Proof.
Admitted.

(* Equivalence between vmaps benv and cenv *)
Lemma equiv_global_benv_cenv : forall vi, 
match_env benv cenv ->
benv ! (vname vi) = None ->
cenv ! (vname vi) = None.
Proof.
move=> vi h hm. case hb: (cenv ! (vname vi))=> [ [l t] | ] //=.
case h=> //= h' h''. move: (h'' (vname vi) hm)=> hc. by rewrite hc in hb.
Qed.

Lemma equiv_local_benv_cenv : forall vi l t ct g g' i, 
match_env benv cenv ->
transBeePL_type t g = Res ct g' i ->
benv ! (vname vi) = Some (l, t) ->
cenv ! (vname vi) = Some (l, ct).
Proof.
move=> vi l t ct g g' i h ht hm. 
case h=> //= h' h''. by move: (h' (vname vi) l t ct g g' i hm ht). 
Qed.

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
Lemma function_return_preserved : forall f tf g g' i,
match_function f tf ->
transBeePL_type (BeePL.fn_return f) g = Res (Csyntax.fn_return tf) g' i.
Proof.
Admitted.

(* Preservation of deref_addr between BeePL and Csyntax *) 
Lemma deref_addr_translated : forall ty m addr ofs bf v cty cv g g' i,
deref_addr ty m addr ofs bf v ->
transBeePL_type ty g = Res cty g' i ->
transBeePL_value_cvalue v = cv ->
Csem.deref_loc cge cty m addr ofs bf Events.E0 cv.
Proof.
move=> ty m addr ofs bf v cty cv g g' i hd ht hv. inversion hd; subst.
+ apply Csem.deref_loc_value with (transl_memory_chunk chunk).
  + by have := BeePL_auxlemmas.access_mode_preserved ty cty (By_value (transl_memory_chunk chunk)) g g' i H ht.
  + by have := non_volatile_type_preserved ty cty g g' i H0 ht.
  rewrite /transBeePL_value_cvalue in H1. rewrite H1 /=.
  case: v hd H2=> //=.
  + by case: v0 H1=> //=.
  + by case: v0 H1=> //= i1 H1 i' Hd [] hi; subst.
  + by case: v0 H1=> //= i1 H1 i' Hd [] hi; subst.
  by case: v0 H1=> //= l i1 H1 l' i' Hd [] h1 h2; subst.
apply Csem.deref_loc_reference.
by have := BeePL_auxlemmas.access_mode_preserved ty cty By_reference g g' i H ht.
Qed.

(* Complete Me *)
(* Preservation of assign_addr between BeePL and Csyntax *) 
Lemma assgn_addr_translated : forall ty m addr ofs bf v m' cty tr cv v' cv' g g' i,
assign_addr ty m addr ofs bf v m' v' ->
transBeePL_type ty g = Res cty g' i ->
transBeePL_value_cvalue v = cv ->
transBeePL_value_cvalue v' = cv' ->
Csem.assign_loc cge cty m addr ofs bf cv tr m' cv'.
Proof.
Admitted.

(* Big step semantics with rvalue *) 
(* If an expression evaluates to a value then in the c semantics if the expression is 
   evaluated in RV position then it should also produce the same value 
   If an expression evaluates to a value then in the c semantics if the expression is 
   evaluated in LV position then it should produce a location (deref, var)*)
Lemma bsem_cexpr_simple : 
(forall m e l ofs, 
    bsem_expr_slv bge benv m e l ofs ->
    forall ce g g' i, 
     transBeePL_expr_expr e g = Res ce g' i ->
     match_env benv cenv ->
    eval_simple_lvalue cge cenv m ce l.(lname) ofs l.(lbitfield)) /\
(forall m e v, 
    bsem_expr_srv bge benv m e v ->
    forall ce g g' i, 
     transBeePL_expr_expr e g = Res ce g' i ->
     match_env benv cenv ->
    eval_simple_rvalue cge cenv m ce (transBeePL_value_cvalue v)).

Proof.
apply bsem_expr_slv_rlv_ind=> //=.
(* LVar *)
+ move=> m x t l h a hm ht g g' i ce hte henv; subst. rewrite /SimplExpr.bind in hte. 
  case htt: (transBeePL_type (vtype x) g') hte=> [er | r g'' i'] //=.
  move=> [] h1 h2; subst. rewrite -ht in hm.
  apply esl_var_local. by have := equiv_local_benv_cenv x l (vtype x) r g' i i' henv htt hm.
(* GVar *)
+ move=> m x t l h a hm /= he ht g g' i ce hte henv. 
  rewrite /SimplExpr.bind in hte. 
  case hte': (transBeePL_type (vtype x) g') hte=> [er | r g'' i'] //=.
  move=> [] h1 h2; subst.
  apply esl_var_global.
  + by have := equiv_global_benv_cenv x henv hm. 
  by have := symbols_preserved (vname x)=> ->. 
(* Loc *)
+ move=> m l ofs ce g g' i hte henv. 
  rewrite /SimplExpr.bind in hte. 
  case ht: (transBeePL_type (ltype l) g) hte=> [er | r g'' i'] //=.
  move=> [] h1 h2; subst. by apply esl_loc.
(* Deref *)
+ move=> m e t l ofs hi ce g g' i hte henv. 
  rewrite /SimplExpr.bind in hte.
  case hte': (transBeePL_expr_expr e g) hte=> [er | r g'' i'] //=.
  case ht': (transBeePL_type t g'')=> [er' | r' g''' i''] //=.
  move=> [] h1 h2; subst. rewrite /=. apply esl_deref.
  by move: (hi r g g'' i' hte' henv).
(* Val *)
+ move=> m v t ce g g' i ht henv /=. 
  rewrite /SimplExpr.bind in ht. 
  case ht: (transBeePL_type t g) ht=> [er | r g'' i'] //=.
  move=> [] h1 h2; subst. by apply esr_val. 
(* Const int *)
+ move=> i t t' ce g g' i' ht henv /=. 
  rewrite /SimplExpr.bind in ht.
  case ht': (transBeePL_type t' g) ht=> [er | r g'' i''] //=.
  move=> [] h1 h2; subst. by apply esr_val.
(* Const long *)
+ move=> m i t ce g g' i' ht henv /=. 
  rewrite /SimplExpr.bind in ht.
  case ht': (transBeePL_type t g) ht=> [er | r g'' i''] //=.
  move=> [] h1 h2; subst.
  by apply esr_val.
(* Const unit *)
+ move=> m ce g g' i' hce henv /=; subst. 
  rewrite /SimplExpr.bind /= in hce. move: hce.
  move=> [] h1 h2; subst. by apply esr_val.
(* Valof *)
+ move=> m e t l ofs v hi ht heq hvt ce g g' i' hte henv /=; subst.
  rewrite /SimplExpr.bind in hte.
  case he1:(transBeePL_type (typeof_expr e) g) hte=> [er | r g'' i''] //=.
  case he2: (transBeePL_expr_expr e g'')=> [er1 | r1 g1 i1] //=.
  move=> [] h1 h2; subst. apply esr_rvalof with l.(lname) ofs l.(lbitfield).
  + by move: (hi r1 g'' g' i1 he2 henv).
  + have h := transBeePL_expr_expr_type_equiv e r1 g'' g' i1 he2. 
    by have := type_preserved_generator (typeof_expr e) r (Csyntax.typeof r1) 
            g g'' g'' g' i'' i1 i'' i1 he1 h.
  + by have := non_volatile_type_preserved (typeof_expr e) r g g'' i'' hvt he1. 
  by have := deref_addr_translated (typeof_expr e) m l.(lname) ofs l.(lbitfield) v r (transBeePL_value_cvalue v) g g'' i'' ht he1 refl_equal.
(* Uop *)
+ move=> m e v uop v' t ct v'' g g' i hi ht /= heq ho hv' ce g1 g2 i1 hte henv.
  rewrite /SimplExpr.bind in hte. 
  case he1: (transBeePL_expr_expr e g1) hte=> [er | r1 g1' i1'] //=.
  case ht1: (transBeePL_type t g1')=> [er' | r2 g2' i2'] //=.
  move=> [] h1 h2; subst; rewrite /=. rewrite /exprlist_list_expr /=. 
  apply esr_unop with (transBeePL_value_cvalue v).
  + by move: (hi r1 g1 g1' i1' he1 henv).
  have heq := bv_cv_reflex v' v'' hv'; subst.
  have ht' := transBeePL_expr_expr_type_equiv e r1 g1 g1' i1' he1.
  have heq1 := type_preserved_generator (typeof_expr e) (Csyntax.typeof r1) r2 
               g1 g1' g1' g2 i1' i2' i1' i2' ht' ht1.
  rewrite -heq1 in ht1.
  by have heq' := type_preserved_generator (typeof_expr e) (Csyntax.typeof r1) ct g1' g2 g g' i2' i
          i2' i ht1 ht; subst.
(* Bop *)
+ move=> m e1 e2 t v1 v2 bop v ct1 ct2 v' g g' g'' i i' hi1 hi2 ht1 ht2 [] 
         heq1 heq2 ho hv ce g1 g2 i1 hte henv; subst.
  rewrite /SimplExpr.bind in hte. 
  case hte1 : (transBeePL_expr_expr e1 g1) hte=> [er1 | re1 ge1 ie1] //=.
  case hte2 : (transBeePL_expr_expr e2 ge1)=> [er2 | re2 ge2 ie2] //=.
  case ht : (transBeePL_type (typeof_expr e1) ge2)=> [ert | rt gt it] //=.
  move=> [] h1 h2; subst. rewrite /exprlist_list_expr /=. 
  apply esr_binop with (transBeePL_value_cvalue v1) (transBeePL_value_cvalue v2).
  + by move: (hi1 re1 g1 ge1 ie1 hte1 henv).
  + by move: (hi2 re2 ge1 ge2 ie2 hte2 henv).
  have hv1 := bv_cv_reflex v v' hv.
  have ht1' := transBeePL_expr_expr_type_equiv e1 re1 g1 ge1 ie1 hte1. 
  have heq := type_preserved_generator (typeof_expr e1) ct1 rt g g' ge2 g2 i it i it ht1 ht; subst.
  have heq' := type_preserved_generator (typeof_expr e1) (Csyntax.typeof re1) rt g1 ge1 ge2 g2 ie1
               it ie1 it ht1' ht; subst.
  have ht2' := transBeePL_expr_expr_type_equiv e2 re2 ge1 ge2 ie2 hte2. 
  have heq'' := type_preserved_generator (typeof_expr e2) ct2 (Csyntax.typeof re2) g' g'' ge1 ge2 
                i' ie2 i' ie2 ht2 ht2'; subst. by have -> := comp_env_preserved.
(* Unit *)
move=> m ce g g' i /=. rewrite /SimplExpr.bind /=.
move=> [] h1 h2 henv /=; subst. by apply esr_val.
Qed.

Lemma bsem_cexpr_lsimple : 
forall m e l ofs, 
    bsem_expr_slv bge benv m e l ofs ->
    forall ce g g' i, 
     transBeePL_expr_expr e g = Res ce g' i ->
     match_env benv cenv ->
    eval_simple_lvalue cge cenv m ce l.(lname) ofs l.(lbitfield).
Proof.
exact (proj1 (bsem_cexpr_simple)).
Qed.

Lemma bsem_cexpr_rsimple :
forall m e v, 
    bsem_expr_srv bge benv m e v ->
    forall ce g g' i, 
     transBeePL_expr_expr e g = Res ce g' i ->
     match_env benv cenv ->
    eval_simple_rvalue cge cenv m ce (transBeePL_value_cvalue v).
Proof.
exact (proj2 (bsem_cexpr_simple)).
Qed.

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
extract_vars_vinfos vrs = cvrs ->
extract_types_vinfos vrs = cvrs' ->
transBeePL_types transBeePL_type cvrs' g = Res cvrs'' g' i ->
from_typelist cvrs'' = cts ->
exists cenv', Csem.alloc_variables cge cenv m (zip cvrs cts) cenv' m'.
Proof.
Admitted.

(* Complete Me *)
(* Preservation of bind parameters between BeePL and Csyntax *)
Lemma bind_variables_preserved: forall m m' benv' vrs cvrs cvrs' cvrs'' cts g g' i,
BeePL.bind_variables benv m vrs benv' m' ->
extract_vars_vinfos vrs = cvrs ->
extract_types_vinfos vrs = cvrs' ->
transBeePL_types transBeePL_type cvrs' g = Res cvrs'' g' i ->
from_typelist cvrs'' = cts ->
exists cenv', Csem.bind_parameters cge cenv m (zip cvrs cts) cenv' m'.
Proof.
Admitted.

(* Preservation of semantics of expressions in BeePL and expressions in Csyntax *) 
(* Refer: sstep_simulation in SimplExprproof.v *)
(* Equivalence between left reduction top level *)
Lemma equiv_lreduction : forall e m e' m' ce g g' i, 
is_top_level e = true /\ is_lv e = true ->
lreduction bge benv e m e' m' ->
transBeePL_expr_expr e g = Res ce g' i ->
match_env benv cenv ->
exists ce', Csem.lred cge cenv ce m ce' m' /\ sim_bexpr_cexpr benv e' ce'.
Proof.
move=> e m e' m' ce g g' i hc hl. move: m m' e' ce hl hc. elim: e=> //=. 
(* val *)
+ by move=> v t m m' e' ce hl [] _ //=. 
(* valof *)
+ move=> e hi t m m' e' ce hl [] _ //=.
(* var *)
+ move=> v m m' e' ce hl _ he hm. 
  rewrite /SimplExpr.bind in he. 
  case ht: (transBeePL_type (vtype v) g) he=> [er | r g'' i'] //=.
  move=> [] h1 h2; subst. inversion hl; subst. case: hm=> [hm1 hm2].
  (* local *)
  + exists (Eloc l Ptrofs.zero Full r). 
    split=> //=.
    + apply Csem.red_var_local. rewrite -H1 in H0. by move: (hm1 (vname v) l (vtype v) r g g' i' H0 ht).
    apply sim_addr with g g' i'; rewrite /=. by rewrite H1 /= in ht.
  (* global *)
  exists (Eloc l Ptrofs.zero Full r). 
  split=> //=.
  + apply Csem.red_var_global. case: hm=> hm1 hm2.
    + by move: (hm2 (vname v) H0).
    by have := symbols_preserved (vname v)=> ->. 
  apply sim_addr with g g' i'. by rewrite H1 /= in ht.
(* const *)
+ by move=> c t m m' e' ce hl [] //=.
(* call *)
+ by move=> e hi es t m m' e' ce hl [] //=.
(* prim *)
+ move=> [].
  (* ref *)
  + by move=> es t m m' e' ce hl [] //=.
  (* deref *)
  + move=> es t m m' e' ce hl hc /= he hm. inversion hl; subst. 
    + rewrite /transBeePL_expr_exprs /= /SimplExpr.bind /= in he.
      case ht0: t0 he=> [ | sz s ai | s ai] //=.
      + move=> [] h1 h2; subst. inversion hl; subst. exists (Eloc l ofs Full (Tpointer Tvoid a)). split=> //=.
        + by apply Csem.red_deref.
        apply sim_addr with g' g' i; rewrite /=. rewrite /ret /=. admit.
      + move=> [] h1 h2; subst. inversion hl; subst. exists (Eloc l ofs Full (Tpointer (Ctypes.Tint sz s ai) a)). 
        split=> //=.
        + by apply Csem.red_deref.
        apply sim_addr with g' g' i; rewrite /=. rewrite /ret /=. admit.
      + move=> [] h1 h2; subst. inversion hl; subst. exists (Eloc l ofs Full (Tpointer (Ctypes.Tlong s ai) a)). 
        split=> //=.
        + by apply Csem.red_deref.
        apply sim_addr with g' g' i; rewrite /=. rewrite /ret /=. admit.
    rewrite /is_vals in hc. move: hc. move=> [] /andP [] hc _ _.
    have [H4' H4''] := val_cannot_be_reduced bge benv e m e'0 m' hc. 
    rewrite /not in H4'. by move: (H4' H4).
  (* massgn *)
  + by move=> es t m m' e' ce hl [] //=.
  (* uop *)
  + by move=> u es t m m' e' ce hl [] //=.
  (* bop *)
  + by move=> b es t m m' e' ce hl [] //=.
  (* run *)
  by move=> m es t m' m'' e' ce hl [] //=.
(* bind *)
+ by move=> x t e hi e' hi' t' m m' e'' ce hl [] //=. 
(* cond *)
+ by move=> e hi e1 hi1 e2 hi2 t m m' e' ce hl [] //=.
(* unit *)
+ by move=> t m m' e' ce hl [] //=.
(* addr *)
+ by move=> l ofs m m' e' ce hl [] //=.
(* hexpr *)
by move=> m e hi t m1 m2 e' ce hl [] //=.
Admitted.

(* Equivalence between right reduction top level *)
Lemma equiv_rreduction : forall e m e' m' ce g g' i,
is_top_level e = true /\ is_rv e = true ->
rreduction bge benv e m e' m' ->
transBeePL_expr_expr e g = Res ce g' i ->
exists ce' t, Csem.rred cge ce m t ce' m' /\ sim_bexpr_cexpr benv e' ce'.
Proof.
move=> e m e' m' ce g g' i hc hl. move: m m' e' ce hl hc. elim: e=> //=. 
(* val *)
+ by move=> v t m m' e' ce hr [] //=. 
(* valof *)
+ (*move=> e hi t m m' e' ce hr [] hc _ he. rewrite /SimplExpr.bind in he.
  case ht: (transBeePL_type t g) he=> [er | r1 g1 i1] //=.
  case he: (transBeePL_expr_expr e g1)=> [er' | r2 g2 i2] //=.
  move=> [] h1 h2; subst. inversion hr; subst. inversion he; subst.
  rewrite /SimplExpr.bind in H0. 
  case h0 : (transBeePL_type (typeof_expr e0)) H0=> [er0 | r0 g0 i0] //=.
  move=> [] h1 h2; subst.
  have heq := type_preserved_generator (typeof_expr e0) r0 r1 g1 g' g g1 i0 i1 i0 i1 h0 ht; subst.
  + exists (Eval (transBeePL_value_cvalue v) r1). exists Events.E0.
    split=> //=.
    + apply Csem.red_rvalof.
      by have := deref_addr_translated (typeof_expr e0) m' l ofs bf v r1 
                 (transBeePL_value_cvalue v) g1 g' i0 H1 h0 refl_equal. 
    by apply sim_val with g1 g' i0.
  have [h1 h2] := addr_cannot_be_reduced e m e'0 m' hc. 
  rewrite /not in h2. by move: (h2 H4).*) admit.
(* var *)
+ by move=> v m m' e' ce hr [] //=.
(* const *)
+ move=> c t m m' e' ce hr _. case: c hr=> //=.
  + move=> i' /= hr he. rewrite /SimplExpr.bind in he.
    case ht: (transBeePL_type t g) he=> [er | r g'' i''] //=. 
    move=> [] h1 h2; subst. by inversion hr; subst.
  + move=> i' /= hr he. rewrite /SimplExpr.bind in he.
    case ht: (transBeePL_type t g) he=> [er | r g'' i''] //=. 
    move=> [] h1 h2; subst. by inversion hr; subst.
  move=> /= hr he. rewrite /SimplExpr.bind in he.
  case ht: (transBeePL_type t g) he=> [er | r g'' i''] //=. 
  move=> [] h1 h2; subst. by inversion hr; subst.
(* app *)
+ by move=> e m m' t m1 m2 e' ce hr [] //=.
(* prim *)
+ move=> [].
  (* ref *)
  + by move=> es t m m' e' ce hr [] hc _ he.
  (* deref *)
  + by move=> es t m m' e' ce hr [] //=.
  (* massgn *)
  + move=> es t m m' e' ce hr. inversion hr; subst; rewrite /=.
    + move=> _. rewrite /SimplExpr.bind /=.  
      case ht1 : (transBeePL_type t g)=> [er1 | r1 g1 i1] //=.
      case ht2 : (transBeePL_type tv2 g1) => [er2 | r2 g2 i2] //=.
      case ht3 : (transBeePL_type t g2) => [er3 | r3 g3 i3] //=.
      move=> [] h1 h2; subst.
      have heq1 := type_preserved_generator t ct1 r1 g0 g'0 g g1 i' i1 i' i1 H1 ht1; subst.
      have heq2 := type_preserved_generator t r3 r1 g2 g' g g1 i3 i1 i3 i1 ht3 ht1; subst.
      exists (Eval (transBeePL_value_cvalue v') r1). exists Events.E0.
      split=> //=.
      + apply Csem.red_assign with (transBeePL_value_cvalue v').
        + by have heq := type_preserved_generator tv2 ct2 r2 g'0 g'' g1 g2 i'' i2 i'' i2 H2 ht2; subst.
        by have := assgn_addr_translated t m l ofs bf v' m' r1 Events.E0
                (transBeePL_value_cvalue v') v' (transBeePL_value_cvalue v') 
                g2 g' i3 H7 ht3 refl_equal refl_equal. 
      by apply sim_val with g2 g' i3.
    + move=> [] /andP [] he1 he2 _.
      have [hf1 hf2] := addr_cannot_be_reduced bge benv e1 m e1' m' he1.
      move: hf1. by move=> [].
    + move=> [] hv _. have [h1 h2]:= val_cannot_be_reduced bge benv e2 m e2' m' hv.
      move: h1. by move=> [].
  (* uop *)
  + move=> u es t m m' e' ce hr [] //= hv _ hte. inversion hr; subst.
    + rewrite /transBeePL_expr_exprs /SimplExpr.bind in hte. 
      case he1: (transBeePL_expr_expr (Val v t) g) hte=> [er | r1 g1' i1'] //=.
      case ht1: (transBeePL_type t g1')=> [er' | r2 g2' i2'] //=.
      move=> [] h1 h2; subst; rewrite /=. exists (Eval v' r2). exists Events.E0.
      split=> //=. inversion he1; subst. rewrite /SimplExpr.bind in H0.
      case ht2: (transBeePL_type t g) H0=> [er'' | r3 g3 i3] //=. move=> [] h1 h2; subst.
      + apply Csem.red_unop. 
        by have heq := type_preserved_generator t ct r3 g0 g'0 g g1' i' i3 i' i3 H2 ht2; subst.
    have heq := bv_cv_reflex v' v'' H7; subst.
    by apply sim_val with g1' g' i2'.
  move: hv. rewrite /=. move=> /andP [] hv _. have [h1 h2] := val_cannot_be_reduced bge benv e m e'0 m' hv.
  move: h1. by move=> [].
  (* bop *)
  + move=> b es t m m' e' ce hr [] //= hv _ hte. inversion hr; subst.
    + rewrite /transBeePL_expr_exprs /= /SimplExpr.bind /= in hte.
      case ht1: (transBeePL_type t1 g) hte=> [er | r1 g2 i2] //=.
      case ht2: (transBeePL_type t2 g2)=> [er' | r2 g3 i3] //=.
      case ht3: (transBeePL_type t g3)=> [er'' | r3 g4 i4] //=.
      move=> [] h1 h2; subst.
      have heq := type_preserved_generator t1 ct1 r1 g1 g1' g g2 i1' i2 i1' i2 H2 ht1; subst.
      have heq' := type_preserved_generator t2 ct2 r2 g1' g2' g2 g3 i2' i3 i2' i3 H3 ht2; subst.
      exists (Eval v r3). exists Events.E0. split=> //=.
      + apply Csem.red_binop. by have -> := comp_env_preserved.
      have <- /= := bv_cv_reflex v v' H8. by apply sim_val with g3 g' i4.
    + rewrite /= in hv. move: hv. move=> /andP [] he1 /andP [] he2 _.
    + have [h1 h2] := val_cannot_be_reduced bge benv e1 m e1' m' he1. move: h1. by move=> [].
    rewrite /= in hv. move: hv. move=> /andP [] he2 _.
    have [h1 h2] := val_cannot_be_reduced bge benv e2 m e2' m' he2.
    move: h2. by move=> [].
  (* run *)
  by move=> m es t m1 m' e' ce hr [] //=. (* fix me *)
(* bind *)
+ by move=> x t e hi e' hi' t' m m' e'' ce hr [] //=. 
(* cond *)
+ move=> e hei e1 hei1 e2 hei2 t m m' e' ce hr [] hv _.
  inversion hr; subst.
  + rewrite /SimplExpr.bind.
    case he1: (transBeePL_expr_expr (Val v tv) g)=> [er | r g1 i1] //=.
    case he2: (transBeePL_expr_expr e1 g1)=> [er1 | r1 g2 i2] //=.
    case he3: (transBeePL_expr_expr e2 g2)=> [er2 | r2 g3 i3] //=.
    case ht1: (transBeePL_type t g3)=> [er3 | r3 g4 i4] //=.
    move=> [] h1 h2; subst. inversion he1; subst.
    rewrite /SimplExpr.bind in H0. 
    case ht2: (transBeePL_type tv g) H0=> [er4 | r4 g5 i5] //=.
    move=> [] h1 h2; subst.
    exists ((Eparen (if b then r1 else r2) r3 r3)). exists Events.E0.
    split=> //=.
    + apply Csem.red_condition.
      by have heq := type_preserved_generator tv r4 ctv g g1 g0 g'0 i5 i0 i5 i0 ht2 H6; subst.
    admit. (* cannot be solved as condition takes step to Eparen in Csyntax (* need to use star step*) *)
  have [h1 h2] := val_cannot_be_reduced bge benv e m' e1' hm' hv. move: h1. by move=> [].
(* unit *)
+ by move=> t m m' e' ce hr [] //=. 
(* addr *)
+ by move=> l ofs m m' e' ce hr [] _ //=.
(* hexpr *)
by move=> m e hi t m1 m' e' ce hr [] //=.
Admitted.
  
(*** Matching between continuations ***) 
Inductive match_bcont_ccont : composite_env -> BeePL.cont -> Csem.cont -> Prop :=
| match_Kstop : match_bcont_ccont bprog.(prog_comp_env) BeePL.Kstop Csem.Kstop
| match_Kdo : forall bc cc,
              match_bcont_ccont bprog.(prog_comp_env) bc cc ->
              match_bcont_ccont bprog.(prog_comp_env) (BeePL.Kdo bc) (Csem.Kdo cc)
| match_Kcall : forall bf cf vm cenv CC BC bt ct bc cc,
                (* add linking order ?? *)
                transBeePL_function_function bf = OK cf ->
                match_env benv cenv ->
                match_bcont_ccont bprog.(prog_comp_env) bc cc ->
                match_bcont_ccont bprog.(prog_comp_env) (BeePL.Kcall bf vm bt BC bc) 
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


Lemma lreduction_kind: forall e m e' m', 
lreduction bge benv e m e' m' -> BeePL.expr_kind e = Csem.LV.
Proof.
induction 1; auto.
Qed.


Lemma rreduction_kind: forall e m e' m', 
rreduction bge benv e m e' m' -> BeePL.expr_kind e = Csem.RV.
Proof.
induction 1; auto.
Qed.

Lemma callreduction_kind: forall e m fd args t, 
callreduction bge e m fd args t -> BeePL.expr_kind e = Csem.RV.
Proof.
induction 1; auto.
Qed.

(* Simulation proof *)
(*         ==
     BS1 ------- CS1
     |          |
     |        + | t
     v          v
     BS2 ------- CS2
           ==                         I
*)

(* == represents the match_bstate_cstate relation, which represents the equivalence relation 
      between the states of BeePL and Csyntax *)
Lemma equiv_bstep_cstep : forall bs1 bs2,
BeePL.step bge benv bs1 bs2 ->
forall cs1, match_bstate_cstate bs1 cs1 ->
exists cs2 t, Csem.step cge cs1 t cs2 /\ match_bstate_cstate bs2 cs2.
Proof.
induction 1; intros.
Admitted.

End semantic_preservation.
