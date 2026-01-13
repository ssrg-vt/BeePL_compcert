Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Csem Clight Globalenvs BeePL_Csyntax SimplExpr Csyntaxdefs.
Require Import Initializersproof Cstrategy BeePL_auxlemmas Coqlib Errors BeePL_values BeePL_sem Type_proof_C.

From mathcomp Require Import all_ssreflect.

(***** Correctness proof for the Csyntax generation from BeePL using BeePL compiler *****)

Section specifications.

Definition fctx_subset
           (fctx_small fctx_big : list (ident * type * string)) : Prop :=
  forall id ty tag,
    In (id, ty, tag) fctx_small ->
    In (id, ty, tag) fctx_big.

(* Relation between BeePL vmap and Csyntax local env *)
Record match_env (vm : BeePL.vmap) (cvm : env) : Prop := {
  mlocal :
    forall x b tx,
      vm ! x = Some (b, tx) ->
      cvm ! x = Some (b, transBeePL_type tx);

  mglobal :
    forall x,
      vm ! x = None ->
      cvm ! x = None
}.

Definition ctx_env_ok (cvm : env) (fctx : list (ident * type * string)) : Prop :=
  forall id ty tag,
    In (id, ty, tag) fctx ->
    exists b, cvm ! id = Some (b, transBeePL_type ty).

Definition fctx_fresh_in_ff (ff : seq (ident * type * string)) : Prop :=
  forall e fctx bctx g ce fctx' bctx' g' i',
    transBeePL_expr_expr e fctx bctx g
      = Res (ce, fctx', bctx') g' i' ->
    (* 1) contexts only grow *)
    fctx_subset fctx fctx' /\
    (* 2) all fresh / produced locals are in ff *)
    fctx_subset fctx' ff.

(* ---------------------------------------------------------------------- *)
(* Well-formed env: adds fctx + injectivity guarantees                    *)
(* ---------------------------------------------------------------------- *)

(* fctx = compiler’s local-variable context:
   (cx, BeePL_type, tag)
   where cx is the C identifier for the BeePL local,
   and tag is whatever metadata you carry. *)

Definition wf_env
           (vm   : BeePL.vmap)
           (cvm  : env)
           (fctx : seq (ident * type * string))
  : Prop :=
  (* 1. runtime consistency *)
  match_env vm cvm
  /\
  (* 2. fresh variable has type consistency in C env *)
  ctx_env_ok cvm fctx.


(* Specification for expressions translations *) 
(* Complete me *)
Inductive sim_bexpr_cexpr : vmap -> BeePL.expr -> Csyntax.expr -> Prop :=
| sim_val : forall le v t ct, 
            transBeePL_type t = ct ->
            sim_bexpr_cexpr le (BeePL.Val v t) (Csyntax.Eval (trans_bvalue_cvalue v) ct)
| sim_var : forall (le:BeePL.vmap) (le':Csem.env) x t ct,
            transBeePL_type t = ct ->
            (forall le' id, if isSome (le ! id) 
                            then (forall l, le ! id = Some (l, t) /\ le' ! id = Some (l, ct)) 
                            else le ! id = None /\ le' ! id = None) ->
            sim_bexpr_cexpr le (BeePL.Var x t) (Csyntax.Evar x ct)
| sim_const_int : forall le i t ct,
                  transBeePL_type t = ct->
                  sim_bexpr_cexpr le (BeePL.Const (ConsInt i) t) (Csyntax.Eval (Values.Vint i) ct)
| sim_const_long : forall le i t ct,
                   transBeePL_type t = ct ->
                   sim_bexpr_cexpr le (BeePL.Const (ConsLong i) t) (Csyntax.Eval (Values.Vlong i) ct).

 

(* Complete me *)  
Inductive sim_bexpr_cstmt : vmap -> BeePL.expr -> Csyntax.statement -> Prop :=
| sim_val_st : forall le v t ct cv,
               transBeePL_type t = ct ->
               trans_bvalue_cvalue v = cv ->
               sim_bexpr_cstmt le (BeePL.Val v t) 
                                  (Csyntax.Sreturn (Some (Eval (trans_bvalue_cvalue v) ct)))
| sim_var_st : forall (le:BeePL.vmap) (le':Csem.env) x t ct,
                   transBeePL_type t = ct ->
                  (forall le' id, if isSome (le ! id) 
                                  then (forall l, le ! id = Some (l, t) /\ le' ! id = Some (l, ct)) 
                                  else le ! id = None /\ le' ! id = None) ->
                sim_bexpr_cstmt le (BeePL.Var x t) (Csyntax.Sreturn (Some (Evalof (Csyntax.Evar x ct) ct)))
| sim_const_int_st : forall le i t ct,
                     transBeePL_type t = ct ->
                     sim_bexpr_cstmt le (BeePL.Const (ConsInt i) t) 
                                        (Csyntax.Sreturn (Some (Evalof (Csyntax.Eval (Values.Vint i) ct) ct)))
| sim_const_long_st : forall le i t ct,
                      transBeePL_type t = ct ->
                      sim_bexpr_cstmt le (BeePL.Const (ConsLong i) t) 
                                        (Csyntax.Sreturn (Some (Evalof (Csyntax.Eval (Values.Vlong i) ct) ct))).


(* Relates global variables of BeePL and Csyntax *) 
Inductive match_globvar : BeePL.globvar type -> AST.globvar Ctypes.type -> Prop :=
| match_globvar_intro : forall t init t' rd vo,
  transBeePL_type t = t' ->
  match_globvar (mkglobvar t init rd vo) (AST.mkglobvar t' init rd vo).

(* Relates the function of BeePL and Csyntax *)
Inductive match_function : BeePL.function -> Csyntax.function -> Prop :=
| match_fun : forall vm bf cf,
  transBeePL_type (BeePL.fn_return bf) = (Csyntax.fn_return cf) ->
  BeePL.fn_callconv bf = Csyntax.fn_callconv cf ->
  unzip1 (BeePL.fn_args bf) = unzip1 (Csyntax.fn_params cf) ->
  transBeePL_types transBeePL_type (unzip2 (BeePL.fn_args bf)) = (unzip2 (Csyntax.fn_params cf)) ->
  unzip1 (BeePL.fn_vars bf) = unzip1 (Csyntax.fn_vars cf) ->
  transBeePL_types transBeePL_type (unzip2 (BeePL.fn_vars bf)) = (unzip2 (Csyntax.fn_vars cf)) ->
  sim_bexpr_cstmt vm (BeePL.fn_body bf) (Csyntax.fn_body cf) ->
  match_function bf cf.

(* Relates the function defintion of BeePL and Csyntax *)
Inductive match_fundef : BeePL.fundef -> Csyntax.fundef -> Prop :=
| match_fundef_internal : forall f cf,
  match_function f cf -> 
  match_fundef (Internal f) (Ctypes.Internal cf)
| match_fundef_external : forall ef cef ts cts t ct cc,
  transBeePL_types transBeePL_type ts = cts ->
  transBeePL_type t = ct ->
  befunction_to_cefunction ef = cef ->
  match_fundef (External ef ts t cc) (Ctypes.External cef cts ct cc).

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
let pds := p1.(prog_defs) in 
let pd := unzip1 pds in 
list_forall2 (match_ident_globdef) pd  p2.(AST.prog_defs)
/\ p2.(AST.prog_main) = p1.(prog_main)
/\ p2.(AST.prog_public) = p1.(prog_public).

Definition match_prog (p1: BeePL.program) (p2: Csyntax.program) :=
    match_program_gen p1 p2
 /\ map bcomposite_ccomposite_definition (prog_types p1) = Ctypes.prog_types p2. 

End specifications.

(***** BeePL compiler adheres to a set of specifications *****)
Lemma tranBeePL_expr_expr_spec: forall vm e ce fctx bctx fctx' bctx' g g' i',
transBeePL_expr_expr e fctx bctx g = Res (ce, fctx', bctx') g' i'  ->
sim_bexpr_cexpr vm e ce. (* Add some property related to fctx and bctx *)
Proof.
Admitted. 

Lemma tranBeePL_expr_stmt_spec: forall bcenv vm e ce fctx bctx fctx' bctx' g g' i',
transBeePL_expr_st bcenv e fctx bctx g = Res (ce, fctx', bctx') g' i' ->
sim_bexpr_cstmt vm e ce. (* Add some property related to fctx and bctx *)
Proof.
Admitted. 

(***** BeePL compiler transforming BeePL global variable to C global variable satisfies the specification *****)
Lemma transBeePLglobvar_globvar_spec : forall gv gv', 
transBeePLglobvar_globvar gv = gv' ->
match_globvar gv gv'.1.
Proof.
move=> [] gt gi g gb [] gt' b /=.
rewrite /transBeePLglobvar_globvar /=. move=> [] <- /= _.
by apply match_globvar_intro.
Qed.

Lemma tranBeePL_function_spec: forall bcenv bf cf ids bctx ids' bctx',
transBeePL_function_function bcenv bf ids bctx = OK (cf, ids', bctx') ->
match_function bf cf. (* Add some property related to ids and bctx *)
Proof.
Admitted.

Lemma transBeePL_fundef_spec : forall cenv bf cf ids bctx ids' bctx', 
transBeePL_fundef_fundef cenv bf ids bctx = OK (cf, ids', bctx') ->
match_fundef bf cf. (* Add some property related to ids and bctx *)
Proof.
(*rewrite /transBeePL_fundef_fundef /= /transBeePL_function_function /=. 
move=> f cf h. monadInv h. move: EQ.
case ht: (transBeePL_type (BeePL.fn_return f) (initial_generator tt))=> [er | r g i]//=. 
case hts : (transBeePL_types transBeePL_type (BeePL_aux.unzip2 (fn_args f))
      (initial_generator tt))=> [er' | r' g' i'] //=.
case hts' : (transBeePL_types transBeePL_type (BeePL_aux.unzip2 (BeePL.fn_vars f)) (initial_generator tt))=> [er1 | r1 g1 i1] //=.
case hes : (transBeePL_expr_st (BeePL.fn_body f) (initial_generator tt))=> [er2 | r2 g2 i2] //=.
move=> [] <- /=.
apply match_fundef_internal; rewrite /=; auto. 
apply tranBeePL_function_spec; auto.
by rewrite /transBeePL_function_function /= ht hts hts' hes /=.*) 
Admitted.

Lemma transBeePL_globdef_spec: forall bcenv ccenv gd ids bctx cgd ids' bctx',
transBeePL_globdef_globdef bcenv gd ids bctx = OK (cgd, ids', ccenv, bctx') ->
match_globdef gd cgd. (* Add some property related to ids, bctx and composite env *)
Proof.
Admitted.

Lemma transf_program_match:
forall p cp, BeePL_compcert p = OK cp -> match_prog p cp.1.1.
Proof.
(*rewrite /BeePL_compcert /=. move=> p cp H. monadInv H.
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
.move=> gv h. monadInv h. apply match_gvar. case: gv EQ=> //= gi i r v.
case: x1=> //= gi' i' r' v'. rewrite /transBeePLglobvar_globvar /=. move=> h.
move: h. case ht: (transBeePL_type gi (initial_generator tt))=> [er | r1 g1 i1] //=.
move=> [] h1 h2 h3 h4; subst. apply match_globvar_intro with (initial_generator tt) g1 i1; auto.
have [h1 h2] := type_translated. by move: (h1 gi gi' (initial_generator tt) g1 i1 ht).
Qed. *)
Admitted.

Lemma fresh_ident_in_dec_false :
  forall used n id s g g' i',
    fresh_ident used n g = Res (id, s) g' i' ->
    in_idents id used = false.
Proof.
  intros.
  induction n as [| n IH].
  - (* Base case: n = 0 *)
    simpl in H.
    (* After [simpl], we have:

       let candidate_str := "__fresh__" ++ ... in
       let candidate := ident_of_string candidate_str in
       if in_idents candidate used then
         error ...
       else
         ret (candidate, candidate_str) = ret (id, s)
    *)
    (* Name the candidate so we can reuse its [in_idents] test easily. *)
    set (candidate :=
           ident_of_string
             ("__fresh__" ++ DecimalString.NilZero.string_of_uint (Nat.to_uint 0))) in *.
    destruct (in_idents candidate used) eqn:Hin.
    + (* then-branch: in_idents candidate used = true *)
      (* Here fresh_ident used 0 = error ..., so it can't equal [ret (id,s)]. *)
      move: H. by case: ifP=> //= h [] h1 h2 h3; subst. 
    + (* else-branch: in_idents candidate used = false *)
      (* Here fresh_ident used 0 = ret (candidate, candidate_str). *)
      inversion H; subst; clear H.
      (* So id = candidate; rewrite and use Hin. *)
      move: H1. by case: ifP=> //= hf [] h1 h2 h3; subst. 

  - simpl in H.
    (* Now [match n with O => _ | S n' => fresh_ident used n' end]
       simplifies to [fresh_ident used n], so we get:

       let candidate_str := "__fresh__" ++ ... in
       let candidate := ident_of_string candidate_str in
       if in_idents candidate used then
         fresh_ident used n
       else
         ret (candidate, candidate_str) = ret (id, s)
    *)
    set (candidate :=
           ident_of_string
             ("__fresh__" ++ DecimalString.NilZero.string_of_uint (Nat.to_uint (S n)))) in *.
    destruct (in_idents candidate used) eqn:Hin.
    + (* then-branch: in_idents candidate used = true *)
      (* Here [fresh_ident used (S n)] = fresh_ident used n. *)
      move: H. case: ifP=> //= hf [] h1 h2 h3; subst. rewrite /= in candidate Hin.
      exact hf.
    + (* else-branch: in_idents candidate used = false *)
      (* Here fresh_ident used (S n) = ret (candidate, candidate_str). *)
      move: H. case: ifP=> //= hf [] h1 h2 h3; subst. rewrite /= in candidate Hin.
      exact hf.
Qed.

Lemma extend_ctx_env_ok :
  forall cvm fctx x tx tag b,
    ctx_env_ok cvm fctx ->
    cvm ! x = Some (b, transBeePL_type tx) ->
    ctx_env_ok cvm ((x, tx, tag) :: fctx).
Proof.
  intros cvm fctx x tx tag b Hok Hcvm.
  unfold ctx_env_ok in *.
  intros id ty tag' Hin.
  simpl in Hin.
  destruct Hin as [Hin | Hin].
  - inversion Hin; subst.
    exists b; assumption.
  - eapply Hok; eauto.
Qed.

Lemma extend_wf_env :
  forall vm cvm fctx x cx tag b tx,
    wf_env vm cvm fctx ->
    vm ! x = Some (b, tx) ->
    cvm ! cx = Some (b, transBeePL_type tx) ->
    wf_env vm cvm ((cx, tx, tag) :: fctx).
Proof.
move=> vm cvm fctx x cx tag b tx Hwf Hvm Hcvm.
case: Hwf => [Hme Hdecls] //=.
case: Hme => [Hloc Hglob]. rewrite /wf_env.
split=> //=.
by apply extend_ctx_env_ok with b.
Qed.

Lemma ctx_env_ok_mono :
  forall cvm fctx_small fctx_big,
    ctx_env_ok cvm fctx_big ->
    fctx_subset fctx_small fctx_big ->
    ctx_env_ok cvm fctx_small.
Proof.
move=> cvm fsmall fbig Hok Hsub.
move=> id ty tag Hin_small.
have Hin_big : In (id, ty, tag) fbig.
  by apply: Hsub.
rewrite /ctx_env_ok in Hok. by move: (Hok id ty tag Hin_big).
Qed.

Lemma fctx_subset_refl : forall fctx,
fctx_subset fctx fctx.
Proof.
rewrite /fctx_subset. by move=> fctx.
Qed.

Lemma fctx_subset_cons :
  forall x fctx fF,
    fctx_subset fctx fF ->
    In x fF ->
    fctx_subset (x :: fctx) fF.
Proof.
move=> x fctx fF Hsub HinF id ty tag.
simpl.
move=> [Heq | Hin]; subst.
- exact: HinF.
- apply: Hsub; exact Hin.
Qed.

Lemma fctx_subset_cons_l x fctx1 fctx2 :
  fctx_subset fctx1 fctx2 ->
  fctx_subset (x :: fctx1) (x :: fctx2).
Proof.
move=> Hsub id ty tag.
rewrite /=.
case=> [Heq | Hin1].
- subst x; now left.
- right; apply: Hsub; exact Hin1.
Qed.

Lemma fctx_subset_trans f1 f2 f3 :
  fctx_subset f1 f2 -> fctx_subset f2 f3 -> fctx_subset f1 f3.
Proof.
move=> H12 H23 id ty tag Hin1.
apply: H23. apply: H12. exact Hin1.
Qed.

(* Preservation of composite env *) 
(* Medium *)
Lemma comp_env_preserved : forall bge cge, 
Csem.genv_cenv cge = bcomposite_composite_env (BeePL.genv_cenv bge). 
Proof.
(*rewrite /=. case: TRANSBPL=> //= h1 h2.
have /= := prog_comp_env_eq bprog. move=> h. rewrite h /=.
generalize (prog_comp_env_eq bprog) (compcert.cfrontend.Ctypes.prog_comp_env_eq cprog). 
congruence.
Qed.*)
Admitted.

(* Medium *)
(* Preservation of symbols *) 
Lemma symbols_preserved : forall bge cge (id : ident), 
Genv.find_symbol (Csem.genv_genv cge) id = Genv.find_symbol (BeePL.genv_genv bge) id.
Proof.
Admitted.

(* Medium *)
(* Preservation of symbol env *)
Lemma senv_preserved : forall bge cge, Senv.equiv (BeePL.genv_genv bge) (Csem.genv_genv cge).
Proof.
Admitted.

(* Equivalence between vmaps benv and cenv *)
Lemma equiv_global_benv_cenv : forall benv cenv vi, 
match_env benv cenv ->
benv ! vi = None ->
cenv ! vi = None.
Proof.
move=> benv cenv vi h hm. case hb: (cenv ! vi)=> [ [l t] | ] //=.
case h=> //= h' h''. move: (h'' vi hm)=> hc. by rewrite hc in hb.
Qed.

Lemma equiv_local_benv_cenv : forall benv cenv vi l t ct, 
match_env benv cenv ->
transBeePL_type t = ct ->
benv ! vi = Some (l, t) ->
cenv ! vi = Some (l, ct).
Proof.
move=> benv cenv vi l t ct h ht hm. 
case h=> //= h' h''; subst. by move: (h' vi l t hm). 
Qed.

(* Medium *)
(* Preservation of function ptr *) 
Lemma function_ptr_translated : forall bge cge v f,
Genv.find_funct_ptr (BeePL.genv_genv bge) v = Some f ->
exists tf, Genv.find_funct_ptr (Csem.genv_genv cge) v = Some tf /\ match_fundef f tf. 
Proof.
Admitted.

(* Medium *)
(* Preservation of function *)
Lemma functions_translated: forall bge cge v f,
Genv.find_funct (BeePL.genv_genv bge) v = Some f ->
exists tf, Genv.find_funct (Csem.genv_genv cge) v = Some tf /\ match_fundef f tf.
Proof.
Admitted.

(* Medium *)
(* Preservation of function returns *)
Lemma function_return_preserved : forall f tf,
match_function f tf ->
transBeePL_type (BeePL.fn_return f) = (Csyntax.fn_return tf).
Proof.
Admitted.

(* Hard *)
(* Preservation of deref_addr between BeePL and Csyntax *) 
Lemma deref_addr_translated:  forall cge ty m addr ofs bf v cty cv,
deref_addr ty m addr ofs bf v ->
transBeePL_type ty = cty ->
trans_bvalue_cvalue v = cv ->
match chunk_for_volatile_type cty bf with 
| None => Csem.deref_loc cge cty m addr ofs bf Events.E0 cv
| Some chunk => exists tr, bf = Full /\ 
                Events.volatile_load (Csem.genv_genv cge) chunk m addr ofs tr cv
end.
Proof.
(*move=> ty m addr ofs bf v cty cv hd ht hv. 
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
Qed.*)
Admitted.

(* Hard *)
(* Preservation of assign_addr between BeePL and Csyntax *)
Lemma assign_addr_translated: forall bge cge ty m addr ofs bf v m' cty cv v' cv',
assign_addr bge ty m addr ofs bf v m' v' ->
transBeePL_type ty = cty ->
trans_bvalue_cvalue v = cv ->
trans_bvalue_cvalue v' = cv' ->
match chunk_for_volatile_type cty bf with 
| None => Csem.assign_loc cge cty m addr ofs bf cv Events.E0 m' cv
| Some chunk => exists tr, bf = Full /\ 
                Events.volatile_store (Csem.genv_genv cge) chunk m addr ofs cv tr m'
end.
Proof.
Admitted.

(* Hard *)
(* Preservation of bind parameters between BeePL and Csyntax *)
Lemma bind_variables_preserved: forall bge cge benv cenv m m' benv' vrs cvrs cvrs' cvrs'' cts,
BeePL.bind_variables bge benv m vrs benv' m' ->
unzip1 vrs = cvrs ->
unzip2 vrs = cvrs' ->
transBeePL_types transBeePL_type cvrs' = cvrs'' ->
exists cenv', Csem.bind_parameters cge cenv m (zip cvrs cts) cenv' m'.
Proof.
Admitted.

(* Simple expressions in BeePL: Side-effect free expressions
   Their evaluation always terminates, are deterministic, and preserve the memory states *) 
Fixpoint is_simple (e : BeePL.expr) : bool :=
match e with 
| Val _ _ => true 
| Var _ _ => true 
| Const _ _ => true 
| App _ _ _ => false 
| Prim b es _ => match b with
                 | Ref => false (* as it allocated in memory *)
                 | Deref => false (* unlike compcert (Evalof with Ederef perfoms read, deref in BeePL performs the read *)
                 | Massgn => false 
                 | Uop o => forallb is_simple es 
                 | Bop o => forallb is_simple es
                 | Cast _ => true 
                 end
| Bind x t e e' t' => is_simple e && is_simple e'
| Cond e1 e2 e3 t => is_simple e1 && is_simple e2 && is_simple e3 
| Unit t => true 
| Addr l ofs t => true 
| Sinit a xs es t => false
| Sfield e x t => false 
| For e1 e2 d e3 t => is_simple e1 && is_simple e2 && is_simple e3
| Enone t => true 
| Esome e t => is_simple e
| Match e ps es t => false
| Ebytes es t => false
| Ainit a t es t' => false
| Aaccess x t n t' => false
end. 

Lemma trans_expr_expr_ind: 
(forall e fctx bctx ce f b g g' i',
transBeePL_expr_expr e fctx bctx g = Res (ce, f, b) g' i' ->
match e with
| Val v t => ce = Eval (trans_bvalue_cvalue v) (transBeePL_type t)
             /\ f = fctx /\ b = bctx
| Var x t => ce = Csyntax.Evar x (transBeePL_type t)
             /\ f = fctx /\ b = bctx
| Const (ConsInt i) t => ce = Eval (Values.Vint i) (transBeePL_type t)
                         /\ f = fctx /\ b = bctx 
| Const (ConsLong i) t => ce = Eval (Values.Vlong i) (transBeePL_type t)
                         /\ f = fctx /\ b = bctx 
| Const ConsUnit t => ce = Eval (Values.Vint (Int.repr 0)) (transBeePL_type t)
                      /\ f = fctx /\ b = bctx       
| Const (ConsBool bo) t => if eqb bo true 
                          then ce = Eval (Values.Vint (Int.repr 1)) (transBeePL_type t)
                               /\ f = fctx /\ b = bctx 
                          else ce = Eval (Values.Vint (Int.repr 0)) (transBeePL_type t)
                               /\ f = fctx /\ b = bctx
| App e es t => exists g1 i1 i2 fce fctx' bctx' ces fctx'' bctx'', 
                transBeePL_expr_expr e fctx bctx g = Res (fce, fctx', bctx') g1 i1 /\
                transBeePL_expr_exprs transBeePL_expr_expr es fctx' bctx' g1 = Res (ces, fctx'', bctx'') g' i2 /\
                ce = Ecall fce ces (transBeePL_type t) /\ f = fctx'' /\ b = bctx''
| Prim Ref es t => exists (ces: exprlist) (fctx':seq (ident * type * string)) (bctx': bcompiler_ctx) 
                    (i : ident) (pty : type) (str : string) (fctx'': seq (ident * type * string)) (g1: generator) 
                    (i1: Ple (gen_next g) (gen_next g1)) (g2: generator) (i2 : Ple (gen_next g1) (gen_next g2)) 
                    (i3 : Ple (gen_next g2) (gen_next g')) ct, 
                   transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ces, fctx', bctx') g1 i1 /\ Zlength es = 1 /\
                   fresh_ident (List.map unzip_ident fctx') max_fresh g1 = Res (i, str) g2 i2 /\
                   ref_to_prim t g2 = Res pty g' i3 /\ ct = (transBeePL_type t) /\
                   ce = Ecomma (Eassign (Csyntax.Evar i (transBeePL_type pty)) (hd default_expr (exprlist_list_expr ces)) (transBeePL_type pty)) 
                                        (Csyntax.Eaddrof (Csyntax.Evar i (transBeePL_type pty)) ct) ct /\
                   f = (i, pty, str) :: fctx' /\ b = bctx'
| Prim Deref es t => exists ces g1 i1, 
                     transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ces, f, b) g1 i1 /\
                     ce = Csyntax.Ederef (hd default_expr (exprlist_list_expr ces)) (transBeePL_type t)
| Prim Massgn es t => exists ces g1 i1, 
                      transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ces, f, b) g1 i1 /\
                      ce = (Csyntax.Eassign (Csyntax.Ederef (hd default_expr (exprlist_list_expr ces)) 
                                                         (Csyntax.typeof (hd default_expr (exprlist_list_expr ces))))
                                            (hd default_expr (tl (exprlist_list_expr ces)))
                                 (transBeePL_type t))
| Prim (Uop o) es t => exists ces g1 i1, 
                       transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ces, f, b) g1 i1 /\
                       ce = (Csyntax.Eunop o (hd default_expr (exprlist_list_expr ces)) (transBeePL_type t)) 
| Prim (Bop o) es t => exists ces g1 i1, 
                       transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ces, f, b) g1 i1 /\
                       match o with 
                       | Cop.Odiv => exists zv g2 i2 rs g3 i3, 
                                     return_czero (transBeePL_type t) g1 = Res zv g2 i2 /\
                                     check_div ces zv (transBeePL_type t) g2 = Res rs g3 i3 /\
                                     ce = rs
                       | Cop.Omod => exists zv g2 i2 rs g3 i3, 
                                     return_czero (transBeePL_type t) g1 = Res zv g2 i2 /\
                                     check_mod ces zv (transBeePL_type t) g2 = Res rs g3 i3 /\
                                     ce = rs
                       | Cop.Oshl => exists zv g2 i2 rs g3 i3, 
                                     return_czero (transBeePL_type t) g1 = Res zv g2 i2 /\
                                     check_shl ces zv (transBeePL_type t) g2 = Res rs g3 i3 /\
                                     ce = rs
                       | Cop.Oshr => exists zv g2 i2 rs g3 i3, 
                                     return_czero (transBeePL_type t) g1 = Res zv g2 i2 /\
                                     check_shr ces zv (transBeePL_type t) g2 = Res rs g3 i3 /\
                                     ce = rs
                       | _ => ce = Csyntax.Ebinop o (hd default_expr (exprlist_list_expr ces))
                                            (hd default_expr (tl (exprlist_list_expr ces)))
                                            (transBeePL_type t)
                       end
| Prim (Cast t) es t' => exists ces g1 i1,
                         transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ces, f, b) g1 i1 /\
                         ce = Csyntax.Ecast (hd default_expr (exprlist_list_expr ces)) (transBeePL_type t)
| Bind x t e1 e2 t' => if (x =? Ctypesdefs.ident_of_string "_")%positive 
                       then exists ce1 fctx1 bctx1 g1 i1 ce2 g2 i2,
                            transBeePL_expr_expr e1 fctx bctx g = Res (ce1, fctx1, bctx1) g1 i1 /\
                            transBeePL_expr_expr e2 fctx1 bctx1 g1 = Res (ce2, f, b) g2 i2 /\ 
                            ce = Ecomma ce1 ce2 (transBeePL_type t')
                       else exists ce1 fctx1 bctx1 g1 i1 ce2 g2 i2,
                            transBeePL_expr_expr e1 fctx bctx g = Res (ce1, fctx1, bctx1) g1 i1 /\ 
                            transBeePL_expr_expr e2 fctx1 bctx1 g1 = Res (ce2, f, b) g2 i2 /\
                            ce = Ecomma (Eassign (Csyntax.Evar x (transBeePL_type t)) ce1 (transBeePL_type t)) ce2 (transBeePL_type t')
| Cond e1 e2 e3 t => exists ce1 fctx1 bctx1 g1 i1 ce2 fctx2 bctx2 g2 i2 ce3 g3 i3,
                     transBeePL_expr_expr e1 fctx bctx g = Res (ce1, fctx1, bctx1) g1 i1 /\
                     transBeePL_expr_expr e2 fctx1 bctx1 g1 = Res (ce2, fctx2, bctx2) g2 i2 /\
                     transBeePL_expr_expr e3 fctx2 bctx2 g2 = Res (ce3, f, b) g3 i3 /\
                     ce = Econdition ce1 ce2 ce3 (transBeePL_type t)
| Unit t => ce = Eval (trans_bvalue_cvalue Vunit) (transBeePL_type t) /\ f = fctx /\ b = bctx 
| Sinit sid fnames es t => match t with 
                           | BeeTypes.Stype sid' noattr => 
                             exists ces f1 b1 g1 i1 tmp tag g2 i2,
                             transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ces, f1, b1) g1 i1 /\
                             fresh_ident (List.map unzip_ident f1) max_fresh g1 = Res (tmp, tag) g2 i2 /\
                             ce = assign_struct_fields_chain (Csyntax.Evar tmp (Ctypes.Tstruct sid Ctypes.noattr)) 
                                                             (combine fnames (exprlist_list_expr ces)) 
                                                             (Csyntax.Evar tmp (Ctypes.Tstruct sid Ctypes.noattr)) 
                                                             (Ctypes.Tstruct sid Ctypes.noattr) /\
                             f = (tmp, BeeTypes.Stype sid' noattr, tag) :: f1 /\ b = b1
                           | BeeTypes.Ptrtype (BeeTypes.Reftype (BeeTypes.Bstruct sid' _) _) =>
                             exists ces f1 b1 g1 i1 tmp tag g2 i2,
                             transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ces, f1, b1) g1 i1 /\
                             fresh_ident (List.map unzip_ident f1) max_fresh g1 = Res (tmp, tag) g2 i2 /\
                             ce = assign_struct_fields_chain (Csyntax.Evar tmp (Ctypes.Tstruct sid Ctypes.noattr))
                                                             (combine fnames (exprlist_list_expr ces)) 
                                                             (Csyntax.Eaddrof (Csyntax.Evar tmp (Ctypes.Tstruct sid Ctypes.noattr)) 
                                                                      (Ctypes.Tpointer (Ctypes.Tstruct sid Ctypes.noattr) Ctypes.noattr))
                                                             (Ctypes.Tpointer (Ctypes.Tstruct sid Ctypes.noattr) Ctypes.noattr) /\
                             f = (tmp, BeeTypes.Stype sid' noattr, tag) :: f1 /\ b = b1 
                           | _ => False
                            end
| Addr _ _ _  => False
| _ => True
end) /\
(forall es fctx bctx ces f b g g' i',
 transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ces, f, b) g' i' ->
 match es with 
 | nil => ces = Enil /\ f = fctx /\ b = bctx
 | e :: es => exists ce f' b' g1 i1 i2 ce' f'' b'', 
              transBeePL_expr_expr e fctx bctx g = Res (ce, f', b') g1 i1 /\
              transBeePL_expr_exprs transBeePL_expr_expr es f' b' g1 = Res (ce', f'', b'') g' i2 /\
              ces = Econs ce ce' /\ f = f'' /\ b = b''
end).
Proof.
split. 
+ move=> e fctx bctx ce f b g g' i'. elim: e.
  + move=> v t /=. by move=> [] h1 h2 h3 h4; subst. 
  + move=> x t /= [] h1 h2 h3 h4; subst;split=> //=.
  + move=> c t /=. case: c=> //=.
    + move=> bo []. case: ifP=> //=.
      + move=> heq [] h1 h2 h3 h4; subst. by case: bo heq=> //=.
      move=> heq [] h1 h2 h3 h4; subst. by case: bo heq=> //=.
    + by move=> i [] h1 h2 h3 h4; subst.
    + by move=> i [] h1 h2 h3 h4; subst.
    by move=> [] h1 h2 h3 h4; subst.
  + move=> e hin es t h. inversion h.
    rewrite /SimplExpr.bind2 /SimplExpr.bind in H0.
    case he: (transBeePL_expr_expr e fctx bctx g) H0=> [err |re g1 i1] //=.
    case hes: (transBeePL_expr_exprs transBeePL_expr_expr es re.1.2 re.2 g1)=> [errs | res g2 i2] //=. 
    move=> [] h1 h2 h3 h4; subst. have i3 := Ple_trans (gen_next g) (gen_next g1) (gen_next g') i1 i2.
    exists g1, i1, i2, re.1.1, re.1.2, re.2, res.1.1, res.1.2, res.2. split=> //=.
    + by case: (re) => [[a b] c].
    rewrite hes /=. split=> //=. by case: (res)=> [[a b] c].
  + move=> b'. case: b'.
    (* ref *)
    + move=> es t h. Local Opaque fresh_ident max_fresh unzip_ident. inversion h.
      rewrite /SimplExpr.bind2 /SimplExpr.bind in H0.
      case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g) H0=> [errs | res g1 i1] //=.
      case hfr: (fresh_ident (List.map unzip_ident res.1.2) max_fresh g1) => [err | fr g2 i2] //=.
      case es=> //= e es'. case: es'=> //=. case htr : (ref_to_prim t g2) => [err1 | tr g3 i3] //=.
      move=> [] h1 h2 h3 h4; subst. exists res.1.1, res.1.2, res.2, fr.1, tr, fr.2. eexists. auto.
      exists g1, i1, g2, i2, i3, (transBeePL_type t). 
      by case: res h hes hfr=> [[a b] c]; subst; case: fr=> [f1 f2];split=> //=.
   (* deref *)
   + move=> es t h. inversion h. rewrite /SimplExpr.bind2 /SimplExpr.bind in H0.
     case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g) H0=> [errs | ces g1 i1] //=.
     move=> [] h1 h2 h3 h4; subst. exists ces.1.1, g', i1. by case: (ces)=> [[a b] c]; split=> //=.
   (* massgn *)       
   + move=> es t h. inversion h. rewrite /SimplExpr.bind2 /SimplExpr.bind in H0.
     case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g) H0=> [errs | ces g1 i1] //=.
     move=> [] h1 h2 h3 h4; subst. exists ces.1.1, g', i1. split=> //=.
     by case: (ces)=> [[a b] c] //=.
   (* uop *)
   + move=> uop es t h. inversion h. rewrite /SimplExpr.bind2 /SimplExpr.bind in H0.
     case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g) H0=> [errs | ces g1 i1] //=.
     move=> [] h1 h2 h3 h4; subst. exists ces.1.1, g', i1. split=> //=.
     by case: (ces)=> [[a b] c] //=.
   (* bop *)
   + move=> bop es t h. inversion h. rewrite /SimplExpr.bind2 /SimplExpr.bind in H0.
     case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g) H0=> [errs | ces g1 i1] //=.
     case: bop h=> //=.
     + move=> h [] h1 h2 h3 h4; subst. 
       exists ces.1.1, g', i1; split=> //=. by case: (ces) => [[a b] c].
     + move=> h [] h1 h2 h3 h4; subst. 
       exists ces.1.1, g', i1; split=> //=. by case: (ces) => [[a b] c].
     + move=> h [] h1 h2 h3 h4; subst. 
       exists ces.1.1, g', i1; split=> //=. by case: (ces) => [[a b] c].
     + case hz: (return_czero (transBeePL_type t) g1)=> [errz | zv g2 i2] //=.
       case hc: (check_div ces.1.1 zv (transBeePL_type t) g2)=> [errc | zc g3 i3] //=. 
       move=> h [] h1 h2 h3 h4; subst. exists ces.1.1, g1, i1;split=> //=. 
       + by case: (ces) => [[a b] c].
       by exists zv, g2, i2, ce, g', i3; split=> //=.
     + case hz: (return_czero (transBeePL_type t) g1)=> [errz | zv g2 i2] //=.
       case hc: (check_mod ces.1.1 zv (transBeePL_type t) g2)=> [errc | zc g3 i3] //=. 
       move=> h [] h1 h2 h3 h4; subst. exists ces.1.1, g1, i1;split=> //=. 
       + by case: (ces) => [[a b] c].
       by exists zv, g2, i2, ce, g', i3; split=> //=.
    + move=> h [] h1 h2 h3 h4; subst. 
       exists ces.1.1, g', i1; split=> //=. by case: (ces) => [[a b] c]. 
    + move=> h [] h1 h2 h3 h4; subst. 
       exists ces.1.1, g', i1; split=> //=. by case: (ces) => [[a b] c].
    + move=> h [] h1 h2 h3 h4; subst. 
       exists ces.1.1, g', i1; split=> //=. by case: (ces) => [[a b] c].
    + case hz: (return_czero (transBeePL_type t) g1)=> [errz | zv g2 i2] //=.
      case hc: (check_shl ces.1.1 zv (transBeePL_type t) g2)=> [errc | zc g3 i3] //=. 
      move=> h [] h1 h2 h3 h4; subst. exists ces.1.1, g1, i1;split=> //=. 
      + by case: (ces) => [[a b] c].
      by exists zv, g2, i2, ce, g', i3; split=> //=.
    + case hz: (return_czero (transBeePL_type t) g1)=> [errz | zv g2 i2] //=.
      case hc: (check_shr ces.1.1 zv (transBeePL_type t) g2)=> [errc | zc g3 i3] //=. 
      move=> h [] h1 h2 h3 h4; subst. exists ces.1.1, g1, i1;split=> //=. 
      + by case: (ces) => [[a b] c].
      by exists zv, g2, i2, ce, g', i3; split=> //=.
    + move=> h [] h1 h2 h3 h4; subst. 
       exists ces.1.1, g', i1; split=> //=. by case: (ces) => [[a b] c].
    + move=> h [] h1 h2 h3 h4; subst. 
       exists ces.1.1, g', i1; split=> //=. by case: (ces) => [[a b] c].
    + move=> h [] h1 h2 h3 h4; subst. 
       exists ces.1.1, g', i1; split=> //=. by case: (ces) => [[a b] c].
    + move=> h [] h1 h2 h3 h4; subst. 
       exists ces.1.1, g', i1; split=> //=. by case: (ces) => [[a b] c].
    + move=> h [] h1 h2 h3 h4; subst. 
       exists ces.1.1, g', i1; split=> //=. by case: (ces) => [[a b] c].
    move=> h [] h1 h2 h3 h4; subst. 
    exists ces.1.1, g', i1; split=> //=. by case: (ces) => [[a b] c].
  (* cast *)
  move=> t es t' hte. inversion hte; subst.
  rewrite /SimplExpr.bind2 /SimplExpr.bind in H0.
  case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g) H0=> [errs | ces g1 i1] //=.
  move=> [] h1 h2 h3 h4; subst. exists ces.1.1, g', i1; split=> //=. by case: (ces)=> [[a b] c].
(* Bind *)
+ move=> x t e1 hte1 e2 hte2 t' hte. inversion hte; subst. 
  case hp : (x =? 126%AC)%positive H0=> //=.
  + rewrite hp /=. rewrite /SimplExpr.bind2 /SimplExpr.bind /=.
    case he1: (transBeePL_expr_expr e1 fctx bctx g)=> [err1 | ce1 g1 i1] //=.
    case he2 : (transBeePL_expr_expr e2 ce1.1.2 ce1.2 g1)=> [err2 | ce2 g2 i2] //=.
    move=> [] h1 h2 h3 h4; subst. exists ce1.1.1, ce1.1.2, ce1.2, g1, i1, ce2.1.1, g', i2.
    split=> //=. + by case: (ce1) => [[a b] c].
    split=> //=. by case: (ce2) he2=> [[a b] c].
  rewrite hp /=. rewrite /SimplExpr.bind2 /SimplExpr.bind /=.
  case he1: (transBeePL_expr_expr e1 fctx bctx g)=> [err1 | ce1 g1 i1] //=.
  case he2: (transBeePL_expr_expr e2 ce1.1.2 ce1.2 g1)=> [err2 | ce2 g2 i2] //=.
  move=> [] h1 h2 h3 h4; subst. exists ce1.1.1, ce1.1.2, ce1.2, g1, i1, ce2.1.1, g', i2.
  split=> //=. + by case: (ce1) => [[a b] c].
  split=> //=. by case: (ce2) he2=> [[a b] c].
(* cond *)
+ move=> e1 hte1 e2 hte2 e3 hte3 t hte. inversion hte; subst.
  move: H0. rewrite /SimplExpr.bind2 /SimplExpr.bind.
  case he1: (transBeePL_expr_expr e1 fctx bctx g) => [err1 | ce1 g1 i1] //=.
  case he2: (transBeePL_expr_expr e2 ce1.1.2 ce1.2 g1) => [err2 | ce2 g2 i2] //=.
  case he3: (transBeePL_expr_expr e3 ce2.1.2 ce2.2 g2) => [err3 | ce3 g3 i3] //=.
  move=> [] h1 h2 h3 h4; subst. exists ce1.1.1, ce1.1.2, ce1.2, g1, i1, ce2.1.1, ce2.1.2, ce2.2.
  exists g2, i2, ce3.1.1, g', i3. split=> //=.
  + by case: (ce1)=> [[a b] c].
  split=> //=.
  + by case: (ce2) he2=> [[a b] c].
  split=> //=. by case: (ce3) he3=> [[a b] c].
(* unit *)
+ move=> t hte. by inversion hte; subst.
(* addr *)
+ by auto.
(* sinit *)
+ move=> i ls l' t hte. inversion hte; subst.
  move: H0. rewrite /SimplExpr.bind2 /SimplExpr.bind.
  case hes : (transBeePL_expr_exprs transBeePL_expr_expr l' fctx bctx g)=> [errs | [[ces f1] b1] g1 i1] //=. 
  case hf : (fresh_ident (List.map unzip_ident f1) max_fresh g1)=> [errf | [fv f2] g2 i2] //=.
  case: t hte=> //=.
  + move=> p /=; case: p=> //= b' a'; case: b'=> //= h' a''.
    rewrite /SimplExpr.bind2 /SimplExpr.bind. rewrite hes /= hf /=. move=> [] h1 h2 h3 h4 [] h5 h6 h7 h8; subst.
    by exists ces, f1, b, g1, i1, fv, f2, g', i2; split=> //=.
  move=> h' a. rewrite /SimplExpr.bind2 /SimplExpr.bind. rewrite hes /= hf /=.
  move=> [] h1 h2 h3 h4 [] h5 h6 h7 h8; subst.
  by exists ces, f1, b, g1, i1, fv, f2, g', i2; split=> //=.

Admitted.

Definition is_lvalue (e : Csyntax.expr) : bool :=
match e with
| Csyntax.Evar _ _ | Csyntax.Ederef _ _ | Csyntax.Efield _ _ _ => true
| _ => false
end.

(* Insights about Cstrategy: 
   In Cstrategy, a bare variable (Evar) is never evaluated as a value; 
   we always need Evalof (Evar …) to turn it into an r-value and then load its contents. 
   A big-step semantics produces a value, only by treating l-value as r-value using Evalof *) 
(* Lifts arbitrary C expressions into the “pure rvalue” fragment that matches our BeePL semantics, 
   which always returns a value *)
Fixpoint convert_to_rval (e : Csyntax.expr) : Csyntax.expr :=
match e with 
| Csyntax.Evar x t => Evalof (Csyntax.Evar x t) t
| Csyntax.Eloc l ofs bf t => Evalof (Csyntax.Eloc l ofs bf t) t
| Csyntax.Ederef e t => Evalof (Csyntax.Ederef (convert_to_rval e) t) t
| Csyntax.Efield a f t => Csyntax.Evalof (Csyntax.Efield (convert_to_rval a) f t) t
| Csyntax.Eunop op e t => Csyntax.Eunop op (convert_to_rval e) t
| Csyntax.Ecast e t => Csyntax.Ecast (convert_to_rval e) t
| Csyntax.Econdition e1 e2 e3 t => Csyntax.Econdition (convert_to_rval e1) (convert_to_rval e2) (convert_to_rval e3) t
| Csyntax.Eassign e1 e2 t => Csyntax.Eassign e1 (convert_to_rval e2) t
| Csyntax.Ecomma e1 e2 t => Csyntax.Ecomma (convert_to_rval e1) (convert_to_rval e2) t
| _ => e
end.

(* if C can evaluate e to v, then it also evaluates convert_to_rval e to the same value with the same trace. 
   For lvalue-ish e like Evar, convert_to_rval is the canonical way to turn it into something evaluable as an expression. *)
Lemma eval_convert_to_rval :
  forall ge env m e tr m' v,
    eval_expression ge env m e tr m' v ->
    eval_expression ge env m (convert_to_rval e) tr m' v.
Proof.
Admitted.

Fixpoint convert_to_rvals (es : Csyntax.exprlist) : Csyntax.exprlist :=
match es with 
| Enil => Enil
| Econs e es => Econs (convert_to_rval e) (convert_to_rvals es)
end.

Fixpoint get_exprlist (vs : list value) (ts : list type) : exprlist :=
match vs, ts with 
| nil, nil => Enil
| v :: vs, t :: ts => Econs (Eval (trans_bvalue_cvalue v) (transBeePL_type t))
                            (get_exprlist vs ts)
| _, _ => Enil
end.

Lemma trans_exprs_to_trans_expr : forall e fctx bctx g ces fctx' bctx' g' i',
transBeePL_expr_exprs transBeePL_expr_expr [:: e] fctx bctx g = Res (ces, fctx', bctx') g' i' ->
exists ce g1 i1, transBeePL_expr_expr e fctx bctx g = Res (ce, fctx', bctx') g1 i1 
                 /\ ce = hd default_expr (exprlist_list_expr ces).
Proof.
move=> e fctx bctx g ces fctx' bctx' g' i' /=. rewrite /SimplExpr.bind2 /SimplExpr.bind.
case he: (transBeePL_expr_expr e fctx bctx g)=> [err | ce g1 i1] //=.
move=> [] h1 h2 h3 h4; subst. exists ce.1.1, g', i1. by case: ce he=> [[a b] c] //=.
Qed.

Lemma access_mode_of_volatile_chunk ty c :
chunk_for_volatile_type ty Full = Some c ->
access_mode ty = By_value c.
Proof.
case: ty=> //=.
+ move=> [] //=.
  + move=> [] //=.
    + move=> a /=. rewrite /chunk_for_volatile_type.
      case: ifP=> //=. by move=> ht [] h; subst.
    move=> a /=. rewrite /chunk_for_volatile_type.
    case: ifP=> //=. by move=> ht [] h; subst.
  + move=> s a. rewrite /chunk_for_volatile_type /=.
    case: ifP=> //= ht. case: s ht=> //=.
    + by move=>  ht [] h; subst. 
    by move=> ht [] h; subst.
  + rewrite /chunk_for_volatile_type /=. move=> s a.
    case: ifP=> //=. by move=> ht [] h; subst.
  rewrite /chunk_for_volatile_type /=. move=> s a.
  case: ifP=> //=. by move=> ht [] h; subst.
+ rewrite /chunk_for_volatile_type /=. move=> s a.
  case: ifP=> //=. by move=> ht [] h; subst.
+ rewrite /chunk_for_volatile_type /=. move=> s a.
  case: ifP=> //=. case: s=> //=. 
  + by move=> ht [] h; subst. 
  by move=> ht [] h; subst.
rewrite /chunk_for_volatile_type /=. move=> t a. case: ifP=> //=.
by move=> ht [] h; subst.
Qed.

(***** Type preservation in compilation *****)
Lemma compilation_preserve_type : forall e fctx bctx ce fctx' bctx' g g' i',
transBeePL_expr_expr e fctx bctx g = Res (ce, fctx', bctx') g' i' ->
transBeePL_type (typeof_expr e) = Csyntax.typeof ce.
Proof.
move=> e. elim: e=> //=.
(* Val *)
+ move=> v t fctx bctx ce fctx' bctx' g g' i'.
  move=> [] h1 h2 h3 h4 /=; subst. by rewrite /Csyntax.typeof.
(* Var *)
+ by move=> v t fctx bctx ce fctx' bctx' g g' i' [] h1 h2 h3 h4; subst.
(* Const *)
+ move=> [].
  (* bool *)
  + move=> b t fctx bctx ce fctx' bctx' g g' i' [] h1 h2; subst.  
    move: h1. case: ifP=> //=.
    + by move=> hb [] h; subst.
    by move=> hb [] h; subst.
  (* int *)
  + by move=> i t fctx bctx ce fctx' bctx' g g' i' [] h1 h2 h3 h4; subst.
  (* long *)
  + by move=> i t fctx bctx ce fctx' bctx' g g' i' [] h1 h2 h3 h4; subst.
  by move=> t fctx bctx ce fctx' bctx' g g' i' [] h1 h2 h3 h4; subst.
(* Call *)
+ move=> e hin es t fctx bctx ce fctx' bctx' g g' i'.
  rewrite /SimplExpr.bind2 /SimplExpr.bind.
  case he: (transBeePL_expr_expr e fctx bctx g) => [err | [[ce' fe] be] g1 i1] //=.
  case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fe be) => [err' | [[ces' fes] bes] g2 i2] //=.
  by move=> [] h1 h2 h3 h4; subst. 
(* builtin *)
+ move=> [].
  (* ref *)
  + move=> es t fctx bctx ce fctx' bctx' g g' i'.
    rewrite /SimplExpr.bind2 /SimplExpr.bind.
    case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g)=> [err' | [[ces' fes] bes] g2 i2] //=.
    case hf: (fresh_ident (List.map unzip_ident fes) max_fresh g2)=> [ferr | fi gi ii] //=.
    case: es hes=> [ | e es'] //=. case: es'=> //=. rewrite /SimplExpr.bind2 /SimplExpr.bind.
    case he: (transBeePL_expr_expr e fctx bctx g) => [err | [[ce' fe] be] g1 i1] //=.
    move=> [] h1 h2 h3 h4; subst. case h: (ref_to_prim t gi)=> [err | tr gr ir] //=.
    by move=> [] h1 h2 h3 h4 /=; subst. 
  (* deref *)
  + move=> es t fctx bctx ce fctx' bctx' g g' i'.
    rewrite /SimplExpr.bind2 /SimplExpr.bind /=.
    case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g)=> [errs | [[ces' fes] bes] g2 i2] //=.
    by move=> [] h1 h2 h3 h4; subst.
  (* massgn *)
  + move=> es t fctx bctx ce fctx' bctx' g g' i'. rewrite /SimplExpr.bind2 /SimplExpr.bind.
    case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g)=> [errs | [[ces' fes] bes] g2 i2] //=.
    by move=> [] h1 h2 h3 h4 /=; subst.
  (* uop *)
  + move=> u es t fctx bctx ce fctx' bctx' g g' i'. rewrite /SimplExpr.bind2 /SimplExpr.bind.
    case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g)=> [errs | [[ces' fes] bes] g2 i2] //=.
    by move=> [] h1 h2 h3 h4; subst.
  (* bop *)
  + move=> u es t fctx bctx ce fctx' bctx' g g' i'. rewrite /SimplExpr.bind2 /SimplExpr.bind.
    case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g)=> [errs | [[ces' fes] bes] g1 i1] //=.
    case hu: u=> //=. 
    + by move=> [] h1 h2 h3 h4 /=; subst. 
    + by move=> [] h1 h2 h3 h4 /=; subst.
    + by move=> [] h1 h2 h3 h4 /=; subst.
    + case hz: (return_czero (transBeePL_type t) g1)=> [errz | zr g2 i2] //=.
      case hd: (check_div ces' zr (transBeePL_type t) g2) => [errd | rd g3 i3] //=. 
      move=> [] h1 h2 h3 h4 /=; subst. rewrite /check_div in hd.
      case: (transBeePL_type t) hd=> //=.
      + move=> [] //= [] //= a.
        + by move=> [] h1 h2; subst.
        by move=> [] h1 h2; subst.
      move=> [] //= a.
      + by move=> [] h1 h2; subst.
      by move=> [] h1 h2; subst.
    + case hz: (return_czero (transBeePL_type t) g1)=> [errz | zr g2 i2] //=.
      case hd: (check_mod ces' zr (transBeePL_type t) g2) => [errd | rd g3 i3] //=. 
      move=> [] h1 h2 h3 h4 /=; subst. rewrite /check_div in hd.
      case: (transBeePL_type t) hd=> //=.
      + move=> [] //= [] //= a.
        + by move=> [] h1 h2; subst.
        by move=> [] h1 h2; subst.
      move=> [] //= a.
      + by move=> [] h1 h2; subst.
      by move=> [] h1 h2; subst.
    + by move=> [] h1 h2 h3 h4 /=; subst.
    + by move=> [] h1 h2 h3 h4 /=; subst.
    + by move=> [] h1 h2 h3 h4 /=; subst.
    + case hz: (return_czero (transBeePL_type t) g1)=> [errz | zr g2 i2] //=.
      case hd: (check_shl ces' zr (transBeePL_type t) g2) => [errd | rd g3 i3] //=.
      move=> [] h1 h2 h3 h4 /=; subst. rewrite /check_shl in hd.
      case: (transBeePL_type t) hd=> //=.
      + by move=> i s a [] h1 h2; subst.
      by move=> s a [] h1 h2; subst.
    + case hz: (return_czero (transBeePL_type t) g1)=> [errz | zr g2 i2] //=.
      case hd: (check_shr ces' zr (transBeePL_type t) g2) => [errd | rd g3 i3] //=.
      move=> [] h1 h2 h3 h4 /=; subst. rewrite /check_shr in hd.
      case: (transBeePL_type t) hd=> //=.
      + by move=> i s a [] h1 h2; subst.
      by move=> s a [] h1 h2; subst.
    + by move=> [] h1 h2 h3 h4 /=; subst.
    + by move=> [] h1 h2 h3 h4 /=; subst.
    + by move=> [] h1 h2 h3 h4 /=; subst.
    + by move=> [] h1 h2 h3 h4 /=; subst.
    + by move=> [] h1 h2 h3 h4 /=; subst.
    by move=> [] h1 h2 h3 h4 /=; subst.
  (* Cast *)
  move=> t es t' fctx bctx ce fctx' bctx' g g' i'. rewrite /SimplExpr.bind2 /SimplExpr.bind /=.
  case hes: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g)=> [errs | [[ces' fes] bes] g3 i3] //=. by move=> [] h1 h2 h3 h4 /=; subst.
(* Bind *)
+ move=> x t e hin e' hin' t' fctx bctx ce fctx' bctx' g g' i'. 
  rewrite /SimplExpr.bind2 /SimplExpr.bind. 
  case he : (transBeePL_expr_expr e fctx bctx g)=> [err | ce1 g1 i1] //=. case: ifP=> //=. 
  + move=> hx.
    case he': (transBeePL_expr_expr e' ce1.1.2 ce1.2 g1) => [err1 | ce2 g2 i2] //=.
    by move=> [] h1 h2 h3 h4 /=; subst.
  move=> /= hx.
  case he': (transBeePL_expr_expr e' ce1.1.2 ce1.2 g1) => [err1 | ce2 g2 i2] //=.
  by move=> [] h1 h2 h3 h4 /=; subst.
(* Cond *)
+ move=> e1 hin1 e2 hin2 e3 hin3 t fctx bctx ce fctx' bctx' g g' i'.
  rewrite /SimplExpr.bind2 /SimplExpr.bind.
  case he1: (transBeePL_expr_expr e1 fctx bctx g)=> [err1 | ce1 g1 i1] //=.
  case he2: (transBeePL_expr_expr e2 ce1.1.2 ce1.2 g1) => [err2 | ce2 g2 i2] //=.
  case he3: (transBeePL_expr_expr e3 ce2.1.2 ce2.2 g2) => [err3 | ce3 g3 i3] //=.
  by move=> [] h1 h2 h3 h4; subst.
(* Unit *)
+ move=> t fctx bctx ce fctx' bctx' g g' i'. by move=> [] h1 h2 h3 h4; subst.
(* Sinit *)
+ admit.
(* Sfield *)
+ move=> e hin i t fctx bctx ce fctx' bctx' g g' i'.
  rewrite /SimplExpr.bind2 /SimplExpr.bind /=.
  case he: (transBeePL_expr_expr e fctx bctx g)=> [err1 | ce1 g1 i1] //=.
  admit.
(* None *)
+ move=> t fctx bctx ce fctx' bctx' g g' i'. case: t=> //= p.
  case: ifP=> //= hot. move=> [] h1 h2 h3 h4 /=; subst.
  by rewrite /Csyntax.typeof /=. 
(* Some *)
+ (*move=> e hin t fctx bctx ce fctx' bctx' g g' i'.
  case: t=> //= p. case: ifP=> /andP //=. move=> [] h1 h2 he.
  move: (hin fctx bctx ce fctx' bctx' g g' i' he) => <- /=.
  by have := ptr_t_eq_trans (typeof_expr e) p h2.*) admit.
(* Match *)
+ (*move=> e hin ps es t fctx bctx ce fctx' bctx' g g' i'. rewrite /SimplExpr.bind2 /SimplExpr.bind /=.
  case he : (transBeePL_expr_expr e fctx bctx) => [err | ce1 g1 i1] //=.
  case hte: (typeof_expr e)=> [ | | p | | | | ] //=. 
  case: ifP=> //= ho. case: ps=> //=.
  + by case: es=> //=.
  move=> [] //=.
  + move=> [] //=. move=> [] //=. move=> h [] //=. case: es=> //= e' es'. case: es'=> //=.
    move=> e'' [] //=. case he': (transBeePL_expr_expr e' fctx ce1.2 g1)=> [err1 | ce2 g3 i3] //=.
    case he'': (transBeePL_expr_expr e'' ce2.1.2 ce2.2 g3)=> [err2 | ce3 g4 i4] //=.
    by move=> [] h1 h2 h3 h4; subst.
  move=> h [] //=. move=> [] //= [] //=. case: es=> //= e' es'. case: es'=> //= e'' es''.
  case: es''=> //=. case he': (transBeePL_expr_expr e' fctx ce1.2 g1)=> [err1 | ce2 g3 i3] //=.
  case he'': (transBeePL_expr_expr e'' ce2.1.2 ce2.2 g3)=> [err2 | ce3 g4 i4] //=.
  by move=> [] h1 h2 h3 h4; subst.*) admit.
(* Bytes *)
+ move=> es t fctx bctx ce fctx' bctx' g g' i'. rewrite /SimplExpr.bind2 /SimplExpr.bind.
  by case he: (transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g)=> [err | ce' g1 i1] //=.
move=> h t n t' fctx bctx ce fctx' bctx' g g' i'. rewrite /SimplExpr.bind /=.
case ha: (get_array_len t g)=> [err | an g1 i1] //=. case: ifP=> //= hn.
by move=> [] h1 h2 h3 h4; subst.
Admitted.

Lemma convert_rval_type_eq : forall e,
Csyntax.typeof (convert_to_rval e) = Csyntax.typeof e.  
Proof.
move=> e. elim: e=> //=.
Qed. 

Lemma check_div_inv : forall ces v t g r g' i',
check_div ces v t g = Res r g' i' ->
match t with 
| Ctypes.Tint I32 Signed a => r = (Econdition (Csyntax.Ebinop Cop.Oor (Csyntax.Ebinop Cop.Oeq (hd default_expr (tl (exprlist_list_expr ces)))
                                                                     (Eval (Values.Vint Int.zero) t) t)
                                                      (Csyntax.Ebinop Cop.Oand (Csyntax.Ebinop Cop.Oeq (hd default_expr (exprlist_list_expr ces))
                                                                                        (Eval (Values.Vint (Int.repr Int.min_signed)) t) t)
                                                                       (Csyntax.Ebinop Cop.Oeq (hd default_expr (tl (exprlist_list_expr ces)))
                                                                                        (Eval (Values.Vint Int.mone) t) t) t) tint)
                                     (Eval v t)
                                     (Csyntax.Ebinop (Cop.Odiv) (hd default_expr (exprlist_list_expr ces)) 
                                                        (hd default_expr (tl (exprlist_list_expr ces))) t) t)
| Ctypes.Tint I32 Unsigned a => r = (Econdition (Csyntax.Ebinop Cop.Oeq (hd default_expr (tl (exprlist_list_expr ces)))
                                                                     (Eval (Values.Vint Int.zero) t) tint)
                                            (Eval v t)
                                            (Csyntax.Ebinop (Cop.Odiv) (hd default_expr (exprlist_list_expr ces)) 
                                                        (hd default_expr (tl (exprlist_list_expr ces))) t) t)
| Ctypes.Tlong Signed a => r = (Econdition (Csyntax.Ebinop Cop.Oor (Csyntax.Ebinop Cop.Oeq (hd default_expr (tl (exprlist_list_expr ces)))
                                                                     (Eval (Values.Vlong Int64.zero) t) t)
                                                      (Csyntax.Ebinop Cop.Oand (Csyntax.Ebinop Cop.Oeq (hd default_expr (exprlist_list_expr ces))
                                                                                        (Eval (Values.Vlong (Int64.repr Int64.min_signed)) t) t)
                                                                       (Csyntax.Ebinop Cop.Oeq (hd default_expr (tl (exprlist_list_expr ces)))
                                                                                        (Eval (Values.Vlong Int64.mone) t) t) t) tint)
                                     (Eval v t)
                                     (Csyntax.Ebinop (Cop.Odiv) (hd default_expr (exprlist_list_expr ces)) 
                                                        (hd default_expr (tl (exprlist_list_expr ces))) t) t)
| Ctypes.Tlong Unsigned a => r = (Econdition (Csyntax.Ebinop Cop.Oeq (hd default_expr (tl (exprlist_list_expr ces)))
                                                                     (Eval (Values.Vlong Int64.zero) t) tint)
                                            (Eval v t)
                                            (Csyntax.Ebinop (Cop.Odiv) (hd default_expr (exprlist_list_expr ces)) 
                                                        (hd default_expr (tl (exprlist_list_expr ces))) t) t)
| _ => False

end.
Proof.
move=> ces v t g r g' i' hc. case: t hc=> //=.
+ move=> [] //=. move=> [] //=.
  + by move=> a [] h1 h2; subst. 
  + by move=> a [] h1 h2; subst.
+ move=> [] //=.
  by move=> a [] h1 h2; subst.
by move=> a [] h1 h2; subst.
Qed.

(***** Semantic equivalence of unary operators between BeePL and C *****)
Lemma sem_equiv_uop : forall uop v e m v' v'' fctx bctx ce fctx' bctx' g g' i',
Cop.sem_unary_operation uop (trans_bvalue_cvalue v) (transBeePL_type (typeof_expr e)) m = Some v' ->
transBeePL_expr_expr e fctx bctx g = Res (ce, fctx', bctx') g' i' -> 
trans_cvalue_bvalue v' = OK v'' ->
Cop.sem_unary_operation uop (trans_bvalue_cvalue v) (Csyntax.typeof ce) m = Some (trans_bvalue_cvalue v'').
Proof.
Admitted.

(***** Semantic equivalence of casting operator between BeePL and C *****)
Lemma sem_equiv_cast: forall v e t m v' fctx bctx g ce fctx' bctx' g' i' v'',
Cop.sem_cast (trans_bvalue_cvalue v) (transBeePL_type (typeof_expr e)) t m = Some v' ->
transBeePL_expr_expr e fctx bctx g = Res (ce, fctx', bctx') g' i' -> 
trans_cvalue_bvalue v' = OK v'' ->
Cop.sem_cast (trans_bvalue_cvalue v) (Csyntax.typeof ce) t m = Some (trans_bvalue_cvalue v'').
Proof.
Admitted.

Lemma return_zero_beepl_c : forall t zv zv' g g' i', 
return_bzero t = OK zv ->
return_czero (transBeePL_type t) g = Res zv' g' i' ->
zv' = trans_bvalue_cvalue zv.
Proof.
move=> t zv zv' g g' i' hr hr'. case ht: t hr hr'=> [ | p| | | | | ] //=.
case: p ht=> //=.
+ by move=> sz s a ht [] h1 [] h2 h3 ; subst.
by move=> s a ht [] h1 [] h2 h3; subst.
Qed. 

Lemma signedness_of_usigned_int: forall t a,
transBeePL_type t = Ctypes.Tint I32 Unsigned a ->
signedness_of_type t = Some Unsigned. 
Proof. 
move=> t. elim t=> //=.
+ move=> [] //=. by move=> sz s a a' [] h1 h2 h3; subst.
move=> p a. elim p=> //=.
move=> [] //=. 
+ by move=> [] //=.
by move=> [] //=.
Qed.

Lemma trans_expr_preserves_fctx :
(forall e fctx bctx ce fctx' bctx' g g' i',
    transBeePL_expr_expr e fctx bctx g = Res (ce, fctx', bctx') g' i' ->
    forall cy,
        In cy (List.map unzip_ident fctx) ->
        In cy (List.map unzip_ident fctx')) /\
(forall es fctx bctx ce fctx' bctx' g g' i',
   transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ce, fctx', bctx') g' i' ->
   forall cy,
        In cy (List.map unzip_ident fctx) ->
        In cy (List.map unzip_ident fctx')).
Proof.
apply: exprs_ind_pair; subst; split=> //=. 
+ move=> fctx bctx ce fctx' bctx' g g' i' [] h1 h2 h3 h4; subst.
  by move=> cy hin.
Admitted.

Lemma trans_expr_preserves_wf_env : forall bvm cvm,
(forall e fctx bctx ce fctx' bctx' g g' i',
    wf_env bvm cvm fctx ->
    transBeePL_expr_expr e fctx bctx g = Res (ce, fctx', bctx') g' i' ->
    wf_env bvm cvm fctx') /\
(forall es fctx bctx ce fctx' bctx' g g' i',
   wf_env bvm cvm fctx ->
   transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ce, fctx', bctx') g' i' ->
   wf_env bvm cvm fctx').
Proof.
move=> bvm cvm.
apply: exprs_ind_pair; subst; split=> //=. 
Admitted.

Lemma trans_expr_preserves_fnctx_subset : 
(forall e fctx bctx ce fctx' bctx' g g' i',
    transBeePL_expr_expr e fctx bctx g = Res (ce, fctx', bctx') g' i' ->
    forall fF,
      fctx_subset fctx fF ->
      fctx_subset fctx' fF) /\
(forall es fctx bctx ce fctx' bctx' g g' i',
   transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ce, fctx', bctx') g' i' ->
   forall fF,
      fctx_subset fctx fF ->
      fctx_subset fctx' fF).
Proof.
apply: exprs_ind_pair; subst; split=> //=. 
Admitted.

(* For every BeePL variable that will need a fresh C local during translation of e, 
   the final function context ff contains some C local for it. *)

(***** Comparing BeePL big-step semantics with Csyntax big-step semantics *****)
(* BeePL’s big-step semantics is always about values, but Csyntax’s big-step semantics 
  (Cstrategy) distinguishes lvalues from rvalues. *)
(* BeePL’s big-step semantics is an rvalue semantics: every expression evaluates directly to a value.
   In contrast, the Csyntax semantics (Cstrategy) distinguishes lvalues and rvalues: expressions 
   like Evar and Efield denote locations, and must be wrapped in Evalof to produce values.
   Our compiler sometimes produces such lvalue expressions when compiling BeePL variables or field accesses. 
   To compare BeePL evaluation with C evaluation, we therefore compose the translator with a standard 
   “rvalue interpretation” convert_to_rval that systematically inserts Evalof at the right places.
   We prove that convert_to_rval is semantics-preserving in the sense that whenever C evaluates an 
   expression ce to a value v, it also evaluates convert_to_rval ce to the same value and trace. 
   Thus, our main equivalence theorem is naturally stated in terms of convert_to_rval ce, 
   which aligns the C semantics with BeePL’s rvalue semantics.*)
(* Expression correctness assumes a well-formed env;
   function correctness proves the env is well-formed. *)
Lemma bsem_csem_expr_equiv : forall bge cp fctxf,
(forall bp bvm m es m' bvm' bv cge fctx bctx ce cvm fctx' bctx' g g' i',
bsem_exprs bge bp bvm m es m' bvm' bv ->
BeePL_compcert bp = OK cp ->
transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ce, fctx', bctx') g' i' ->
wf_env bvm cvm fctx ->
fctx_fresh_in_ff fctxf ->
exists tr, eval_exprlist cge cvm m (convert_to_rvals ce) tr m' (get_exprlist bv (map typeof_expr es))) /\
(forall bp bvm m e m' bvm' bv cge fctx bctx ce cvm fctx' bctx' g g' i',
bsem_expr bge bp bvm m e m' bvm' bv ->
BeePL_compcert bp = OK cp ->
transBeePL_expr_expr e fctx bctx g = Res (ce, fctx', bctx') g' i' ->
wf_env bvm cvm fctx ->
fctx_fresh_in_ff fctxf ->
exists tr, eval_expression cge cvm m (convert_to_rval ce) tr m' (trans_bvalue_cvalue bv)).
Proof.
move=> bge.
suff: (forall bp bvm m es m' bvm' bv,
       bsem_exprs bge bp bvm m es m' bvm' bv ->
       forall cp cge fctx bctx ce cvm fctx' bctx' g g' i' fctxf,
         BeePL_compcert bp = OK cp ->
         transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ce, fctx', bctx') g' i' ->
         wf_env bvm cvm fctx ->
         fctx_fresh_in_ff fctxf ->
         exists tr, eval_exprlist cge cvm m (convert_to_rvals ce) tr m' (get_exprlist bv (map typeof_expr es))) /\
      (forall bp bvm m e m' bvm' bv ,
        bsem_expr bge bp bvm m e m' bvm' bv ->
        forall cp cge fctx bctx ce cvm fctx' bctx' g g' i' fctxf,
          BeePL_compcert bp = OK cp ->
          transBeePL_expr_expr e fctx bctx g = Res (ce, fctx', bctx') g' i' ->
          wf_env bvm cvm fctx ->
          fctx_fresh_in_ff fctxf ->
          exists tr, eval_expression cge cvm m (convert_to_rval ce) tr m' (trans_bvalue_cvalue bv)).
+ move=> [] hwt1 hwt2. split=> //=.
  + admit.
  admit.
(* We need to not simplify all defs at a time as it makes the proof slower *)
Local Opaque transBeePL_expr_expr transBeePL_type trans_bvalue_cvalue ret.
apply bsem_exprs_bsem_expr_ind_mut=> //=.
(* val *) (* done *)
+ move=> p' vm' m'' v t hw cp cge fctx bctx ce cvm fctx' bctx' g g' i' ff hp H hwf hsf.
  have [htr1 htr2] := trans_expr_expr_ind.
  move: (htr1 (Val v t) fctx bctx ce fctx' bctx' g g' i' H)=> [] h1 [] h2 h3; subst.
  exists Events.E0. apply eval_expression_intro with (Eval (trans_bvalue_cvalue v) (transBeePL_type t)).
  + by apply eval_val.
  by apply esr_val.
(* lvar *) (* done *)
+ move=> p' vm' m'' x t l v hvm hd cp cge fctx bctx ce cvm fctx' bctx' g g' i' ff hp H hwf hcvm.
  have [htr1 htr2] := trans_expr_expr_ind.
  move: (htr1 (Var x t) fctx bctx ce fctx' bctx' g g' i' H)=> [] h1 [] h2 h3; subst. inversion hd; subst.
  (* type is non volatile *)
  exists Events.E0. rewrite /convert_to_rval /=. apply eval_expression_intro with (Evalof (Csyntax.Evar x (transBeePL_type t)) (transBeePL_type t)). 
  apply eval_valof.
  + by apply H1. 
  + by apply eval_var.
  apply esr_rvalof with l Ptrofs.zero Full.
  + apply esl_var_local. case: hwf=> hm hm'.
    by have := equiv_local_benv_cenv vm' cvm x l t (transBeePL_type t) hm erefl hvm.
  + by rewrite /Csyntax.typeof.
  + by apply H1.
  have := deref_addr_translated cge t m'' l Ptrofs.zero Full v (transBeePL_type t) (trans_bvalue_cvalue v) hd erefl erefl.
  case hc: (chunk_for_volatile_type (transBeePL_type t) Full)=> [c | ] //=.
  move=> [] tr [] _ hvo. by rewrite /chunk_for_volatile_type H1 /= in hc.
(* gvar *) (* done *)
+ move=> p' vm' m'' x t l v hvm hg hd cp cge fctx bctx ce cvm fctx' bctx' g g' i' ff hp H hwf hsf.
  have [htr1 htr2] := trans_expr_expr_ind.
  move: (htr1 (Var x t) fctx bctx ce fctx' bctx' g g' i' H)=> [] h1 [] h2 h3; subst. inversion hd; subst.
  (* type is non volatile *)
  exists Events.E0. rewrite /convert_to_rval /=. 
  apply eval_expression_intro with (Evalof (Csyntax.Evar x (transBeePL_type t)) (transBeePL_type t)).
  apply eval_valof.
  + by apply H1. 
  + by apply eval_var.
  apply esr_rvalof with l Ptrofs.zero Full.
  + apply esl_var_global. case: hwf=> hm hm'. by have := equiv_global_benv_cenv vm' cvm x hm hvm.
  + have hg' := symbols_preserved bge cge x. by rewrite hg in hg'.
  + by simpl. 
  + by apply H1.
  have := deref_addr_translated cge t m'' l Ptrofs.zero Full v (transBeePL_type t) (trans_bvalue_cvalue v) hd erefl erefl.
  case hc: (chunk_for_volatile_type (transBeePL_type t) Full)=> [c | ] //=.
  move=> [] tr [] _ hvo. by rewrite /chunk_for_volatile_type H1 /= in hc.
(* const int *) (* done *)
+ move=> p' vm m'' i t cp cge fctx bctx ce cvm fctx' bctx' g g' i' ff hp H hwf hsf.
  have [htr1 htr2] := trans_expr_expr_ind.
  move: (htr1 (Const (ConsInt i) t) fctx bctx ce fctx' bctx' g g' i' H)=> [] h1 [] h2 h3; subst.
  exists Events.E0. rewrite /convert_to_rval /=. apply eval_expression_intro with (Eval (Values.Vint i) (transBeePL_type t)).
  + by apply eval_val.
  by apply esr_val.
(* const long *) (* done *)
+ move=> p' vm m'' i t cp cge fctx bctx ce cvm fctx' bctx' g g' i' ff hp H hwf hsf.
  have [htr1 htr2] := trans_expr_expr_ind.
  move: (htr1 (Const (ConsLong i) t) fctx bctx ce fctx' bctx' g g' i' H)=> [] h1 [] h2 h3; subst.
  exists Events.E0. rewrite /convert_to_rval /=. apply eval_expression_intro with (Eval (Values.Vlong i) (transBeePL_type t)).
  + by apply eval_val.
  by apply esr_val.
(* const unit *) (* done *)
+ move=> p' vm m'' cp cge fctx bctx ce cvm fctx' bctx' g g' i' ff hp H hwf hsf.
  have [htr1 htr2] := trans_expr_expr_ind.
  move: (htr1 (Const ConsUnit Utype) fctx bctx ce fctx' bctx' g g' i' H)=> [] h1 [] h2 h3; subst.
  exists Events.E0. rewrite /convert_to_rval /=. apply eval_expression_intro with (Eval (Values.Vint (Int.repr 0)) (transBeePL_type Utype)).
  + by apply eval_val.
  by apply esr_val.
(* app *)
+ (*move=> p vm1 vm2 m1 e' es t l fd m2 m3 m4 m5 m6 vs rv he hin hf htf hl ha hes hts hta hbv hfb hin' 
         htr hteq cp cge fctx bctx ce cvm fctx' bctx' g g' i' hp H hm.
  have [htr1 htr2] := trans_expr_expr_ind.
  move: (htr1 (App e' es t) fctx bctx ce fctx' bctx' g g' i' H)=> [] g1 [] i1 [] i2 [] ce' [] fctx1 [] bctx1
  [] ces [] fctx2 [] bctx2 [] he' [] hes' [] h1 [] h2 h3; subst.
  move: (hin cp cge fctx bctx ce' cvm fctx1 bctx1 g g1 i1 hp he' hm)=> [] tr1 hce'.
  move: (hts cp cge fctx1 bctx1 ces cvm fctx2 bctx2 g1 g' i2 hp hes' hm)=> [] tr2 hces'.
  have hmp := transf_program_match p cp hp. case: hmp=> hmp1 hmp2.
  case: hmp1=> hpl [] hpmain hppublic.*) admit.
(* ref *)
+ admit.
(* deref *) (* done *)
+ move=> p vm m e m' l ofs v he hin hd cp cge fctx bctx ce cvm fctx' bctx' g g' i' ff hp H hwf hsf.
  have [htr1 htr2] := trans_expr_expr_ind.
  move: (htr1 (Prim Deref [:: e] (typeof_expr e)) fctx bctx ce fctx' bctx' g g' i' H)=> [] ces [] g1 [] i1 [] htes hceq; subst.
  have [ce [g2 [i2 [he' heq]]]] := trans_exprs_to_trans_expr e fctx bctx g ces fctx' bctx' g1 i1 htes. 
  have [hs1 hs2] := trans_expr_preserves_fnctx_subset. move: (hs1 e fctx bctx ce fctx' bctx' g g2 i2 he' ff)=> hsf'.
  move: (hin cp cge fctx bctx ce cvm fctx' bctx' g g2 i2 ff hp he' hwf hsf)=> [] tr hce. rewrite -heq.
  inversion hd; subst. exists tr. inversion hce; subst. 
  apply eval_expression_intro with (Evalof (Csyntax.Ederef a' (transBeePL_type (typeof_expr e))) (transBeePL_type (typeof_expr e))).
  + apply eval_valof.
    + by apply H1.
    + apply eval_deref.
    subst. apply H4. apply esr_rvalof with l ofs Full.
    + apply esl_deref. by apply H5.
    + by auto.
    by apply H1.
  have := deref_addr_translated cge (typeof_expr e) m' l ofs Full v (transBeePL_type (typeof_expr e)) (trans_bvalue_cvalue v) hd erefl erefl.  case hc: (chunk_for_volatile_type (transBeePL_type (typeof_expr e)) Full)=> [c | ] //=.
  move=> [] tr' [] _ hvo. by rewrite /chunk_for_volatile_type H1 /= in hc.
(* massgn *)
+ admit.
(* uop *) (* done *)
+ move=> p vm m e v uop m' v' ct v'' hse hin he huop hv cp cge fctx bctx ce cvm fctx' bctx' g g' i' ff hp hte hwf hsf.
  have [htr1 htr2] := trans_expr_expr_ind.
  move: (htr1 (Prim (Uop uop) [:: e] (typeof_expr e)) fctx bctx ce fctx' bctx' g g' i' hte)=> [] ces [] g1 [] i1 [] htes h1; subst.
  have [ce [g2 [i2 [hce h]]]] := trans_exprs_to_trans_expr e fctx bctx g ces fctx' bctx' g1 i1 htes; subst.
  move: (hin cp cge fctx bctx (hd default_expr (exprlist_list_expr ces)) cvm fctx' bctx' g g2 i2 ff hp hce hwf hsf)=> [] tr he.
  inversion he; subst.
  exists tr. apply eval_expression_intro with 
             (Csyntax.Eunop uop a' (transBeePL_type (typeof_expr e))).
  + rewrite /=. apply eval_unop. by apply H.
  apply esr_unop with (trans_bvalue_cvalue v). + by apply H0.
  have htce := compilation_preserve_type e fctx bctx (hd default_expr (exprlist_list_expr ces)) fctx' bctx' g g2 i2 hce.
  have := c_eval_expr_type_preservation (convert_to_rval (hd default_expr (exprlist_list_expr ces))) cge cvm m a' tr m' H=> hteq.
  have hteq' := convert_rval_type_eq (hd default_expr (exprlist_list_expr ces)); subst.
  rewrite hteq' in hteq. have := sem_equiv_uop uop v e m' v' v'' fctx bctx 
                                  (hd default_expr (exprlist_list_expr ces)) fctx' bctx' g g2 i2 huop hce hv.
  by rewrite hteq.
(* bop *)
+ admit.
  admit.
(* cast *) (* done *)
+ move=> p vm m e m' v t2 v' v'' he hin hc hv cp cge fctx bctx ce cvm fctx' bctx' g g' i' ff hp hte hwf hsf.
  have [htr1 htr2] := trans_expr_expr_ind.
  move: (htr1 (Prim (Cast t2) [:: e] t2) fctx bctx ce fctx' bctx' g g' i' hte)=> [] ces [] g1 [] i1 [] htes heq; subst.
  have [ce [g2 [i2 [hce h]]]] := trans_exprs_to_trans_expr e fctx bctx g ces fctx' bctx' g1 i1 htes; subst.
  move: (hin cp cge fctx bctx (hd default_expr (exprlist_list_expr ces)) cvm fctx' bctx' g g2 i2 ff hp hce hwf hsf)=> [] tr hces.
  inversion hces; subst.
  exists tr. apply eval_expression_intro with (Csyntax.Ecast a' (transBeePL_type t2)).
  + apply eval_cast. by apply H.
  apply esr_cast with (trans_bvalue_cvalue v).
  + by apply H0. have htce := compilation_preserve_type e fctx bctx (hd default_expr (exprlist_list_expr ces)) fctx' bctx' g g2 i2 hce; subst.
  have hteq := c_eval_expr_type_preservation (convert_to_rval (hd default_expr (exprlist_list_expr ces))) cge cvm m a' tr m' H; subst.
  have hteq' := convert_rval_type_eq (hd default_expr (exprlist_list_expr ces)); subst. rewrite hteq' in hteq.
  rewrite -htce in hteq. rewrite -hteq.
  have := sem_equiv_cast v e (transBeePL_type t2) m' v' fctx bctx g (hd default_expr (exprlist_list_expr ces)) fctx' bctx' g2 i2 v'' hc hce hv.
  by rewrite htce.
(* bind x != _ *) (* done *)
+ move=> bge' p vm m x e1 m' m'' m''' v e2 l v' tx he1 hin1 hx hxt hvo hca ha he2 hin2 cp cge fctx bctx 
         ce cvm fctx' bctx' g g' i' ff hp hte hwf hsf.
  have [htr1 htr2] := trans_expr_expr_ind.
  move: (htr1 (Bind x tx e1 e2 (typeof_expr e2)) fctx bctx ce fctx' bctx' g g' i' hte); subst. 
  rewrite /ident_of_string /=. case: ifP=> //= hx'. 
  move=> [] ce1 [] fctx1 [] bctx1 [] g1 [] i1 [] ce2 [] g2 [] i2 [] hce1 [] hce2 heq /=; subst.
  move: (hin1 cp cge fctx bctx ce1 cvm fctx1 bctx1 g g1 i1 ff hp hce1 hwf hsf)=> [] tr1 hc1.
  have := assign_addr_translated bge' cge tx m' l Ptrofs.zero Full v m'' (transBeePL_type tx) 
            (trans_bvalue_cvalue v) v (trans_bvalue_cvalue v) ha erefl erefl erefl. 
  rewrite hvo /=. move=> hca'. have [h1 h2] := trans_expr_preserves_wf_env vm cvm. 
  move: (h1 e1 fctx bctx ce1 fctx1 bctx1 g g1 i1 hwf hce1)=> hwf'.
  move: (hin2 cp cge fctx1 bctx1 ce2 cvm fctx' bctx' 
           g1 g2 i2 ff hp hce2 hwf' hsf)=> [] tr3 hc2. 
  inversion hc1; subst; inversion hc2; subst. exists ((Events.E0 ++ tr1 ++ Events.E0) ++ tr3).
  apply eval_expression_intro with a'0.
  + apply eval_comma with m'' 
      (Eval (trans_bvalue_cvalue v) (transBeePL_type tx)) (trans_bvalue_cvalue v).
      + apply eval_assign with m (Csyntax.Evar x (transBeePL_type tx)) m' a'
                                l Ptrofs.zero Full 
         (trans_bvalue_cvalue v) (trans_bvalue_cvalue v).
        + by apply eval_var.
        + by apply H.
        + apply esl_var_local. inversion hwf'; subst.
          have hcm := equiv_local_benv_cenv vm cvm x l tx (transBeePL_type tx) H3. 
          by move: (hcm erefl hxt).
        + by apply H0.
        + have ht1 := compilation_preserve_type e1 fctx bctx ce1 fctx1 bctx1 g g1 i1 hce1.
          have -> := convert_rval_type_eq ce1. by rewrite -ht1 /=. 
        by apply hca'.
      + by auto.
      + by apply esr_val.
      + by apply H1.
      + have htce2 := compilation_preserve_type e2 fctx1 
                      bctx1 ce2 fctx' bctx' g1 g2 i2 hce2. 
        by have -> := convert_rval_type_eq ce2.
      by apply H2. 
(* binc x = _ *) (* bind as seq *) (* done *)
+ move=> p vm m x e1 m' m'' v e2 v' tx he1 hin1 hx he2 hin2 cp cge fctx bctx ce cvm fctx' bctx' g g' i' ff hp hte hwf hsf.
  have [htr1 htr2] := trans_expr_expr_ind.
  move: (htr1 (Bind x tx e1 e2 (typeof_expr e2)) fctx bctx ce fctx' bctx' g g' i' hte). 
  rewrite /ident_of_string /=. case: ifP=> //= hx'.  
  move=> [] ce1 [] fctx1 [] bctx1 [] g1 [] i1 [] ce2 [] g2 [] i2 [] hce1 [] hce2.
  move: (hin1 cp cge fctx bctx ce1 cvm fctx1 bctx1 g g1 i1 ff hp hce1 hwf hsf)=> [] tr1 hce3; subst.
  have hwf' := trans_expr_preserves_wf_env. move: (hwf' vm cvm)=> [] hwf1 hwf2.
  move: (hwf1 e1 fctx bctx ce1 fctx1 bctx1 g g1 i1 hwf hce1)=> hwf1'.
  have [hs1 hs2] := trans_expr_preserves_fnctx_subset. rewrite /fctx_fresh_in_ff in hsf. 
  move: (hsf e1 fctx bctx g ce1 fctx1 bctx1 g1 i1 hce1)=> [] hf1 hf2.
  move: (hsf e2 fctx1 bctx1 g1 ce2 fctx' 
          bctx' g2 i2 hce2)=> [] hf3 hf4 heq; subst.
  move: (hin2 cp cge fctx1 bctx1 ce2 cvm fctx' bctx' g1 g2 i2 ff hp hce2 hwf1' hsf)=> [] tr2 hce4; subst.
  exists (tr1 ++ tr2). rewrite /=. inversion hce3; subst. inversion hce4; subst.
  apply eval_expression_intro with a'0.
  + apply eval_comma with m' a' (trans_bvalue_cvalue v); auto.
  have ht := compilation_preserve_type e2 fctx1 bctx1 ce2 fctx' bctx' g1 g2 i2 hce2.  
  have -> := convert_rval_type_eq ce2. by rewrite ht.
  by apply H2. by rewrite hx in hx'.
(* cond *) (* done *)
+ move=> p vm m e1 e2 e3 t m' vb ct1 v' v v'' m'' he1 hin1 ht1 hb he2 hin2 hs hv cp cge fctx bctx ce
         cvm fctx' bctx' g g' i' ff hp he hwf hsf.
  have [htr1 htr2] := trans_expr_expr_ind.
  move: (htr1 (Cond e1 e2 e3 t) fctx bctx ce fctx' bctx' g g' i' he)=> [] ce1 [] fctx1 [] bctx1 [] g1 [] i1 [] ce2 [] fctx2 [] bctx2 [] g2 [] i2
  [] ce3 [] g3 [] i3 [] hte1 [] hte2 [] hte3 heq; subst. 
  move: (hin1 cp cge fctx bctx ce1 cvm fctx1 bctx1 g g1 i1 ff hp hte1 hwf hsf)=> [] tr1 hve1.
  have hwf' := trans_expr_preserves_wf_env. move: (hwf' vm cvm)=> [] hwf1 hwf2.
  move: (hwf1 e1 fctx bctx ce1 fctx1 bctx1 g g1 i1 hwf hte1)=> hwf1'.
  move: (hin2 cp cge fctx1 bctx1 ce2 cvm fctx2 bctx2 g1 g2 i2 ff hp hte2 hwf1' hsf)=> [] tr2 hve2.
  (* true *)
  + inversion hve1; subst.  inversion hve2; subst. exists (tr1 ++ tr2). apply eval_expression_intro with (Eval v'' (transBeePL_type t)).
    + rewrite /=. apply eval_condition with m' a' (trans_bvalue_cvalue vb) a'0 (trans_bvalue_cvalue v') true; auto.
      + have hteq := compilation_preserve_type e1 fctx bctx ce1 fctx1 bctx1 g g1 i1 hte1. 
        have hteq' := convert_rval_type_eq ce1. rewrite -hteq' in hteq. by rewrite hteq in hb.
        have hteq'' := compilation_preserve_type e2 fctx1 bctx1 ce2 fctx2 bctx2 g1 g2 i2 hte2.
        have hteq3 := convert_rval_type_eq ce2. rewrite hteq3 -hteq'' /=. by apply hs.
    have -> := bv_cv_reflex v'' v hv. by apply esr_val.
  (* false *)
  + move=> p vm m e1 e2 e3 t m' vb ct1 v' v v'' m'' he1 hin1 ht1 hb he2 hin2 hs hv cp cge fctx bctx ce
         cvm fctx' bctx' g g' i' ff hp he hwf hsf.
  have [htr1 htr2] := trans_expr_expr_ind.
  move: (htr1 (Cond e1 e2 e3 t) fctx bctx ce fctx' bctx' g g' i' he)=> 
  [] ce1 [] fctx1 [] bctx1 [] g1 [] i1 [] ce2 [] fctx2 [] bctx2 [] g2 [] i2
  [] ce3 [] g3 [] i3 [] hte1 [] hte2 [] hte3 heq; subst.
  move: (hin1 cp cge fctx bctx ce1 cvm fctx1 bctx1 g g1 i1 ff hp hte1 hwf hsf)=> [] tr1 hve1.
  have hwf' := trans_expr_preserves_wf_env. move: (hwf' vm cvm)=> [] hwf1 hwf2.
  move: (hwf1 e1 fctx bctx ce1 fctx1 bctx1 g g1 i1 hwf hte1)=> hwf1'.
  move: (hwf1 e2 fctx1 bctx1 ce2 fctx2 bctx2 g1 g2 i2 hwf1' hte2)=> hwf2'.
  move: (hin2 cp cge fctx2 bctx2 ce3 cvm fctx' bctx' g2 g3 i3 ff hp hte3 hwf2' hsf)=> [] tr3 hve3.
  inversion hve1; subst.  inversion hve3; subst. exists (tr1 ++ tr3). apply eval_expression_intro with (Eval v'' (transBeePL_type t)).
  + rewrite /=. apply eval_condition with m' a' (trans_bvalue_cvalue vb) a'0 (trans_bvalue_cvalue v') false; auto.
    + have hteq := compilation_preserve_type e1 fctx bctx ce1 fctx1 bctx1 g g1 i1 hte1. 
      have hteq' := convert_rval_type_eq ce1. rewrite -hteq' in hteq. by rewrite hteq in hb.
      have hteq'' := compilation_preserve_type e3 fctx2 bctx2 ce3 fctx' bctx' g2 g3 i3 hte3.
      have hteq3 := convert_rval_type_eq ce3. rewrite hteq3 -hteq'' /=.
    by apply hs. 
  have -> := bv_cv_reflex v'' v hv. by apply esr_val.
(* unit *)
+ move=> p vm m cp cge fctx bctx ce cvm fctx' bctx' g g' i' ff hp hte hwf hsf.
  rewrite /=. admit.
(* sinit *)
+ 
Admitted.

Lemma trans_expr_st_ind: forall bcmp e fctx bctx (ct:Csyntax.statement) f b g g' i',
transBeePL_expr_st bcmp e fctx bctx g = Res (ct, f, b) g' i' ->
match e with
| Val v t => ct = Csyntax.Sreturn (Some (Eval (trans_bvalue_cvalue v) (transBeePL_type t)))
             /\ f = fctx /\ b = bctx
| Var x t => ct = Csyntax.Sreturn (Some (Evalof (Csyntax.Evar x (transBeePL_type t)) (transBeePL_type t))) 
             /\ f = fctx /\ b = bctx 
| Const (ConsInt i) t => ct = Csyntax.Sreturn (Some (Csyntax.Eval (Values.Vint i) (transBeePL_type t)))
                         /\ f = fctx /\ b = bctx 
| Const (ConsLong i) t => ct = Csyntax.Sreturn (Some (Csyntax.Eval (Values.Vlong i) (transBeePL_type t)))
                         /\ f = fctx /\ b = bctx 
| Const ConsUnit t => ct = Csyntax.Sreturn (Some (Csyntax.Eval (Values.Vint (Int.repr 0)) (transBeePL_type t)))
                      /\ f = fctx /\ b = bctx       
| Const (ConsBool bo) t => if eqb bo true 
                          then ct = Csyntax.Sreturn (Some (Csyntax.Eval (Values.Vint (Int.repr 1)) (transBeePL_type t)))
                               /\ f = fctx /\ b = bctx 
                          else ct =  Csyntax.Sreturn (Some (Csyntax.Eval (Values.Vint (Int.repr 0)) (transBeePL_type t)))
                               /\ f = fctx /\ b = bctx
| Prim Deref es t => exists ces g1 i1, 
                     transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ces, f, b) g1 i1 /\
                     ct = Csyntax.Sreturn (Some (Csyntax.Ederef (hd default_expr (exprlist_list_expr ces)) (transBeePL_type t)))
| Prim Massgn es t => exists ces g1 i1, 
                      transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ces, f, b) g1 i1 /\
                      ct = Csyntax.Sdo (Csyntax.Eassign (Csyntax.Ederef (hd default_expr (exprlist_list_expr ces)) 
                                                             (Csyntax.typeof (hd default_expr (exprlist_list_expr ces)))) 
                                                (hd default_expr (tl (exprlist_list_expr ces)))
                                                (transBeePL_type t))
| Prim (Uop o) es t => exists ces g1 i1,
                       transBeePL_expr_exprs transBeePL_expr_expr es fctx bctx g = Res (ces, f, b) g1 i1 /\
                        ct = Csyntax.Sreturn (Some (Csyntax.Eunop o 
                                     (hd default_expr (exprlist_list_expr ces)) 
                                     (transBeePL_type t)))
| _ => True
end.
Proof.
Admitted.

Definition convert_stmt_rvals (s : Csyntax.statement) : Csyntax.statement  :=
  match s with
  | Csyntax.Sreturn (Some a) => Csyntax.Sreturn (Some (convert_to_rval a))
  | _ => s
  end.

(***** Comparing BeePL big-step semantics with Csyntax big-step semantics *****)
(*
  As in the expression-level correctness proof, we must reconcile BeePL’s
  rvalue-only semantics with Csyntax’s distinction between lvalues and rvalues.
  The compiler may generate return statements whose expression is an lvalue
  (e.g., Ederef a t). Such expressions cannot be evaluated directly by
  eval_expression and must be wrapped in Evalof.

  The function convert_stmt_rvals applies convert_to_rval to the return
  expression of a statement, ensuring that returns are evaluated as rvalues.
  This lets us state the statement-level correctness theorem without changing
  the compiler, while preserving the intended semantics.
*)
Lemma bsem_csem_stmt_equiv (e : BeePL.expr) : 
forall bge cge bp cp bcmp fctx bctx bvm m m' bvm' bv ct cvm fctx' bctx' g g' i' fctxf,
BeePL_compcert bp = OK cp ->
bsem_expr bge bp bvm m e m' bvm' bv ->
transBeePL_expr_st bcmp e fctx bctx g = Res (ct, fctx', bctx') g' i'  ->
match_env bvm cvm ->
wf_env bvm cvm fctx ->
fctx_fresh_in_ff fctxf ->
exists o tr, exec_stmt cge cvm m (convert_stmt_rvals ct) tr m' o.
Proof.
move=> bge cge bp cp bcmp fctx bctx bvm m m' bvm' bv ct cvm fctx' bctx' g g' i' fctxf hp.
move=> he hte hm hwf hf.
(* We need to not simplify all defs at a time as it makes the proof slower *)
Local Opaque transBeePL_expr_st transBeePL_type trans_bvalue_cvalue ret. 
elim: e he hte=> //=.
(* val *) (* done *)
+ move=> v t he hte. inversion he; subst. 
  have := trans_expr_st_ind bcmp (Val bv t) fctx bctx ct fctx' bctx' g g' i' hte.
  move=> [] h1 h2; subst. exists (Out_return (Some((trans_bvalue_cvalue bv), (transBeePL_type t)))).
  exists Events.E0.
  apply exec_Sreturn_some. apply eval_expression_intro with (Eval (trans_bvalue_cvalue bv) (transBeePL_type t)).
  + by apply eval_val.
  by apply esr_val.
(* var *) (* done *)
+ move=> x t he hte. 
  have := trans_expr_st_ind bcmp (Var x t) fctx bctx ct fctx' bctx' g g' i' hte. 
  move=> [] h1 h2; subst. inversion he; subst. inversion H8; subst.
  (* local *)
  + exists (Out_return (Some((trans_bvalue_cvalue bv), (transBeePL_type t)))). exists  Events.E0.
    apply exec_Sreturn_some. 
    apply eval_expression_intro with (Evalof (Csyntax.Evar x (transBeePL_type t)) (transBeePL_type t)). 
    + apply eval_valof.
      + by apply H0.
      by apply eval_var.
    apply esr_rvalof with l Ptrofs.zero Full.
    + apply esl_var_local. case: hwf=> hm1 hm2.
    by have := equiv_local_benv_cenv bvm' cvm x l t (transBeePL_type t) hm1 erefl H4.
  + by rewrite /Csyntax.typeof.
  + by apply H0.
  have := deref_addr_translated cge t m' l Ptrofs.zero Full bv (transBeePL_type t) (trans_bvalue_cvalue bv) H8 erefl erefl.
  case hc: (chunk_for_volatile_type (transBeePL_type t) Full)=> [c | ] //=.
  move=> [] tr [] _ hvo. by rewrite /chunk_for_volatile_type H0 /= in hc.
 (* global *)  
 + inversion H9; subst. 
   exists (Out_return (Some((trans_bvalue_cvalue bv), (transBeePL_type t)))). exists  Events.E0.
   apply exec_Sreturn_some. 
   apply eval_expression_intro with (Evalof (Csyntax.Evar x (transBeePL_type t)) (transBeePL_type t)). 
   + apply eval_valof.
     + by apply H0.
      by apply eval_var.
    apply esr_rvalof with l Ptrofs.zero Full.
    + apply esl_var_global. case: hwf=> hm1 hm2.
    by have := equiv_global_benv_cenv bvm' cvm x hm1 H1.
  + have hg' := symbols_preserved bge cge x. by rewrite H5 in hg'.
  + by simpl.
  + by apply H0.
  have := deref_addr_translated cge t m' l Ptrofs.zero Full bv (transBeePL_type t) (trans_bvalue_cvalue bv) H9 erefl erefl.
  case hc: (chunk_for_volatile_type (transBeePL_type t) Full)=> [c | ] //=.
  move=> [] tr [] _ hvo. by rewrite /chunk_for_volatile_type H0 /= in hc.
(* const int *) (* done *)
+ move=> c t he hte. inversion he; subst.
  have := trans_expr_st_ind bcmp (Const (ConsInt i) t) fctx bctx ct fctx' bctx' g g' i' hte.
  move=> [] h1 [] h2 h3; subst. exists (Out_return (Some((Values.Vint i), (transBeePL_type t)))). 
  exists Events.E0. apply exec_Sreturn_some. 
  apply eval_expression_intro with 
    (Csyntax.Eval (Values.Vint i) (transBeePL_type t)).
  + by apply eval_val.
  by apply esr_val.
(* const long *) (* done *)
+ inversion he; subst. have := trans_expr_st_ind bcmp (Const (ConsLong i) t) fctx bctx ct fctx' bctx' g g' i' hte.
  move=> [] h1 [] h2 h3; subst.
  exists (Out_return (Some((Values.Vlong i), (transBeePL_type t)))). 
  exists Events.E0. apply exec_Sreturn_some. 
  apply eval_expression_intro with 
    (Csyntax.Eval (Values.Vlong i) (transBeePL_type t)).
  + by apply eval_val.
  by apply esr_val.
(* const unit *) (* done *)
+ inversion he; subst. have := trans_expr_st_ind bcmp (Const (ConsUnit) Utype) fctx bctx ct fctx' bctx' g g' i' hte.
  move=> [] h1 [] h2 h3; subst.
  exists (Out_return (Some((Values.Vint (Int.repr 0)), (transBeePL_type Utype)))). 
  exists Events.E0. apply exec_Sreturn_some. 
  apply eval_expression_intro with 
    (Csyntax.Eval (Values.Vint (Int.repr 0)) (transBeePL_type Utype)).
  + by apply eval_val.
  by apply esr_val.
(* app *)
+ move=> e hin es t he hte. admit.
(* builtin *)
+ move=> [].
  (* ref *)
  + admit.
  (* deref *) (* done *)
  + move=> es t he hte. inversion he; subst.
    have := trans_expr_st_ind bcmp (Prim Deref [:: e] (typeof_expr e)) fctx bctx ct 
             fctx' bctx' g g' i' hte. move=> [] es' [] g'' [] i'' [] h3 h4; subst.  
    have := trans_exprs_to_trans_expr e fctx bctx g es' fctx' bctx' g'' i'' h3.
    move=> [] ce' [] g1 [] i1 [] /= he1 h1; subst.
    have [h1 h2] := bsem_csem_expr_equiv bge cp fctxf.
    move: (h2 bp bvm' m e m' bvm' (Vloc l ofs) cge fctx bctx 
           (hd default_expr (exprlist_list_expr es')) cvm fctx' bctx' g g1 i1 H4 hp he1 hwf hf).
    move=> [] tre hce. inversion hce; subst.
    exists (Out_return (Some((trans_bvalue_cvalue bv), (transBeePL_type (typeof_expr e))))).
    exists tre. apply exec_Sreturn_some; rewrite /=. inversion H8; subst. 
    apply eval_expression_intro with 
      (Evalof (Csyntax.Ederef a' (transBeePL_type (typeof_expr e))) (transBeePL_type (typeof_expr e))).
    + apply eval_valof.
    + by apply H2.
    + apply eval_deref.
    subst. apply H. apply esr_rvalof with l ofs Full.
    + apply esl_deref. by apply H0.
    + by auto.
    by apply H2.
  have := deref_addr_translated cge (typeof_expr e) m' l ofs Full bv (transBeePL_type (typeof_expr e)) 
            (trans_bvalue_cvalue bv) H8 erefl erefl.  
  case hc: (chunk_for_volatile_type (transBeePL_type (typeof_expr e)) Full)=> [c | ] //=.
  move=> [] tr' [] _ hvo. by rewrite /chunk_for_volatile_type H2 /= in hc.
  (* massgn *)
  + admit.
  (* uop *) (* done *)
  + move=> u es t he hte. inversion he; subst.
    have := trans_expr_st_ind bcmp (Prim (Uop u) [:: e] (typeof_expr e)) fctx bctx ct fctx' bctx' g g' i' hte.
    move=> [] es' [] g'' [] i'' [] h3 h4; subst. 
    have := trans_exprs_to_trans_expr e fctx bctx g es' fctx' bctx' g'' i'' h3.
    move=> [] ce' [] g1 [] i1 [] /= he1 h1; subst.
    have [h1 h2] := bsem_csem_expr_equiv bge cp fctxf.
    move: (h2 bp bvm' m e m' bvm' v cge fctx bctx 
           (hd default_expr (exprlist_list_expr es')) cvm fctx' bctx' g g1 i1 H2 hp he1 hwf hf).
    move=> [] tre hce. inversion hce; subst.
    exists (Out_return (Some((trans_bvalue_cvalue bv), (transBeePL_type (typeof_expr e))))).
    exists tre. apply exec_Sreturn_some; rewrite /=. 
    apply eval_expression_intro with 
             (Csyntax.Eunop u a' (transBeePL_type (typeof_expr e))).
    + rewrite /=. apply eval_unop. by apply H.
    apply esr_unop with (trans_bvalue_cvalue v). + by apply H0.
    have htce := compilation_preserve_type e fctx bctx (hd default_expr (exprlist_list_expr es')) fctx' bctx' g g1 i1 he1.
    have := c_eval_expr_type_preservation (convert_to_rval (hd default_expr (exprlist_list_expr es'))) 
              cge cvm m a' tre m' H=> hteq.
  have hteq' := convert_rval_type_eq (hd default_expr (exprlist_list_expr es')); subst.
  rewrite hteq' in hteq. have := sem_equiv_uop u v e m' v' bv fctx bctx 
                                  (hd default_expr (exprlist_list_expr es')) fctx' bctx' g g1 i1 H10 he1 H11.
  by rewrite hteq.
Admitted.


      
