Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import compcert.common.Errors Initializersproof Cstrategy BeePL_auxlemmas Coqlib Errors Memory.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import BeePL_sem BeePL_typesystem BeePL_safety BeePL_typesystem_proofs.

From mathcomp Require Import all_ssreflect.

(*Lemma no_divergence_fnbody : forall p efs,
type_program p ->
accumulate_effect_progs p = OK efs ->
no_divergence efs.
Proof.
move=> p efs htp. inversion htp; subst.
inversion H1; subst.
+ rewrite -H5 /= in H1. inversion H1; subst.
  rewrite /accumulate_effect_progs /= -H5 /=. by move=> [] <-.
rewrite /accumulate_effect_progs /= -H /=. 
case hgef : (accumulate_effect_gd g) => [efg | ] //=.
case hgefs : (accumulate_effect_gds)=> [efgs | ] //=.  move=> [] heq; subst.
rewrite -H /= in H1 H0 H6. inversion H1; subst.
inversion H9; subst.
+ inversion H3; subst.
  (* internal *)
  + inversion H4; subst. rewrite /accumulate_effect_gd /accumulate_effect_fundef in hgef. 
    case: hgef=> [] h; subst. elim: (BeePL.fn_body fn) H5=> //=.
    + move=> v t hte. inversion  *)

(****** No divergence effect ********)
Lemma no_divergence_type_system :
(forall cenv Gamma Sigma es efs ts, 
 type_exprs cenv Gamma Sigma es efs ts ->
 no_divergence efs) /\
(forall cenv Gamma Sigma e ef t, 
 type_expr cenv Gamma Sigma e ef t ->
 no_divergence ef).
Proof.
suff : (forall cenv Gamma Sigma es efs ts, 
 type_exprs cenv Gamma Sigma es efs ts ->
 no_divergence efs) /\
(forall cenv Gamma Sigma e ef t, 
 type_expr cenv Gamma Sigma e ef t ->
 no_divergence ef).
+ move=> [] h1 h2. by split=> //=.
apply type_exprs_type_expr_ind_mut=> //=.
(* app *)
+ move=> cenv Gamma Sigma e te es rt efs ts ef efs' hte hd hteq hts hds. apply no_divergence_concat.
  + by apply hd. apply no_divergence_concat. 
  + admit.
  (* here function signature has the effect of the body also, how to ensure that there is no divergence in the effect of body *)
  by apply hds.
(* ref *)
+ move=> cenv Gamma Sigma e ef h bt a he hd. by apply no_divergence_concat.
(* deref *)
+ move=> cenv Gamma Sigma e ef h bt a he hd. by apply no_divergence_concat.
(* massgn *)
+ move=> cenv Gamma Sigma e e' h pt ef ef' hte hd1 hte' hd2. apply no_divergence_concat.
  + by apply hd1.
  by apply no_divergence_concat.
+ move=> cenv Gamma Sigma e ef1 ef2 t e' hteq hte1 hd1 hte2 hd2. by apply no_divergence_concat.
+ move=> cenv Gamma Sigma e ef1 ef2 t e' hteq hte1 hd1 hte2 hd2. by apply no_divergence_concat.
+ move=> cenv Gamma Sigma e ef1 ef2 t e' hteq hte1 hd1 hte2 hd2. by apply no_divergence_concat.
+ move=> cenv Gamma Sigma e ef1 ef2 t e' hteq hte1 hd1 hte2 hd2. by apply no_divergence_concat.
+ move=> cenv Gamma Sigma e ef1 ef2 t e' hteq hte1 hd1 hte2 hd2. by apply no_divergence_concat.
+ move=> cenv Gamma Sigma e ef1 ef2 t e' hteq hte1 hd1 hte2 hd2. by apply no_divergence_concat.
+ move=> cenv Gamma Sigma e ef1 ef2 t e' hteq hte1 hd1 hte2 hd2. by apply no_divergence_concat.
+ move=> cenv Gamma Sigma e ef1 ef2 t e' hteq hte1 hd1 hte2 hd2. by apply no_divergence_concat.
+ move=> cenv Gamma Sigma e ef1 ef2 t e' hteq hte1 hd1 hte2 hd2. by apply no_divergence_concat.
+ move=> cenv Gamma Sigma e ef1 ef2 t e' hteq hte1 hd1 hte2 hd2. by apply no_divergence_concat.
+ move=> cenv Gamma Sigma e ef1 ef2 t e' hteq hte1 hd1 hte2 hd2. by apply no_divergence_concat.
+ move=> cenv Gamma Sigma e ef1 ef2 t e' hteq hte1 hd1 hte2 hd2. by apply no_divergence_concat.
+ move=> cenv Gamma Sigma e ef1 ef2 t e' hteq hte1 hd1 hte2 hd2. by apply no_divergence_concat.
+ move=> cenv Gamma Sigma e ef1 ef2 t e' hteq hte1 hd1 hte2 hd2. by apply no_divergence_concat.
+ move=> cenv Gamma Sigma e ef1 ef2 t e' hteq hte1 hd1 hte2 hd2. by apply no_divergence_concat.
+ move=> cenv Gamma Sigma e ef1 ef2 t e' hteq hte1 hd1 hte2 hd2. by apply no_divergence_concat.
+ move=> cenv Gamma Sigma e ef1 ef2 t e' hteq hte1 hd1 hte2 hd2. by apply no_divergence_concat.
+ move=> cenv Gamma Sigma e1 e2 e3 t ef1 ef2 hte1 hd1 hte2 hd2 hte3 hd3. by apply no_divergence_concat.
+ move=> cenv Gamma Sigma e1 e2 d e ef1 t1 ef2 t2 fv1 fv2 fv ef t hte1 hd1 hte2 hd2 hte hd heq hil hfv1 hfv2
         hfv hdis1 hdis2. apply no_divergence_concat. + by apply hd1. + by apply no_divergence_concat.
+ move=> cenv Gamma Sigma e ef te ps es efs ts fvs hg hte hd htes hds ho ha. by apply no_divergence_concat.
move=> cenv Gamma Sigma e es ef efs t ts hte hd htes hds. by apply no_divergence_concat.
Admitted.

Lemma lift_ref_closure : forall bge p vm m v t e h bt a m' vm' n,
(n > 0)%N ->
ssem_closure bge p vm m e n m' vm' (Val v t) ->
ssem_closure bge p vm m (Prim Ref [:: e] (Ptrtype (Reftype h bt a))) n m' vm' 
  (Prim Ref [:: Val v t] (Ptrtype (Reftype h bt a))).
Proof.
move=> bge p vm m v t e h bt a m' vm' n hn H. 
induction H as [| bge p vm m e m1 vm1 e1 Hstep
                   | bge p vm m e m1 vm1 e1 n' m2 vm2 e2 Hstep Hcl' IH].
+ by inversion hn.
+ apply ssem_one. by apply ssem_ref1. 
apply ssem_multi with m1 vm1 (Prim Ref [:: e1] (Ptrtype (Reftype h bt a))).
+ by apply ssem_ref1.
apply IH. admit.
Admitted.

(***** Termination *****)
(* A well typed program where the effects contain no divergence effect is always terminating *)
Lemma guaranteed_termination : 
(forall cenv Gamma Sigma es efs ts bge p vm m, 
 type_exprs cenv Gamma Sigma es efs ts ->
 store_well_typed cenv Gamma Sigma bge vm m ->
 exists n m' vm' vs, ssem_closures bge p vm m es n m' vm' vs /\ is_values vs /\ no_divergence efs) /\
(forall cenv Gamma Sigma e ef t bge p vm m, 
 type_expr cenv Gamma Sigma e ef t ->
 store_well_typed cenv Gamma Sigma bge vm m ->
 exists n m' vm' v, ssem_closure bge p vm m e n m' vm' v /\ is_value v /\ no_divergence ef).
Proof.
suff : (forall cenv Gamma Sigma es efs ts, 
           type_exprs cenv Gamma Sigma es efs ts ->
           forall bge p vm m, store_well_typed cenv Gamma Sigma bge vm m -> exists n m' vm' vs, 
                                                  ssem_closures bge p vm m es n m' vm' vs /\
                                                  is_values vs /\ no_divergence efs) /\
       (forall cenv Gamma Sigma e ef t, 
           type_expr cenv Gamma Sigma e ef t ->
           forall bge p vm m, store_well_typed cenv Gamma Sigma bge vm m -> exists n m' vm' v, 
                                                 ssem_closure bge p vm m e n m' vm' v /\
                                                  is_value v /\ no_divergence ef).
+ admit.
apply type_exprs_type_expr_ind_mut=> //=.
(* Val unit *)
+ move=> cenv Gamma Sigma bge p vm m. exists 0%N. exists m.
  exists vm. exists (Val BeePL_values.Vunit BeePL_notations.tunit). split=> //=.
  by apply ssem_val.
(* Val bool *)
+ move=> cenv Gamma Sigma b bge p vm m. exists 0%N. exists m.
  exists vm. exists (Val (BeePL_values.Vbool b) (Vtype Tbool)). split=> //=.
  by apply ssem_val.
(* Val int *)
+ admit. (* easy *)
(* Val long *) 
+ admit. (* easy *)
(* Val loc *)
+ admit. (* easy *)
(* Var *)
+ move=> cenv Gamma Sigma x t hx bge p vm m hw. case: hw => [] hw1 [] hw2 hw3. inversion hw1.
  + move: (H x t hx)=> [] l' [] t' [] v [] ofs [] h1 [] h2 [] h3 [] hd [] hf h; subst.
    exists 1%N. exists m. exists vm. exists (Val v t'); split=> //=. apply ssem_one.
    by apply ssem_lvar with l' ofs.
  admit. (* provable *)
(* const *)
+ admit. (* provable *)
+ admit. (* provable *)
+ admit. (* provable *)
(* app *)
+ move=> cenv Gamma Sigma e te es rt efs ts ef efs' hte hin hteq htes hin' bge p vm m hw.
  move: (hin bge p vm m hw)=> [] n [] m' [] vm' [] v [] hsf [] hv hd. inversion hsf; subst.
  + admit.
  + admit.
  admit.
(* ref *)
+ move=> cenv Gamma Sigma e ef h bt a hte hin bge p vm m hw. 
  move: (hin bge p vm m hw)=> [] n1 [] m' [] vm' [] v [] hes [] hvs hd.
  inversion hes; subst.
  + have [hp1 hp2] := progress_ssem_expr_exprs.
    have hrt : type_expr cenv Gamma Sigma (Prim Ref [:: Val v0 t] (Ptrtype (Reftype h bt a)))
     (ef ++ [:: Alloc h]) (Ptrtype (Reftype h bt a)).
    + by apply ty_ref.
    have hvt := type_rel_typeof_val cenv Gamma Sigma v0 ef t (construct_type_btype bt) hte.
    have [m'' [b] ha] := mem_alloc_total m' 0 (sizeof_type (prog_comp_env p) t).
    have hw'' := store_well_typed_mem_alloc cenv Gamma Sigma bge vm' m' 0 (sizeof_type (prog_comp_env p) t) 
                   m'' b hw ha. 
    have [m''' [] chunk [] v' [] htv [] hc [] hs hws] := ref_allocation_succeeds cenv Gamma Sigma p 
                                                          bge vm' m' v0 t (m'', b) hw hvt ha. 
    exists 1%N. exists m'''. exists vm'. exists (Val (BeePL_values.Vloc b Ptrofs.zero) (Ptrtype (Reftype h bt a))).
    split=> //=.
    + apply ssem_one. apply type_val_reflx in hte; subst.
      apply ssem_ref2 with (Mem.alloc m' 0 (sizeof_type (prog_comp_env p) (construct_type_btype bt))) chunk Sigma
             (extend_context Sigma (Mem.alloc m' 0 (sizeof_type (prog_comp_env p) (construct_type_btype bt))).2 
             (Ptrtype (Reftype h bt a))); auto.
      + rewrite ha /=. by apply hs.
      rewrite ha /=. by rewrite /extend_context.
    split=> //=. by apply no_divergence_concat.
  + case: v hes hvs H=> //= v t hes hvs H. 
    have hr := ssem_ref1 bge p vm m e m' vm' (Val v t) h bt a H. 
    have [hp1 hp2] := preservation_ssem_expr_exprs.
    move: (hp2 cenv Gamma Sigma e ef (construct_type_btype bt) bge p vm m vm' m' (Val v t) hte hw H)=> 
        [] ef' [] hvt [] hsub hw1.
    have hvt' := type_rel_typeof_val cenv Gamma Sigma v ef' t (construct_type_btype bt) hvt.
    have [m'' [b] ha] := mem_alloc_total m' 0 (sizeof_type (prog_comp_env p) t).
    have hw'' := store_well_typed_mem_alloc cenv Gamma Sigma bge vm' m' 0 (sizeof_type (prog_comp_env p) t) 
                   m'' b hw1 ha.
    have [m''' [] chunk [] v' [] htv [] hc [] hs hws] := ref_allocation_succeeds cenv Gamma Sigma p 
                                                          bge vm' m' v t (m'', b) hw1 hvt' ha.
    have hteq := type_val_reflx cenv Gamma Sigma v t ef' (construct_type_btype bt) hvt; subst. 
    eexists. exists m'''. exists vm'. exists (Val (BeePL_values.Vloc b Ptrofs.zero) (Ptrtype (Reftype h bt a))).
    split=> //=.
    + apply ssem_multi with m' vm' (Prim Ref [:: Val v (construct_type_btype bt)] (Ptrtype (Reftype h bt a))). 
      + by apply hr.
      have hr' : ssem_expr bge p vm' m' (Prim Ref [:: (Val v (construct_type_btype bt))] 
                  (Ptrtype (Reftype h bt a))) m''' vm' 
                 (Val (BeePL_values.Vloc b Ptrofs.zero) (Ptrtype (Reftype h bt a))).
  
      + by apply ssem_ref2 with (m'', b) chunk Sigma (PTree.set b (Ptrtype (Reftype h bt a)) Sigma).
    by apply ssem_one. split=> //=. by apply no_divergence_concat.
  exists (n + 1)%N. exists m'. exists vm'. exists v. split=> //=.
  + have hr := ssem_ref1 bge p vm m e m'0 vm'0 e' h bt a H.
    case: v hes hvs H H0=> //= v t hes hvs H H0. 
    have [hp1 hp2] := multi_preservation_ssem_expr_exprs.
    move: (hp2 cenv Gamma Sigma e ef (construct_type_btype bt) bge p vm m vm' m' (Val v t) 
           (n+1)%N hte hw hes)=> [] ef' [] hvt [] hsub hw'.
    have hvt' := type_rel_typeof_val cenv Gamma Sigma v ef' t (construct_type_btype bt) hvt.
    have [m'' [b] ha] := mem_alloc_total m' 0 (sizeof_type (prog_comp_env p) t).
    have hw'' := store_well_typed_mem_alloc cenv Gamma Sigma bge vm' m' 0 (sizeof_type (prog_comp_env p) t) 
                   m'' b hw' ha.
    have [m''' [] chunk [] v' [] htv [] hc [] hs hws] := ref_allocation_succeeds cenv Gamma Sigma p 
                                                          bge vm' m' v t (m'', b) hw' hvt' ha.
    have : ssem_closure bge p vm'0 m'0 (Prim Ref [:: e'] (Ptrtype (Reftype h bt a))) n m' vm'
             (Prim Ref [ :: (Val v t)] (Ptrtype (Reftype h bt a))).
    + 
    have : ssem_closure bge p vm'0 m'0 (Prim Ref [:: e'] (Ptrtype (Reftype h bt a))) n m' vm'
             (Val (BeePL_values.Vloc b Ptrofs.zero) (Ptrtype (Reftype h bt a))).
    admit.
Admitted.
