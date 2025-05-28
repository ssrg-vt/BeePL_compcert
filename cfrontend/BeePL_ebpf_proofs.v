Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import compcert.common.Errors Initializersproof Cstrategy BeePL_auxlemmas Coqlib Errors Memory.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import BeePL_sem BeePL_typesystem BeePL_safety BeePL_typesystem_proofs.

From mathcomp Require Import all_ssreflect.

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

 
(*Lemma no_divergence_sem :
(forall cenv Gamma Sigma es efs ts bge p vm m m' vm' es', 
 type_exprs cenv Gamma Sigma es efs ts ->
 ssem_exprs bge p vm m es m' vm' es' ->
 no_divergence efs) /\
(forall cenv Gamma Sigma e ef t bge p vm m m' vm' e', 
 type_expr cenv Gamma Sigma e ef t ->
 ssem_expr bge p vm m e m' vm' e' ->
 no_divergence ef).
Proof.
suff : (forall cenv Gamma Sigma es efs ts, type_exprs cenv Gamma Sigma es efs ts ->
           forall  bge p vm m m' vm' es', ssem_exprs bge p vm m es m' vm' es' ->
                                          no_divergence efs) /\
       (forall cenv Gamma Sigma e ef t, type_expr cenv Gamma Sigma e ef t ->
           forall bge p vm m m' vm' e', ssem_expr bge p vm m e m' vm' e' ->
                                        no_divergence ef).
+ admit.
apply type_exprs_type_expr_ind_mut=> //=.
(* app *)
+ admit.
(* ref *)
+ move=> cenv Gamma Sigma e ef h bt a hte hin bge p vm m m' vm' e' he.
  inversion he; subst.
  + move: (hin bge p vm m m' vm' e'0 H9)=> hd. by apply no_divergence_concat.
  have hv : ssem_expr bge p vm m (Val v (construct_type_btype bt)) m vm (Val v (construct_type_btype bt)).
  + apply ssem_value. 
    by have := typed_well_formed_value cenv Gamma Sigma v (construct_type_btype bt) ef hte.
    move: (hin bge p vm m m vm  (Val v (construct_type_btype bt)) hv)=> hd.
  by apply no_divergence_concat.
(* deref *)
+ admit.
(* massgn *)
+ admit.
(* onotbool *)
+ admit.
(* onotint *)
+ admit.
(* oneg *)
+ admit.
(* oadd *)
+ admit.
(* osub *)
+ admit.
(* omul *)
+ admit.
(* odiv *)
+ admit.
(* omod *)
+ admit.
(* oand *)
+ admit.
(* oor *)
+ admit.
(* oxor *)
+ admit.
(* oshl *)
+ admit.
(* oshr *)
+ admit.
(* oeq *)
+ admit.
(* one *)
+ admit.
(* olt *)
+ admit.
(* ogt *)
+ admit.
(* ole *)
+ admit.
(* oge *)
+ admit.
(* bind *)
+ move=> cenv Gamma Sigma x t e e' t' ef ef' hte hin hte' hin' bge p vm m m' vm' e'' he.
  inversion he; subst.
  (* step *)
  + move: (hin bge p vm m m' vm' e1' H10)=> hd1. 
    have [h1 h2] := no_divergence_type_system.
    move: (h2 cenv (extend_context Gamma x t) Sigma e' ef' (typeof_expr e') hte')=> hd2.
    by apply no_divergence_concat.
  (* value *)
   have [h1 h2] := no_divergence_type_system.
   move: (h2 cenv (extend_context Gamma x t) Sigma e' ef' (typeof_expr e') hte')=> hd2.
    
Admitted. *) 

(***** Termination *****)
(* A well typed program where the effects contain no divergence effect is always terminating *)
Lemma guaranteed_termination : 
(forall cenv Gamma Sigma es efs ts bge p vm m, 
 type_exprs cenv Gamma Sigma es efs ts ->
 store_well_typed Gamma Sigma bge vm m ->
 exists n m' vm' vs, ssem_closures bge p vm m es n m' vm' vs /\ is_values vs /\ no_divergence efs) /\
(forall cenv Gamma Sigma e ef t bge p vm m, 
 type_expr cenv Gamma Sigma e ef t ->
 store_well_typed Gamma Sigma bge vm m ->
 exists n m' vm' v, ssem_closure bge p vm m e n m' vm' v /\ is_value v /\ no_divergence ef).
Proof.
suff : (forall cenv Gamma Sigma es efs ts, 
           type_exprs cenv Gamma Sigma es efs ts ->
           forall bge p vm m, store_well_typed Gamma Sigma bge vm m -> exists n m' vm' vs, 
                                                  ssem_closures bge p vm m es n m' vm' vs /\
                                                  is_values vs /\ no_divergence efs) /\
       (forall cenv Gamma Sigma e ef t, 
           type_expr cenv Gamma Sigma e ef t ->
           forall bge p vm m, store_well_typed Gamma Sigma bge vm m -> exists n m' vm' v, 
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
+ move=> cenv Gamma Sigma x t hx bge p vm m hw. inversion hw.
  + move: (H x t hx)=> [] l' [] t' [] v [] ofs [] h1 [] h2 [] h3 [] hd [] hf h; subst.
    exists 1%N. exists m. exists vm. exists (Val v t'); split=> //=. apply ssem_one.
    by apply ssem_lvar with l' ofs. 
Admitted.
