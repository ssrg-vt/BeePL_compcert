Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import compcert.common.Errors Initializersproof Cstrategy BeePL_auxlemmas Coqlib Errors Memory.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import BeePL_sem BeePL_typesystem BeePL_compiler_proofs BeePL_values BeePL_notations.

From mathcomp Require Import all_ssreflect.

Lemma cty_chunk_rel : forall (ty: Ctypes.type) chunk v,
Ctypes.access_mode ty = By_value chunk ->
Values.Val.has_type v (type_of_chunk chunk) ->
Values.Val.has_type v (typ_of_type ty).
Proof.
  intros ty chunk v ha hv.
  destruct chunk; simpl in *.
  (* Mbool *)
  - induction ty; intros; try discriminate; auto.
    destruct f; discriminate.
    injection ha as contra.
    unfold Mptr in contra.
    destruct Archi.ptr64 eqn:Eptr; discriminate.
  (* Mint8signed *)
  - induction ty; intros; try discriminate; auto.
    destruct f; discriminate.
    injection ha as contra.
    unfold Mptr in contra.
    destruct Archi.ptr64 eqn:Eptr; discriminate.
  - induction ty; intros; try discriminate; auto.
    destruct f; discriminate.
    injection ha as contra.
    unfold Mptr in contra.
    destruct Archi.ptr64 eqn:Eptr; discriminate.
  - induction ty; intros; try discriminate; auto.
    destruct f; discriminate.
    injection ha as contra.
    unfold Mptr in contra.
    destruct Archi.ptr64 eqn:Eptr; discriminate.
- induction ty; intros; try discriminate; auto.
    destruct f; discriminate.
    injection ha as contra.
    unfold Mptr in contra.
    destruct Archi.ptr64 eqn:Eptr; discriminate.
  - induction ty; intros; try discriminate; auto.
    destruct f eqn:Ef; try discriminate.
    injection ha as contra.
    unfold Mptr in contra.
    destruct Archi.ptr64 eqn:Eptr; try discriminate.
    simpl. unfold Tptr. rewrite Eptr. auto.
  - induction ty; intros; try discriminate; auto.
    destruct i; destruct s; discriminate.
    destruct f; discriminate.
    injection ha as contra.
    unfold Mptr in contra.
    destruct Archi.ptr64 eqn:Eptr; try discriminate.
    simpl. unfold Tptr. rewrite Eptr. auto.
  - induction ty; intros; try discriminate; auto.
    destruct i; destruct s; discriminate.
    destruct f; try discriminate; auto.
    injection ha as contra.
    unfold Mptr in contra.
    destruct Archi.ptr64 eqn:Eptr; discriminate.
  - induction ty; intros; try discriminate; auto.
    destruct i; destruct s; discriminate.
    destruct f; try discriminate; auto.
    injection ha as contra.
    unfold Mptr in contra.
    destruct Archi.ptr64 eqn:Eptr; discriminate.
  - induction ty; intros; try discriminate; auto.
    destruct i; destruct s; discriminate.
    destruct f eqn:Ef; try discriminate.
    injection ha as contra.
    unfold Mptr in contra.
    destruct Archi.ptr64 eqn:Eptr; try discriminate.
  - induction ty; intros; try discriminate; auto.
    destruct i; destruct s; discriminate.
    destruct f eqn:Ef; try discriminate.
    injection ha as contra.
    unfold Mptr in contra.
    destruct Archi.ptr64 eqn:Eptr; try discriminate.
Qed.

(* Complete me: Easy *)
Definition store_well_typed_ext : forall cenv Gamma Sigma bge vm m x l t,
store_well_typed cenv Gamma Sigma bge vm m ->
(* don't think this is actually necessary *)
(*(Gamma ! x = None \/ (exists t', Gamma ! x = Some t' /\ t' = t)) ->*) (* we would need this *)
store_well_typed cenv Gamma Sigma bge (PTree.set x (l, t) vm) m.
Proof.
  intros.
  destruct H as [Hvar [Hloc Hfunc]].
  constructor.
  - inv Hvar.
    + constructor 1. intros. specialize (H x0 t0 H0).
      destruct H as [l'  [t' [v [ofs H]]]].
      exists l', t', v, ofs.
      destruct H as [Hvm [h1 [h2 h3]]].
      split; auto.
      subst.
      rewrite PTree.gsspec.
      destruct (peq x0 x).
      * subst. admit.
      * exact Hvm.
    + constructor 2. intros. specialize (H x0 t0 H0).
      destruct H as [l'  [ofs [v H]]].
      exists l', ofs, v.
      destruct H as [Hvm [h1 [h2 h3]]].
      split; auto.
      rewrite PTree.gsspec.
      destruct (peq x0 x).
      * admit.
      * exact Hvm.
  - split.
    + constructor. inv Hloc.
      intros. specialize (H x0 ofs t0 H0).
      destruct H as [chunk [h1 h2]].
      exists chunk.
      auto.
    + constructor. inv Hfunc.
      intros. specialize (H l0 o ef te ts efs rt vs efs' H0 H1 H2).
      destruct H as [fd H].
      exists fd.
      destruct H as [h1 [h2 [h3 [h4 h5]]]].
      auto.
Admitted.   

(* Complete me : Easy *)
Definition store_well_typed_mem_alloc : forall cenv Gamma Sigma bge vm m lo hi m' b,
store_well_typed cenv Gamma Sigma bge vm m ->
Mem.alloc m lo hi = (m', b) ->
store_well_typed cenv Gamma Sigma bge vm m'.
Proof.
  intros cenv Gamma Sigma bge vm m lo hi m' b Hst Halloc.
  unfold store_well_typed in *.
  destruct Hst as [Hvar [Hloc Hfun]].
  split; [|split].
  - destruct Hvar.
    + constructor.
      intros x t Hx.
      destruct (H x t Hx) as [l' [t' [v [ofs [Hvm [Heq [HSigma Hderef]]]]]]].
      exists l', t', v, ofs.
      split; [exact Hvm|].
      split; [exact Heq|].
      split; [exact HSigma|].
      inv Hderef.
      * eapply deref_addr_value; eauto.
        admit.
      * eapply deref_addr_reference; eauto.
      * eapply deref_addr_copy; eauto.
    + constructor 2.
      intros x t Hx.
      destruct (H x t Hx) as [l' [ofs [v [Hvm [Heq [HSigma Hderef]]]]]].
      exists l', ofs, v.
      split; [exact Hvm|].
      split; [exact Heq|].
      split; [exact HSigma|].
      inv Hderef.
      * eapply deref_addr_value; eauto.
        admit.
      * eapply deref_addr_reference; eauto.
      * eapply deref_addr_copy; eauto.
  - inv Hloc.
    constructor.
    intros x ofs t [HSigma Hvolatile].
    destruct (H x ofs t) as [chunk [Hvalid Hchunk]]; auto.
    exists chunk.
    split; [|exact Hchunk].
    eapply Mem.valid_access_alloc_other; eauto.
  - inv Hfun.
    constructor.
    intros l o ef te ts efs rt vs efs' Hte Heq_type Htes.
    destruct (H l o ef te ts efs rt vs efs') as [fd [Hfind [Hnorepet [Hlen [Hargs Hrt]]]]]; auto.
    exists fd.
    split; [exact Hfind|].
    split; [exact Hnorepet|].
    split; [exact Hlen|].
    split; [exact Hargs|].
    exact Hrt.
Admitted.
 
Lemma mem_alloc_total :
forall m lo hi, exists m' b, Mem.alloc m lo hi = (m', b).
Proof.
intros. destruct (Mem.alloc m lo hi) as [m' b]. eauto.
Qed.

Lemma chunk_fits_allocation : forall p t chunk,
Archi.ptr64 = true ->
chunk_of_type t = Some chunk ->
size_chunk (transl_bchunk_cchunk chunk) <= sizeof_type (prog_comp_env p) t.
Proof.
move=> p t chunk harch. case: t=> [| | | | pt | ptr | bt] //=.
+ move=> pr. case: pr=> //=. 
  + by case: chunk=> //=.
  + move=> sz s a. by case: sz=> //=; case: s=> //=; case: chunk=> //=. 
  move=> s a. by case: chunk=> //=.
move=> ptr. rewrite harch. by case: chunk=> //=.
Qed.

Lemma storev_succeeds_on_fresh_alloc : forall m chunk v sz,
let (m1, b) := Mem.alloc m 0 sz in
size_chunk  (transl_bchunk_cchunk chunk) <= sz ->
exists m', Mem.storev  (transl_bchunk_cchunk chunk) m1 (Values.Vptr b Ptrofs.zero) v = Some m'.
Proof.
  intros.
  destruct (Mem.alloc m 0 sz) as [m1 b] eqn:Ealloc.
  intros Hsize.
  assert (Hvalid: Mem.valid_access m1 (transl_bchunk_cchunk chunk) b 0 Writable).
  {
    admit.
  }
Admitted.

Lemma store_well_typed_preserve : forall cenv Gamma Sigma bge vm m chunk b v t m',
store_well_typed cenv Gamma Sigma bge vm m ->
typeof_value v t ->
chunk_of_type t = Some chunk ->
Mem.storev (transl_bchunk_cchunk chunk) m (Values.Vptr b Ptrofs.zero) (trans_bvalue_cvalue v) = Some m' ->
store_well_typed cenv Gamma Sigma bge vm m'.
Proof.
  intros cenv Gamma Sigma bge vm m chunk b v t m' Hwt Htyv Hchunk Hstore.
  destruct Hwt as [Hvar [Hloc Hfunc]].
  split; [| split].
  - inv Hvar.
    + constructor 1. 
      intros x t0 HGamma.
      specialize (H x t0 HGamma).
      destruct H as [l' [t' [v0 [ofs [Hvm [Heq [HSigma Hderef]]]]]]].
      exists l', t', v0, ofs.
      split; [exact Hvm | split; [exact Heq | split; [exact HSigma |]]].
      inv Hderef.
      * eapply deref_addr_value; eauto.
        admit.
      * eapply deref_addr_reference; eauto.
      * eapply deref_addr_copy; eauto.
    + constructor 2. intros x t0 HGamma.
      specialize (H x t0 HGamma).
      destruct H as [l' [ofs [v0 [Hvm [Hfind [HSigma Hderef]]]]]].
      exists l', ofs, v0.
      split; [exact Hvm | split; [exact Hfind | split; [exact HSigma |]]].
      admit.
  - inv Hloc.
    constructor.
    intros x ofs t0 [HSigma Hvolatile].
    specialize (H x ofs t0 (conj HSigma Hvolatile)).
    destruct H as [chunk' [Hvalid Hchunk']].
    exists chunk'.
    split; [| exact Hchunk'].
    eapply Mem.store_valid_access_1; eauto.
  - inv Hfunc.
    constructor.
    intros l o ef te ts efs rt vs efs' Htype Heqtype Htypes.
    specialize (H l o ef te ts efs rt vs efs' Htype Heqtype Htypes).
    exact H.      
Admitted.

(* I think we can prove this and make the well formedness definition simpler *)
Lemma safe_deref_valid_pointers : forall Sigma m x ofs pt chunk, 
PTree.get x Sigma = Some (Ptrtype pt) ->
chunk_of_type (get_data_type pt) = Some chunk ->
Mem.valid_access m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) Freeable ->
exists v, deref_addr (get_data_type pt) m x ofs Full v. 
Proof.
move=> Sigma m x ofs pt chunk hs htv hc hl. 
(*Mem.valid_access_freeable_any*)
(*have [v hload] := Mem.valid_access_load m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) hl. 
eexists. apply deref_addr_value with chunk v.*)
Admitted.


(* I think we can prove this and make the well formedness definition simpler *)
Lemma safe_assgn_valid_pointers : forall cenv Gamma Sigma bge vm m x ofs pt v chunk, 
store_well_typed cenv Gamma Sigma bge vm m ->
PTree.get x Sigma = Some (Ptrtype pt) ->
chunk_of_type (get_data_type pt) = Some chunk ->
Mem.valid_access m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) Freeable ->
exists bf m', assign_addr bge (get_data_type pt) m x ofs bf v m' v /\ store_well_typed cenv Gamma Sigma bge vm m'.
Proof.
move=> cenv Sigma bge vm m x ofs h bt a hs hv. 
Admitted.

(* Allocation through ref should be successful in getting space in memory and storing value v to it *)
Lemma ref_allocation_succeeds : forall cenv Gamma Sigma (p : BeePL.program) (bge : BeePL.genv) (vm : vmap) 
(m : Memory.mem) (v : BeePL_values.value) (t : type) ml,
store_well_typed cenv Gamma Sigma bge vm m ->
typeof_value v t ->
Mem.alloc m 0 (sizeof_type p.(prog_comp_env) t) = ml ->
exists m' chunk v', 
trans_bvalue_cvalue v = v' /\
chunk_of_type t = Some chunk /\
Mem.storev (transl_bchunk_cchunk chunk) ml.1 (trans_bvalue_cvalue (Vloc ml.2 Ptrofs.zero)) v' = Some m' /\
store_well_typed cenv Gamma Sigma bge vm m'. 
Proof.
move=> cenv Gamma Sigma p bge vm m v t [m1 b] he ht ha.
case hc: (chunk_of_type t)=> [chunk | ] //=.
+ set (v' := trans_bvalue_cvalue v).
  have hs : size_chunk (transl_bchunk_cchunk chunk) <= sizeof_type (p.(prog_comp_env)) t. + by apply chunk_fits_allocation.
  have [m' hms] := storev_succeeds_on_fresh_alloc m chunk v' (sizeof_type (p.(prog_comp_env)) t) hs.
  exists m'. exists chunk. exists v'. split=> //=; split=> //=; split=> //=.
  + admit.
  admit.
admit.
Admitted.

Lemma alloc_variables_wf : forall cenv Gamma Sigma bge vm m vars,
store_well_typed cenv Gamma Sigma bge vm m ->
list_norepet vars ->
exists vm' m', BeePL.alloc_variables bge vm m vars vm' m' /\ store_well_typed cenv Gamma Sigma bge vm' m'.
Proof.
move=> cenv Gamma Sigma bge vm m vars hw hl. move: vm m hw. elim: vars hl=> //=.
+ move=> hl vm m. exists vm, m. split=> //=. by apply BeePL.alloc_variables_nil.
move=> [x t] xts hi hl vm m. inversion hl; subst. have [m' [l hm hw']] := mem_alloc_total m 0 (sizeof_type bge t).
have hw'' := store_well_typed_mem_alloc cenv Gamma Sigma bge vm m 0 (sizeof_type bge t) m' l hw' hm.
have hw''' := store_well_typed_ext cenv Gamma Sigma bge vm m' x l t hw''.
move: (hi H2  (PTree.set x (l, t) vm) m' hw''') => [] vm' [] m'' [] ha hw1.
exists vm', m''. split=> //=. apply BeePL.alloc_variables_con with m' l.
+ by apply hm. by apply ha.
Qed.

Lemma bind_variables_wf : forall cenv Gamma Sigma bge vm m args vs,
store_well_typed cenv Gamma Sigma bge vm m ->
length args = length vs ->
exists m', bind_variables bge vm m args vs m' /\ store_well_typed cenv Gamma Sigma bge vm m'.
Proof.
  intros.
Admitted.
