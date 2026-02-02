Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import compcert.common.Errors Initializersproof Cstrategy BeePL_auxlemmas Coqlib Errors Memory.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import BeePL_sem BeePL_typesystem BeePL_values BeePL_notations.

From mathcomp Require Import all_ssreflect.

Lemma cty_chunk_rel : forall (ty: Ctypes.type) chunk v,
Ctypes.access_mode ty = By_value chunk ->
Values.Val.has_type v (type_of_chunk chunk) ->
Values.Val.has_type v (typ_of_type ty).
Proof.
move=> ty chunk v ha hv. case: chunk ha hv=> //=.
(* Mbool *)
+ case: ty=> //= f a. by case: f=> //=.
(* Mint8signed *)
+ case: ty=> //= f a. by case: f=> //=.
(* Mint8unsigned *)
+ case: ty=> //= f a. by case: f=> //=.
(* Mint16signed *)
+ case: ty=> //= f a. by case: f=> //=.
(* Mint16unsigned *)
+ case: ty=> //= f a. by case: f=> //=.
(* Mint32 *)
+ case: ty=> //= f a. by case: f=> //=.
(* Mint64 *)
+ case: ty=> //= i s a. 
  + case: i=> //=.
    + by case: s=> //=.
    by case: s=> //=.
  by case: i a=> //=.
(* Mfloat32 *)
+ case: ty=> //= f s a. 
  + case: f=> //=.
    + by case: s=> //=.
    by case: s=> //=.
  by case: f a=> //=.
(* Mfloat64 *)
+ case: ty=> //= f s a. 
  + case: f=> //=.
    + by case: s=> //=.
    by case: s=> //=.
  by case: f a=> //=.
(* Many32 *)
+ case: ty=> //=.
  + move=> i s a. case: i=> //=.
    + by case: s=> //=.
    by case: s=> //=.
  move=> f a. by case: f=> //=.
case: ty=> //=. 
+ move=> i s a. case: i=> //=.
  + by case: s=> //=.
  by case: s=> //=.
move=> f. by case: f=> //=.
Qed.

(* Complete me: Easy *)
Definition store_well_typed_ext : forall cenv Gamma Sigma bge vm m x l t,
store_well_typed cenv Gamma Sigma bge vm m ->
(*(Gamma ! x = None \/ (exists t', Gamma ! x = Some t' /\ t' = t)) ->*) (* we would need this *)
store_well_typed cenv Gamma Sigma bge (PTree.set x (l, t) vm) m.
Proof.
move=> cenv Gamma Sigma bge vm m x l t hw. case: hw=> [] h1 [] h2 h3.
Admitted. 

Lemma gsnone :
  forall (vm : vmap) (x x0 l : positive)  (t : type),
    (PTree.set x (l,t) vm) ! x0 = None
    <-> (x0 <> x /\ vm ! x0 = None).
Proof.
  intros. rewrite PTree.gsspec.
  destruct (peq x0 x); split; simpl; try (intuition congruence).
Qed.

Definition store_well_typed_ext_weaker : forall cenv Gamma Sigma bge vm m x l t,
store_well_typed cenv Gamma Sigma bge vm m ->
vm ! x = None \/ (exists l' t', vm ! x = Some (l' , t') /\ l = l' /\ t = t') ->
Genv.find_symbol bge x = None -> (*Makes sure x is fresh*)
store_well_typed cenv Gamma Sigma bge (PTree.set x (l, t) vm) m.
Proof.
  intros.
  destruct H as [Hvar [Hloc Hfunc]].
  constructor.
  - inv Hvar.
    + constructor 1. intros. specialize (H x0 t0 H2).
      destruct H as [l'  [t' [v  H]]].
      exists l', t', v.
      destruct H as [Hvm [h1 [h2 h3]]].
      split; auto.
      subst.
      rewrite PTree.gsspec.
      destruct (peq x0 x).
      * destruct H0.
        +  subst. congruence.
        + subst. destruct H. destruct H. destruct H.  destruct H0.
          subst. congruence.
      * exact Hvm.
    + constructor 2. intros. specialize (H x0 t0 H2).
      destruct H as [l'  [v H]].
      exists l', v.
      destruct H as [Hvm [h1 [h2 h3]]].
      split; auto.
      rewrite PTree.gsspec.
      destruct (peq x0 x).
      *  destruct H0.
         -- subst. congruence.
         -- destruct H. destruct H.  destruct H. congruence.
      * exact Hvm.
  - split.
    + constructor. inv Hloc. intros. specialize (H x0 ofs t0 chunk).
      apply H; auto.
    + constructor. inv Hfunc.
      intros. specialize (H l0 o ef te ts efs rt vs efs' H2 H3 H4).
      destruct H as [fd H].
      exists fd.
      destruct H as [h1 [h2 [h3 [h4 h5]]]].
      auto.
Qed.

Lemma alloc_to_balloc: forall m m' b t Sigma (bge:BeePL.genv),
Mem.alloc m  0 (sizeof_type bge t) = (m', b) ->
@balloc bge Sigma m t 0 (sizeof_type bge t) = (m', b, PTree.set b t Sigma).
Proof.
move=> m m' b t Sigma bge hm /=. by rewrite /balloc /= hm /=.
Qed.

Lemma extract_sigma : forall m m' b t Sigma Sigma' (bge:BeePL.genv),
@balloc bge Sigma m t 0 (sizeof_type bge t) = (m', b, Sigma') ->
Sigma' = PTree.set b t Sigma.
Proof.
  intros. unfold balloc in H. injection H as Hm Hl HSigma. intros. subst.
  reflexivity.
Qed.

Lemma valid_access_valid_block2:
  forall m chunk b ofs p,
  Mem.valid_access m chunk b ofs p ->
  Mem.valid_block m b.
Proof.
  intros. destruct H.
  assert (Mem.perm m b ofs Cur p).
  apply H. generalize (size_chunk_pos chunk). lia.
  eauto with mem.
Qed.

Lemma deref_valid_block: forall t m b ofs addr v,
  deref_addr t m b ofs addr v ->
  Mem.valid_block m b.
Proof.
  intros. inv H.
  - simpl in H2. apply Mem.load_valid_access in H2.
     apply valid_access_valid_block2 in H2. apply H2. 
  - inv H1. simpl in *. apply Mem.load_valid_access in H6.
    apply valid_access_valid_block2 in H6. apply H6.
Qed.

(* Complete me : Easy *)
Definition store_well_typed_mem_alloc : forall cenv Gamma Sigma bge vm ty m lo hi m' b Sigma',
store_well_typed cenv Gamma Sigma bge vm m ->
balloc bge Sigma m ty lo hi = (m', b, Sigma') ->
store_well_typed cenv Gamma Sigma' bge vm m'.
Proof.
  intros cenv Gamma Sigma bge vm ty m lo hi m' b Sigma' Hst Hballoc.
  unfold store_well_typed in *.
  destruct Hst as [Hvar [Hloc Hfun]].
  assert (Halloc: Mem.alloc m 0 (sizeof_type bge ty) = (m', b)).
  unfold balloc in Hballoc. inversion Hballoc as [[Hm Hl]]; subst. auto.
  split; [|split].
  - destruct Hvar.
    + constructor.
      intros x t Hx.
      destruct (H x t Hx) as [l' [t' [v [Hvm [Heq [HSigma Hderef]]]]]]. subst.
      exists l', t', v. repeat split; try assumption.
      * apply extract_sigma in Hballoc. subst.  rewrite <- HSigma.
        apply PTree.gso. intro. subst.
        apply Mem.fresh_block_alloc in Halloc.
        apply deref_valid_block in Hderef. contradiction.
      * inv Hderef.
        -- eapply deref_addr_value; eauto.
           ++  eapply Mem.load_alloc_other with (chunk:= (transl_bchunk_cchunk chunk)) (b' :=l')  (v:=v0) in Halloc.
           rewrite <- H2 in Halloc. rewrite <- Halloc in H2. apply H2.
           simpl in *. auto.
    + constructor 2.
      intros x t Hx.
      destruct (H x t Hx) as [l' [v [Hvm [Heq [HSigma Hderef]]]]].
      exists l', v. repeat split; try assumption.
      * apply extract_sigma in Hballoc. subst. rewrite <-  HSigma.
        apply PTree.gso.  intro.  subst. apply Mem.fresh_block_alloc in Halloc.
        apply deref_valid_block in Hderef. contradiction.
      * inv Hderef.
        -- eapply deref_addr_value; eauto.
           eapply Mem.load_alloc_other with (chunk:= (transl_bchunk_cchunk chunk)) (b' :=l') (v:=v0) in Halloc.
           rewrite <- H2 in Halloc. rewrite <- Halloc in H2. apply H2.
           simpl in H2. auto.
  - inv Hloc. 
    constructor.  
    inv Hballoc. intros. simpl in H0.
    unfold balloc in H0.
(* Property about balloc in
Use offset properties  instead of compcert lemmas.

    simpl.
    intros.
    specialize (H x ofs t chunk).
    Print Mem.valid_access_alloc_other.
    eapply Mem.valid_access_alloc_other in Halloc.
    apply Halloc. apply H; auto.
    assert(HSigma: Sigma' = PTree.set b ty Sigma).
    apply extract_sigma in Hballoc; auto.
    rewrite HSigma in H0.
    destruct (peq x b).
    subst.

    apply PTree.gso with (j := b) (x := ty) (m := Sigma) in n.
    rewrite <- n; auto.*) admit.
  - inv Hfun.
    constructor.
    intros l o ef te ts efs rt v vs efs' Hte Heq_type Htes.
    destruct (H l o ef te ts efs rt v vs efs') as [fd [Hfind [Hnorepet [Hlen [Hargs Hrt]]]]]; auto.
    apply extract_sigma in Hballoc. subst. inv Hte. constructor.
    destruct (Pos.eq_dec l b) as [Heq | Hneq]; subst.
    + rewrite PTree.gss in H7.  rewrite <- H7. injection H7.
      intros. subst. (*Consider ty_valloc*)
      admit.
    + eapply PTree.gso with (x := ty) (m := Sigma) in Hneq.
      symmetry. rewrite  <- H7. auto.
    (*induction on vs but this doesn't make sense*)
    apply extract_sigma in Hballoc. subst. inv Htes.
    + constructor.
    + admit. (*constructor.*)
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
(* busted definition *)
(*
Definition sizetype (env : bcomposite_env) (t : BeeTypes.type) : Z :=
   match t with
   | Vtype pt => match pt with
                | Tbool | Tint _ _ _ => 4
                | Tlong _ _ => 8
                end
   | t => sizeof_type env t
   end.
*)

Definition get_chunk (t : type) : option bmemory_chunk :=
  match t with
  | Vtype pt => match pt with
               | Tlong _ _ => Some BMint64
               | Tint I8 Unsigned _ =>  Some BMint8unsigned
               | Tint I8 Signed _ =>  Some BMint8signed
               | Tint IBool _ _ => Some BMint8unsigned
               | Tint I16 Unsigned _ =>  Some BMint16unsigned
               | Tint I16 Signed _ =>  Some BMint16signed
               | Tbool => Some BMbool
               | _ => Some BMint32
               end
  | _ => chunk_of_type t
  end.


Lemma chunk_fits_allocation_st : forall p t chunk,
Archi.ptr64 = true ->
get_chunk t = Some chunk ->
sizeof_type (prog_comp_env p) t = size_chunk (transl_bchunk_cchunk chunk).
Proof.
  intros. induction t; try inv H0.
  induction p0; try inv H2.
  simpl; lia. 
  induction i; induction s; try inv H1; simpl; try lia.
  simpl. lia.
  simpl. rewrite H.
  (* change Bytes to 8
                        Change Ftype to Mint64
                        Don't use C definitions as a guide for BeePL definitions
                      *)
  lia.
Qed.                                  

Lemma storev_succeeds_on_fresh_alloc : forall m chunk v sz,
let (m1, b) := Mem.alloc m 0 sz in
size_chunk  (transl_bchunk_cchunk chunk) = sz ->
exists m', Mem.storev  (transl_bchunk_cchunk chunk) m1 (Values.Vptr b Ptrofs.zero) v = Some m'.
Proof.
  intros.
  destruct (Mem.alloc m 0 sz) as [m1 b] eqn:Ealloc.
  intros Hsize.
  assert (Hvalid: Mem.valid_access m1 (transl_bchunk_cchunk chunk) b 0 Writable).
  {
    apply Mem.valid_access_alloc_same with (chunk := (transl_bchunk_cchunk chunk)) (ofs := 0) in Ealloc.
    apply Mem.valid_access_freeable_any with (p := Writable) in Ealloc. eauto. lia. lia.
    apply Z.divide_0_r.
  }
simpl. eapply Mem.valid_access_store with (v := v) in Hvalid.
destruct Hvalid. exists x. apply e.
Qed.

Lemma store_well_typed_preserve : forall cenv Gamma Sigma bge vm m chunk b v t m',
store_well_typed cenv Gamma Sigma bge vm m ->
typeof_value v t ->
chunk_of_type t = Some chunk ->
Mem.storev (transl_bchunk_cchunk chunk) m (Values.Vptr b Ptrofs.zero) (trans_bvalue_cvalue v) = Some m' ->
store_well_typed cenv Gamma Sigma bge vm m'.
Proof.
Admitted.

Lemma store_well_typed_preserve_gc : forall cenv Gamma Sigma bge vm m b m' v chunk t ofs,
store_well_typed cenv Gamma Sigma bge vm m ->
typeof_value v t /\
get_chunk t = Some chunk /\
Mem.storev (transl_bchunk_cchunk chunk) m (Values.Vptr b ofs) (trans_bvalue_cvalue v) = Some m' ->
store_well_typed cenv Gamma Sigma bge vm m'.
Proof.
  (*intros cenv Gamma Sigma bge vm m chunk b t m' Hwt Htyv Hchunk Hstore.*)
  intros.
  destruct H as [Hvar [Hloc Hfunc]].
  split; [| split].
  - inv Hvar.
    + constructor 1.
      intros x t0 HGamma.
      specialize (H x t0 HGamma).
      destruct H as [l' [t' [v0 [Hvm [Heq [HSigma Hderef]]]]]].
      exists l', t', v0.
      split; [exact Hvm | split; [exact Heq | split; [exact HSigma |]]].
      inv Hderef.
      * (*  apply deref_addr_value with chunk v; eauto.
        specialize H0 with v0 chunk t' (Ptrofs.zero).  destruct H0 as [Htyv [Hchunk Hstore]]. simpl in *.
        apply Mem.load_store_same in Hstore. simpl in Hstore.*)
        (*
        apply Mem.load_store_other with (chunk' := (transl_bchunk_cchunk chunk)) (b' := l') (ofs' := Ptrofs.unsigned (Ptrofs.zero)) in Hstore.
        rewrite Hstore. exact H2.
        left. simpl in *. intro. subst.
        assert(Hload2: Mem.load (transl_bchunk_cchunk chunk) m' b (Ptrofs.unsigned Ptrofs.zero) =
           Some
             (Values.Val.load_result (transl_bchunk_cchunk chunk) (trans_bvalue_cvalue v0))).
        eapply Mem.load_store_same in Hstore. auto.
        assert (Hv: trans_bvalue_cvalue v0 = v).
        apply bv_cv_reflex. auto. rewrite Hv in Hstore Hload2.
        assert (Hht: Values.Val.has_type v (type_of_chunk (transl_bchunk_cchunk chunk))).
        eapply Mem.load_type. apply H2.
        assert (Hval: (Values.Val.load_result (transl_bchunk_cchunk chunk) v) = v).
        apply Values.Val.load_result_same in Hht.
        simpl in *.  rewrite <- Hht. f_equal. *)
Admitted.

Lemma safe_deref_valid_pointers : forall Sigma m x ofs pt chunk, 
PTree.get x Sigma = Some pt ->
chunk_of_type (get_data_type pt) = Some chunk ->
Mem.valid_access m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) Freeable ->
exists v, deref_addr (get_data_type pt) m x ofs Full v. 
Proof.
(*Mem.valid_access_freeable_any*)
(*have [v hload] := Mem.valid_access_load m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) hl. 
eexists. apply deref_addr_value with chunk v.*)
Admitted.


(* I think we can prove this and make the well formedness definition simpler *)
Lemma safe_assgn_valid_pointers : forall cenv Gamma Sigma bge vm m x ofs pt v chunk, 
store_well_typed cenv Gamma Sigma bge vm m ->
PTree.get x Sigma = Some pt ->
chunk_of_type pt = Some chunk ->
Mem.valid_access m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) Freeable ->
exists bf m', assign_addr bge pt m x ofs bf v m' v /\ store_well_typed cenv Gamma Sigma bge vm m'.
Proof.
move=> cenv Sigma bge vm m x ofs h bt a hs hv. 
Admitted.


(* type mismatch in sigma and value
 valid access not given.
Undefined should not be possible since variables must be defined in BeePL
 *)
Lemma load_not_error :
  forall v e c m x ofs,
    trans_cvalue_bvalue v = Errors.Error e ->
    Mem.load (transl_bchunk_cchunk c) m x ofs = Some v ->
    False.
Proof.
  intros.
induction v; try inv H.
  - admit.
  - apply Mem.load_type in H0. simpl in H0. destruct c; simpl in H0; try inv H0.
  - apply Mem.load_type in H0. simpl in H0. destruct c; simpl in H0; try inv H0.
Admitted.

(* I think we can prove this and make the well formedness definition simpler *)
Lemma safe_deref_valid_pointers_gc : forall Sigma m x ofs pt chunk,
PTree.get x Sigma = Some pt ->
get_chunk pt = Some chunk ->
type_is_volatile (transBeePL_type pt) = false ->
Mem.valid_access m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) Freeable ->
exists (v : value), deref_addr pt m x ofs Full v.
Proof.
intros.
apply Mem.valid_access_freeable_any with (p:= Readable) in H2.
have [v hload] := Mem.valid_access_load m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) H2.
destruct (trans_cvalue_bvalue (v : Values.val)) eqn:resbv.
exists v0. 
apply deref_addr_value with chunk v; auto. 
- induction pt eqn:Eqpt; simpl in *; try congruence.  
    + unfold access_mode_prim. 
      induction p eqn:Eqp. simpl in *; try congruence; try (injection H0; intros).
      subst.  auto.
    + destruct i; destruct s; injection H0; intros; subst; auto.
      simpl.
      injection H0; intros; subst; auto. 
injection H0. intros. unfold Mptr. Transparent Archi.ptr64. unfold Archi.ptr64.
injection H0. intros. subst. auto.
eapply load_not_error in resbv. inv resbv. apply hload. 
Qed.
       
(* I think we can prove this and make the well formedness definition simpler *)
Lemma safe_assgn_valid_pointers_gc : forall cenv Gamma Sigma bge vm m x ofs pt v chunk,
store_well_typed cenv Gamma Sigma bge vm m ->
PTree.get x Sigma = Some pt ->
get_chunk pt = Some chunk ->
type_is_volatile (transBeePL_type pt) = false ->
Mem.valid_access m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) Freeable ->
exists bf m', assign_addr bge pt m x ofs bf v m' v /\ store_well_typed cenv Gamma Sigma bge vm m'.
Proof.
intros. exists Full.
assert(Hderef: exists v : value, deref_addr pt m x ofs Full v).
apply safe_deref_valid_pointers_gc with (Sigma := Sigma) (chunk := chunk); auto.
  apply Mem.valid_access_freeable_any with (p:= Writable) in H3.
  eapply Mem.valid_access_store with (v := trans_bvalue_cvalue v) in H3.
  destruct H3 as [m' Hstore]. exists m'.
  split. 
  induction pt; simpl in *; try (injection H1; intros; subst; simpl in * ); try inv H1.
  induction p.
  - injection H4. intros. apply assign_addr_value with (chunk := BMbool) (v := (trans_bvalue_cvalue v)); simpl; subst; auto.
    apply bc_cv_comp.
    + induction i; induction s; simpl in *; injection H4; intros; subst.
      apply assign_addr_value with (chunk := BMint8signed) (v := (trans_bvalue_cvalue v)); simpl; subst; auto.
      apply bc_cv_comp.
      apply assign_addr_value with (chunk := BMint8unsigned) (v := (trans_bvalue_cvalue v)); simpl; subst; auto.
      apply bc_cv_comp.
      apply assign_addr_value with (chunk := BMint16signed) (v := (trans_bvalue_cvalue v)); simpl; subst; auto.
      apply bc_cv_comp.
      apply assign_addr_value with (chunk := BMint16unsigned) (v := (trans_bvalue_cvalue v)); simpl; subst; auto.
      apply bc_cv_comp.
      apply assign_addr_value with (chunk := BMint32) (v := (trans_bvalue_cvalue v)); simpl; subst; auto.
      apply bc_cv_comp.
      apply assign_addr_value with (chunk := BMint32) (v := (trans_bvalue_cvalue v)); simpl; subst; auto.
      apply bc_cv_comp.
      apply assign_addr_value with (chunk := BMint8unsigned) (v := (trans_bvalue_cvalue v)); simpl; subst; auto.
      apply bc_cv_comp.
      apply assign_addr_value with (chunk := BMint8unsigned) (v := (trans_bvalue_cvalue v)); simpl; subst; auto.
      apply bc_cv_comp.
      apply assign_addr_value with (chunk := BMint64) (v := (trans_bvalue_cvalue v)); simpl; subst; auto.
      injection H4; intros; subst; auto.
      apply bc_cv_comp.
      apply assign_addr_value with (chunk := BMint64) (v := (trans_bvalue_cvalue v)); simpl; subst; auto.
      apply bc_cv_comp.
  - 
    simpl in Hstore. 
    apply store_well_typed_preserve_gc with (b := x) (m' := m') (v := v) (chunk := chunk) (t := pt) (ofs := ofs) in H.
    apply H. split.
    apply Mem.load_store_same in Hstore.
    apply Mem.load_type in Hstore.
    (* Values.Val.load_result_type:
  forall (chunk : memory_chunk) (v : Values.val),
  Values.Val.has_type (Values.Val.load_result chunk v)
    (type_of_chunk chunk) *)
    (* Assume next step would be to create a lemma relating
     Values.Val.has_type with typeof_value.*)
    simpl in *.
    eapply type_rel_typeof_val.
    
    (* Use both H1 and Hstore to derive conclusion *)
    admit.
    split. auto.
    auto.
Admitted.

Lemma balloc_to_alloc: forall m m' b t Sigma (bge:BeePL.genv),
@balloc bge Sigma m t 0 (sizeof_type bge t) = (m', b, PTree.set b t Sigma) ->
Mem.alloc m  0 (sizeof_type bge t) = (m', b).
Proof.
move=> m m' b t Sigma bge hm /=.
unfold balloc in hm. inv hm. inv H2.
simpl. auto.
Qed.


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
  have hs : size_chunk (transl_bchunk_cchunk chunk) <= sizeof_type (p.(prog_comp_env)) t.
Admitted.

(*
(* Allocation through ref should be successful in getting space in memory and storing value v to it *)
(* Not true, if t = Utype and v = Vunit then typeof_value v t holds but chunk_of_type t = None *)
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
  have hs : size_chunk (transl_bchunk_cchunk chunk) = sizeof_type (p.(prog_comp_env)) t.
  admit.
  have [m' hms] := storev_succeeds_on_fresh_alloc m chunk v' (sizeof_type (p.(prog_comp_env)) t) hs.
  exists m'. exists chunk. exists v'. split=> //=; split=> //=; split=> //=.
  + assert (b = Mem.nextblock m).
    {
      injection ha; intros; auto.
    }
    subst b.
    assert (H: m1 = {|
      Mem.mem_contents := PMap.set (Mem.nextblock m) (ZMap.init Undef) (Mem.mem_contents m);
      Mem.mem_access := PMap.set (Mem.nextblock m)
        (fun ofs : Z => fun=> (if zle 0 ofs && zlt ofs (sizeof_type (prog_comp_env p) t)
                                 then Some Freeable else None)) (Mem.mem_access m);
      Mem.nextblock := Pos.succ (Mem.nextblock m);
      Mem.access_max := fun b => [eta Memory.Mem.alloc_obligation_1 m 0 (sizeof_type (prog_comp_env p) t) b];
      Mem.nextblock_noaccess := fun b ofs k => [eta Memory.Mem.alloc_obligation_2 m 0 (sizeof_type (prog_comp_env p) t) b ofs k];
      Mem.contents_default := [eta Memory.Mem.alloc_obligation_3 m]
    |}).
    {
      injection ha; intros; subst. 
      apply Mem.mkmem_ext. auto. auto. auto.
    }
Admitted.
*)


(* Either

A) only allocate primitive values and fit in 32/16 bit chunks
B) model initialize memory (need to iterate over all fields i.e. multiple stores/ field)

type preservation lemma typesystem_proofs.
In the ref case
in the massign case

 *)

(* Allocation through ref should be successful in getting space in memory and storing value v to it *)
(* Not true, if t = Utype and v = Vunit then typeof_value v t holds but chunk_of_type t = None *)
Lemma ref_allocation_succeeds_gc : forall cenv Gamma Sigma ml b Sigma' (p : BeePL.program) (bge : BeePL.genv) (vm : vmap)
(m : Memory.mem) (v : BeePL_values.value) (t : type),
store_well_typed cenv Gamma Sigma bge vm m ->
typeof_value v t ->
balloc bge Sigma m t 0 (sizeof_type p.(prog_comp_env) t) = (ml, b, Sigma') ->
exists m' chunk v',
trans_bvalue_cvalue v = v' /\
get_chunk t = Some chunk /\
Mem.storev (transl_bchunk_cchunk chunk) ml (trans_bvalue_cvalue (Vloc b Ptrofs.zero)) v' = Some m' /\
store_well_typed cenv Gamma Sigma' bge vm m'.
Proof.
intros. rename H into he. rename H0 into ht. rename H1 into ha.
case hc: (get_chunk t)=> [chunk | ] //=.
+ set (v' := trans_bvalue_cvalue v).
  have hs : sizeof_type (p.(prog_comp_env)) t = size_chunk (transl_bchunk_cchunk chunk). 
  apply chunk_fits_allocation_st; auto. symmetry in hs.
  have [m' hms] := storev_succeeds_on_fresh_alloc m chunk v' (sizeof_type (p.(prog_comp_env)) t) hs.
  exists m'. exists chunk. exists v'. split=> //=; split=> //=; split=> //=.
  + assert (b = Mem.nextblock m).
    {
      injection ha; intros; auto.
    }
    subst b.
    assert (H: ml = {|
      Mem.mem_contents := PMap.set (Mem.nextblock m) (ZMap.init Undef) (Mem.mem_contents m);
      Mem.mem_access := PMap.set (Mem.nextblock m)
        (fun ofs : Z => fun=> (if zle 0 ofs && zlt ofs (sizeof_type (prog_comp_env p) t)
                                 then Some Freeable else None)) (Mem.mem_access m);
      Mem.nextblock := Pos.succ (Mem.nextblock m);
      Mem.access_max := fun b => [eta Memory.Mem.alloc_obligation_1 m 0 (sizeof_type (prog_comp_env p) t) b];
      Mem.nextblock_noaccess := fun b ofs k => [eta Memory.Mem.alloc_obligation_2 m 0 (sizeof_type (prog_comp_env p) t) b ofs k];
      Mem.contents_default := [eta Memory.Mem.alloc_obligation_3 m]
    |}).
    {
      injection ha; intros; subst; inv ha.
    (* If we use chunk_fits_allocation_st which only works with defined sizetype
       sizeof_type comes from definition of balloc
       *)
      apply Mem.mkmem_ext; auto. (*Set Printing All.*)
      (*assert (BeePL.genv_cenv bge = (prog_comp_env p)).*)
      admit.
    }
    rewrite <- H in hms.
    unfold Mem.storev in hms.
    rewrite Ptrofs.unsigned_zero in hms.
    exact hms.
    assert (Hm1_wt: store_well_typed cenv Gamma Sigma' bge vm ml).
    {
      apply (store_well_typed_mem_alloc cenv Gamma Sigma bge vm t m 0 (sizeof_type (prog_comp_env p) t) ml b).
      - exact he.
      - exact ha.
    }
  apply (store_well_typed_preserve_gc cenv Gamma Sigma' bge vm ml b m' v chunk t Ptrofs.zero).
  - exact Hm1_wt.
  - split. exact ht.
  - split. exact hc.
  - assert (b = Mem.nextblock m).
    {
      injection ha; intros; auto.
    }
    subst b.
    assert (H: ml = {|
      Mem.mem_contents := PMap.set (Mem.nextblock m) (ZMap.init Undef) (Mem.mem_contents m);
      Mem.mem_access := PMap.set (Mem.nextblock m)
        (fun ofs : Z => fun=> (if zle 0 ofs && zlt ofs (sizeof_type (prog_comp_env p) t)
                                 then Some Freeable else None)) (Mem.mem_access m);
      Mem.nextblock := Pos.succ (Mem.nextblock m);
      Mem.access_max := fun b => [eta Memory.Mem.alloc_obligation_1 m 0 (sizeof_type (prog_comp_env p) t) b];
      Mem.nextblock_noaccess := fun b ofs k => [eta Memory.Mem.alloc_obligation_2 m 0 (sizeof_type (prog_comp_env p) t) b ofs k];
      Mem.contents_default := [eta Memory.Mem.alloc_obligation_3 m]
    |}).
    {
      injection ha; intros; subst.
      apply Mem.mkmem_ext; auto. admit.
    }
    rewrite <- H in hms.
    exact hms.
+ 
  (*Change defn of chunk_of_type for None to BMany64*)
  (* Change lemma to bge in balloc *)
Admitted.


Lemma alloc_variables_wf : forall cenv Gamma Sigma bge vm m vars,
store_well_typed cenv Gamma Sigma bge vm m ->
list_norepet vars ->
exists vm' m' Sigma', BeePL.alloc_variables bge Sigma vm m vars vm' m' Sigma' 
/\ store_well_typed cenv Gamma Sigma bge vm' m'.
Proof.
move=> cenv Gamma Sigma bge vm m vars hw hl. move: vm m hw. elim: vars hl=> //=.
+ intros. exists vm, m, Sigma. split. constructor.
+ auto.
+ intros. simpl in *. destruct a. 
  Transparent Memory.mem. unfold Memory.mem in m.
  destruct (chunk_of_type t) eqn:EqChunktyp.
  - assert( exists (m' : Mem.mem') (b : Values.block),
         Mem.alloc m 0 (sizeof_type bge t) = (m', b)).
    apply mem_alloc_total.
    destruct H0 as [m' [b' H0]]. 
  exists (PTree.set i (b', t) vm).
  exists m'. exists (PTree.set b' t Sigma).
  simpl. split.
    * eapply BeePL.alloc_variables_con.
      -- apply alloc_to_balloc with (Sigma := Sigma) in H0.
         apply H0.
      -- admit.
   * inv hw. constructor.
     -- inv H1.
        ** constructor.
           intros. specialize H3 with x t0.
           apply H3 in H1. destruct H1 as [l' [t' [v' [Hvm [Hteq [HSig Hderef]]]]]].
           exists l'. exists t'. exists v'.
           repeat (split; auto).
          ++ rewrite <- Hvm. eapply PTree.gso. intro. subst.
              admit. (* Contradiction hl and Hvm *)
          ++ inv Hderef. eapply deref_addr_value; auto.
             apply H1.  admit.
          ++ apply H6.
       ** Admitted.

Lemma bind_variables_wf : forall cenv Gamma Sigma bge vm m args vs,
store_well_typed cenv Gamma Sigma bge vm m ->
length args = length vs ->
exists m', bind_variables bge vm m args vs m' /\ store_well_typed cenv Gamma Sigma bge vm m'.
Proof.
  intros. generalize dependent vs.
  exists m. split.
  - inv H. inv H1.
    + generalize dependent vs. induction args. induction vs.
      * constructor 1.
      * intros; inv H0.
      * induction vs.
        -- intros; inv H0.
        -- intros; simpl in *.
           assert ((Datatypes.length args) = (Datatypes.length vs)).
           lia. apply IHargs in H1.  
           destruct a.
           eapply bind_variables_cons.
           ++ admit.
           ++ admit.
           ++ apply H1.
  - generalize dependent vs. induction args; induction vs.
    + intros. apply bind_variables_nil.
    + intros. inv H0.
    + intros. inv H0.
    + intros. destruct a. eapply bind_variables_cons.
      * admit.
      * admit.
      * simpl in H0. assert ((Datatypes.length args) = (Datatypes.length vs)).
       lia. apply IHargs in H1.  apply H1.
  - apply H.
Admitted.
