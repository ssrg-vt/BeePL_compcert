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
  - induction ty; intros; try discriminate; auto.
    destruct f; discriminate.
  - induction ty; intros; try discriminate; auto.
    destruct f; discriminate.
  - induction ty; intros; try discriminate; auto.
    destruct f; discriminate.
  - induction ty; intros; try discriminate; auto.
    destruct f; discriminate.
  - induction ty; intros; try discriminate; auto.
    destruct f; discriminate.
  - induction ty; intros; try discriminate; auto.
    destruct f eqn:Ef; try discriminate.
  - induction ty; intros; try discriminate; auto.
    destruct i; destruct s; discriminate.
    destruct f; discriminate.
  - induction ty; intros; try discriminate; auto.
    destruct i; destruct s; discriminate.
    destruct f; try discriminate; auto.
  - induction ty; intros; try discriminate; auto.
    destruct i; destruct s; discriminate.
    destruct f; try discriminate; auto.
  - induction ty; intros; try discriminate; auto.
    destruct i; destruct s; discriminate.
    destruct f eqn:Ef; try discriminate.
  - induction ty; intros; try discriminate; auto.
    destruct i; destruct s; discriminate.
    destruct f eqn:Ef; discriminate.
Qed.

(* Local Weakening Lemma *)
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
      destruct H as [H1 H2].
      split.
      * intros.
        specialize (H1 x0 ofs t0 H).
        destruct H1 as [chunk [h1 h2]].
        exists chunk.
        auto.
      * intros.
        specialize (H2 chunk x0 ofs t0 H).
        exact H2.
    + constructor. inv Hfunc.
      intros. specialize (H l0 o ef te ts efs rt vs efs' H0 H1 H2).
      destruct H as [fd H].
      exists fd.
      destruct H as [h1 [h2 [h3 [h4 h5]]]].
      auto.
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
(* With the following as an assumption*)
  intros.
  destruct H as [Hvar [Hloc Hfunc]].
  constructor.
  - inv Hvar.
    + constructor 1. intros. specialize (H x0 t0 H2).
      destruct H as [l'  [t' [v [ofs H]]]].
      exists l', t', v, ofs.
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
      destruct H as [l'  [ofs [v H]]].
      exists l', ofs, v.
      destruct H as [Hvm [h1 [h2 h3]]].
      split; auto.
      rewrite PTree.gsspec.
      destruct (peq x0 x).
      *  destruct H0.
         -- subst. congruence.
         -- destruct H. destruct H.  destruct H. congruence.
      * exact Hvm.
  - split.
    + constructor. inv Hloc.
      destruct H as [H2 H3].
      split.
      * intros.
        specialize (H2 x0 ofs t0 H).
        destruct H2 as [chunk [h1 h2]].
        exists chunk.
        auto.
      * intros.
        specialize (H3 chunk x0 ofs t0 H).
        exact H3.
    + constructor. inv Hfunc.
      intros. specialize (H l0 o ef te ts efs rt vs efs' H2 H3 H4).
      destruct H as [fd H].
      exists fd.
      destruct H as [h1 [h2 [h3 [h4 h5]]]].
      auto.
Qed.


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
       inv H2.
       eapply Mem.load_alloc_other with (chunk:= (transl_bchunk_cchunk chunk)) (b' :=l') (ofs:= (Ptrofs.unsigned ofs)) (v:=v0) in Halloc.
       rewrite <- H5 in Halloc. apply Halloc. apply H5.
      * apply deref_loc_volatile with chunk tr v0; auto.
        inv H2.
          -- apply Events.volatile_load_vol; auto.
          -- eapply Mem.load_alloc_other with (chunk:= (transl_bchunk_cchunk chunk)) (b' :=l') (ofs:= (Ptrofs.unsigned ofs)) (v:=v0) in Halloc.
             eapply Events.volatile_load_nonvol with (m := m') (chunk := (transl_bchunk_cchunk chunk)) (ofs:= ofs) (v := v0) in H4.  (* Needs to specify ofs *)
             auto. eapply Halloc. apply H5.
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
        inv H2.
        eapply Mem.load_alloc_other with (chunk:= (transl_bchunk_cchunk chunk)) (b' :=l') (ofs:= (Ptrofs.unsigned ofs)) (v:=v0) in Halloc.
        rewrite <- H5 in Halloc. apply Halloc. apply H5.
      * apply deref_loc_volatile with chunk tr v0; auto.
        inv H2.
          -- apply Events.volatile_load_vol; auto.
          -- eapply Mem.load_alloc_other with (chunk:= (transl_bchunk_cchunk chunk)) (b' :=l') (ofs:= (Ptrofs.unsigned ofs)) (v:=v0) in Halloc.
             eapply Events.volatile_load_nonvol with (m := m') (chunk := (transl_bchunk_cchunk chunk)) (ofs:= ofs) (v := v0) in H4.
             auto. eapply Halloc. apply H5.
      * eapply deref_addr_reference; eauto.
      * eapply deref_addr_copy; eauto.
  - inv Hloc.
    destruct H as [H1 H2]. 
    constructor.
    split.
    + intros x ofs t Hsigma.
      destruct (H1 x ofs t) as [chunk [Hvalid Hchunk]]; auto.
      exists chunk.
      split; [|exact Hchunk].
      eapply Mem.valid_access_alloc_other; eauto.
    + (*  intros chunk x ofs t [Hmem' Hchunk].
       destruct (Values.eq_block x b) eqn:Eqxb. (* I become stuck here *)
       subst. exfalso.   pose proof (Mem.fresh_block_alloc m lo hi m' b Halloc) as Hfresh.
       assert (Mem.valid_block m b).
       {
         (* If Sigma ! b = Some (Ptrtype t), then H1 gives us such a valid access. *)
         specialize (H1 b ofs t). destruct (Sigma ! b) eqn:Hs; try contradiction.
         rewrite <- Hs in H1. specialize (H2 chunk b ofs t).
specialize (H2 (conj Hmem' Hchunk)).
specialize (H1 H2).
destruct H1 as (chunk0 & Hvalid_m & _).
eapply Mem.valid_access_valid_block in Hvalid_m.
contradiction.*)
       
      intros chunk x ofs t Hvalid.
      specialize (H2 chunk x ofs t).
      destruct Hvalid as [Hmem Hchunk].
      apply H2.
      split; [|exact Hchunk].
      assert (Haccess: Mem.alloc m lo hi = (m', b)). apply Halloc.
      apply Mem.valid_access_alloc_inv with (chunk:= (transl_bchunk_cchunk chunk)) (b' := x) (ofs := (Ptrofs.unsigned ofs)) (p:= Freeable) in Haccess.
      destruct (Values.eq_block x b) eqn:Eqxb. (* I become stuck here *)
      * destruct Haccess as [Hlo [Hhi Halign]]. (*Proof goal is contradictory, but can't find conflicting assumptions *)
        assert (Hvalid: Mem.valid_block m' b). apply Mem.valid_new_block with m lo hi; assumption.
        assert (Hinvalid: ~ Mem.valid_block m b). apply Mem.fresh_block_alloc with lo hi m'; assumption.
        assert (~ Mem.valid_access m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) Freeable).
        intro. apply Mem.valid_access_freeable_any with (p := Nonempty) in H. apply Mem.valid_access_valid_block in H.
        subst. congruence. Search Mem.alloc.
        assert (Hload: Mem.load (transl_bchunk_cchunk chunk) m' b (Ptrofs.unsigned ofs) = Some Values.Vundef).
        eapply Mem.load_alloc_same'. apply Halloc. auto. auto. auto. Print chunk_of_ptype.

        admit.
      * apply Haccess.
      * apply Hmem.
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



Definition sizetype (env : bcomposite_env) (t : BeeTypes.type) : Z :=
   match t with
   | Vtype pt => match pt with
                | Tbool | Tint _ _ _ => 4
                | Tlong _ _ => 8
                end
   | t => sizeof_type env t
   end.

Lemma chunk_fits_allocation : forall p t chunk,
Archi.ptr64 = true ->
chunk_of_type t = Some chunk ->
size_chunk (transl_bchunk_cchunk chunk) <= sizetype (prog_comp_env p) t.
Proof.
move=> p t chunk harch ct. induction t.
+ induction chunk; simpl in ct; try inv ct.
+ destruct p0.
  induction chunk; simpl in ct. inv ct. inv ct.
  inv ct. inv ct. inv ct. simpl; lia. inv ct.
  destruct i; destruct s; destruct a; destruct chunk;
    simpl; try lia; try (simpl in ct; inv ct).
  destruct s; destruct a; destruct chunk;
    simpl; try lia; try (simpl in ct; inv ct).
  destruct p0; destruct chunk; simpl; try lia; try (simpl in ct; inv ct); try (rewrite harch; lia).
  destruct i; destruct a; destruct chunk;
    simpl; try lia; try (simpl in ct; inv ct).
  destruct t; destruct z; destruct a; destruct chunk;
  simpl; try lia; try (simpl in ct; inv ct).
  destruct l; destruct e; destruct t; destruct chunk;
  simpl; try lia; try (simpl in ct; inv ct).
  destruct chunk;
  simpl; try lia; try (simpl in ct; inv ct).
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
    apply Mem.valid_access_alloc_same with (chunk := (transl_bchunk_cchunk chunk)) (ofs := 0) in Ealloc.
    apply Mem.valid_access_freeable_any with (p := Writable) in Ealloc. eauto. lia. lia.
    apply Z.divide_0_r.
  }
simpl. eapply Mem.valid_access_store with (v := v) in Hvalid.
destruct Hvalid. exists x. apply e.
Qed.


(*  
Lemma chunk_type_refl : forall chunk,
    AST.chunk_of_type (type_of_chunk chunk) = chunk.
Proof.
  intros. induction chunk; auto.
  - simpl. Print AST.chunk_of_type.
    (* Unprovable *)
Admitted.
*)
(*
Lemma load_result_same
  forall (v : Values.val) (ty : typ), Values.Val.has_type v ty -> Values.Val.load_result (AST.chunk_of_type ty) v = v
*)
(*perform a write in memory state [m].
  Value [v] is stored at address [b + ofs=zero]. (idk what chunk is doing here really)
*)



Lemma store_well_typed_preserve : forall cenv Gamma Sigma bge vm m b m',
store_well_typed cenv Gamma Sigma bge vm m ->
(forall v chunk t ofs, typeof_value v t /\
chunk_of_type t = Some chunk /\
Mem.storev (transl_bchunk_cchunk chunk) m (Values.Vptr b ofs) (trans_bvalue_cvalue v) = Some m') ->
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
      destruct H as [l' [t' [v0 [ofs' [Hvm [Heq [HSigma Hderef]]]]]]].
      exists l', t', v0, ofs'.
      split; [exact Hvm | split; [exact Heq | split; [exact HSigma |]]].
      inv Hderef.
      * apply deref_addr_value with chunk v; eauto.
        specialize H0 with v0 chunk t' ofs'.  destruct H0 as [Htyv [Hchunk Hstore]]. simpl in *.
        apply Mem.load_store_other with (chunk' := (transl_bchunk_cchunk chunk)) (b' := l') (ofs' := Ptrofs.unsigned ofs') in Hstore.
        rewrite Hstore. exact H2.
        left. simpl in *. intro. subst.
        assert(Hload2: Mem.load (transl_bchunk_cchunk chunk) m' b (Ptrofs.unsigned ofs') =
           Some
             (Values.Val.load_result (transl_bchunk_cchunk chunk) (trans_bvalue_cvalue v0))).
        eapply Mem.load_store_same in Hstore. auto.
        assert (Hv: trans_bvalue_cvalue v0 = v).
        apply bv_cv_reflex. auto. rewrite Hv in Hstore Hload2.
        assert (Hht: Values.Val.has_type v (type_of_chunk (transl_bchunk_cchunk chunk))).
        eapply Mem.load_type. apply H2.
        assert (Hval: (Values.Val.load_result (transl_bchunk_cchunk chunk) v) = v).
        apply Values.Val.load_result_same in Hht.
        Print AST.chunk_of_type. Print type_of_chunk.
Admitted.
Print primitive_type.
Print bmemory_chunk.
Definition get_chunk (t : type) : option bmemory_chunk :=
  match t with
  | Vtype pt => match pt with
               | Tlong _ _ => Some BMint64
               | _ => Some BMint32
               end
  | _ => chunk_of_type t
  end.


Lemma safe_deref_valid_pointers : forall bge Sigma m x ofs pt chunk,
PTree.get x Sigma = Some (Ptrtype pt) ->
get_chunk (get_data_type pt) = Some chunk ->
Mem.valid_access m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) Freeable ->
exists (v : value), deref_addr bge (get_data_type pt) m x ofs Full v.
Proof.
intros.
apply Mem.valid_access_freeable_any with (p:= Readable) in H1.
have [v hload] := Mem.valid_access_load m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) H1.
destruct (trans_cvalue_bvalue (v : Values.val)) eqn:resbv.
exists v0. apply deref_addr_value with chunk v; auto.
Print get_data_type. Print transl_bchunk_cchunk.
- inv H1.
 unfold access_mode_type.
   induction (get_data_type pt) eqn:Eqpt; simpl in *; try congruence.
    + unfold access_mode_prim. Print transl_bchunk_cchunk.
      Print chunk_of_type. Print get_data_type.
      induction p eqn:Eqp; simpl in *; try congruence; try (injection H0; intros).
      subst. simpl in *.
 
(* I think we can prove this and make the well formedness definition simpler *)
(*
Lemma safe_deref_valid_pointers : forall bge Sigma m x ofs pt chunk,
PTree.get x Sigma = Some (Ptrtype pt) ->
chunk_of_type (get_data_type pt) = Some chunk ->
Mem.valid_access m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) Freeable ->
exists (v : value), deref_addr bge (get_data_type pt) m x ofs Full v.
Proof.
intros.
apply Mem.valid_access_freeable_any with (p:= Readable) in H1.
have [v hload] := Mem.valid_access_load m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) H1.
destruct (trans_cvalue_bvalue (v : Values.val)) eqn:resbv.
exists v0. apply deref_addr_value with chunk v; auto.
-  inv H1. unfold access_mode_type.
   induction (get_data_type pt) eqn:Eqpt; simpl in *; try congruence. 
   + unfold access_mode_prim. induction p eqn:Eqp; simpl in *; try congruence; try (injection H0; intros).
     * injection H0. intros. subst. simpl in *.
       Locate By_value.
       admit.
     *  induction i; induction s; simpl in *; try congruence; try (subst; simpl; auto).
        -- admit.
        -- admit.
  + subst. auto.
  + admit.
  + unfold type_is_volatile. admit.
    induction (access_mode (transBeePL_type (get_data_type (Vptype p)))); auto. admit.
- admit.
Admitted.
(*Mem.valid_access_freeable_any*)
(*have [v hload] := Mem.valid_access_load m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) hl.
eexists. apply deref_addr_value with chunk v.*)

*)
(* [assign_addr ty m addr ofs v] returns the updated memory after storing the value v at address [addr] and offset
   [ofs] *)
Admitted.

(* I think we can prove this and make the well formedness definition simpler *)
Lemma safe_assgn_valid_pointers : forall cenv Gamma Sigma bge vm m x ofs pt v chunk,
store_well_typed cenv Gamma Sigma bge vm m ->
PTree.get x Sigma = Some (Ptrtype pt) ->
chunk_of_type (get_data_type pt) = Some chunk ->
Mem.valid_access m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) Freeable ->
exists bf m', assign_addr bge (get_data_type pt) m x ofs bf v m' v /\ store_well_typed cenv Gamma Sigma bge vm m'.
Proof.
  intros. exists Full.
  assert(exists v : value, deref_addr bge (get_data_type pt) m x ofs Full v).
  apply safe_deref_valid_pointers with (Sigma := Sigma) (chunk := chunk); auto.
  apply Mem.valid_access_freeable_any with (p:= Writable) in H2.
  eapply Mem.valid_access_store with (v := trans_bvalue_cvalue v) in H2.
  destruct H2 as [m' Hstore]. (*exists m'.
  split.
  - set (v' := trans_bvalue_cvalue v).
    apply assign_addr_value with (v := v') (chunk := chunk); auto.
    +
    + admit. *)
  (*
  Search store_well_typed. Search well_formed_loc.
  assert (Sigma ! x = Some (Ptrtype pt) ->
   exists chunk : bmemory_chunk,
     Mem.valid_access m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) Freeable /\
     chunk_of_type (get_data_type pt) = Some chunk).
  intros. destruct H4. exists chunk. split; auto.
  assert (Mem.valid_access m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) Freeable /\
   chunk_of_type (get_data_type pt) = Some chunk -> Sigma ! x = Some (Ptrtype pt)).
  intros. apply H0.
  assert ((Sigma ! x = Some (Ptrtype pt) ->
       exists chunk : bmemory_chunk,
         Mem.valid_access m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) Freeable /\
         chunk_of_type (get_data_type pt) = Some chunk) /\
            (Mem.valid_access m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) Freeable /\
       chunk_of_type (get_data_type pt) = Some chunk -> Sigma ! x = Some (Ptrtype pt))).
  auto.  assert (well_formed_loc Sigma bge vm m). apply store_well_typed_loc.
*)

(*store_well_typed_loc
  forall (Sigma : store_context) (bge : BeePL.genv) (vm : vmap) (m : Memory.mem),

  (forall (x : positive) (ofs : ptrofs) (t : ptr_type),
   Sigma ! x = Some (Ptrtype t) ->
   exists chunk : bmemory_chunk,
     Mem.valid_access m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) Freeable /\
     chunk_of_type (get_data_type t) = Some chunk)

 /\
  (forall (chunk : bmemory_chunk) (x : Values.block) (ofs : ptrofs) (t : ptr_type),
   Mem.valid_access m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) Freeable /\
   chunk_of_type (get_data_type t) = Some chunk -> Sigma ! x = Some (Ptrtype t))

 ->
  well_formed_loc Sigma bge vm m
 *)

(*move=> cenv Sigma bge vm m x ofs h bt a hs hv. intros.*)

Admitted.

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
  have hs : size_chunk (transl_bchunk_cchunk chunk) <= sizeof_type (p.(prog_comp_env)) t. (*+ by apply chunk_fits_allocation.
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
      apply Mem.mkmem_ext; auto.
    }
    rewrite <- H in hms.
    unfold Mem.storev in hms.
    rewrite Ptrofs.unsigned_zero in hms.
    exact hms.
  assert (Hm1_wt: store_well_typed cenv Gamma Sigma bge vm m1).
  {
    apply (store_well_typed_mem_alloc cenv Gamma Sigma bge vm m 0 (sizeof_type (prog_comp_env p) t) m1 b).
    - exact he.
    - exact ha.
  }
admit.*)
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
  exists m. split.
  - inv H. inv H1.
    + simpl. induction args. induction vs.
      * constructor 1.
      * inv H0.
      * induction vs.
        -- inv H0.
        -- admit.
    + admit.
  - admit.
Admitted.
