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
(* With the following as an assumption*)
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

Locate Events.volatile_load.
Print eq_type. Search Mem.valid_access.
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
(* I don't think you can say that,
  At least because the only condition is that it was allocated before.
 It can still be valid after free'ing which would make dereferencing impossible*)
Lemma deref_valid_block: forall bge t m b ofs p v,
  deref_addr bge t m b ofs p v ->
  Mem.valid_block m b.
Proof.
  intros. inv H.
  -  Search Mem.valid_block. Search access_mode_type.
     simpl in H2. Search Mem.load. apply Mem.load_valid_access in H2.
     apply valid_access_valid_block2 in H2. apply H2.
  - Search Events.volatile_load. inv H2.
    + admit.
    + apply Mem.load_valid_access in H4. apply valid_access_valid_block2 in H4.
      apply H4.
  - admit. (* Will need to add an assumption for this point *)
  - admit. (* Will need to add an assumption for this point *)
  - admit.
Admitted.

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
        Search Mem.alloc. apply Mem.fresh_block_alloc in Halloc.
        apply deref_valid_block in Hderef. contradiction.
      * inv Hderef.
        -- eapply deref_addr_value; eauto.
           ++  eapply Mem.load_alloc_other with (chunk:= (transl_bchunk_cchunk chunk)) (b' :=l')  (v:=v0) in Halloc.
           rewrite <- H2 in Halloc. rewrite <- Halloc in H2. apply H2.
           simpl in *. auto.
        -- apply deref_loc_volatile with chunk tr v0; auto.
          ++ apply extract_sigma in Hballoc. subst. Print primitive_type.
             Print basic_type. admit.
        -- eapply deref_addr_reference; eauto.
        -- eapply deref_addr_copy; eauto.
    + constructor 2.
      intros x t Hx.
      destruct (H x t Hx) as [l' [v [Hvm [Heq [HSigma Hderef]]]]].
      exists l', v. repeat split; try assumption.
      * admit.
      * inv Hderef.
        -- eapply deref_addr_value; eauto.
           eapply Mem.load_alloc_other with (chunk:= (transl_bchunk_cchunk chunk)) (b' :=l') (v:=v0) in Halloc.
           rewrite <- H2 in Halloc. rewrite <- Halloc in H2. apply H2.
           simpl in H2. auto.
        -- eapply deref_loc_volatile; eauto.
           ++ admit.
        -- eapply deref_addr_reference; eauto.
        -- eapply deref_addr_copy; eauto.
  - inv Hloc. destruct H as [H1 H2].
    constructor. split.
    + intros x ofs t Hsigma.
      destruct (H1 x ofs t) as [chunk [Hvalid Hchunk]]; auto.
      -- admit.
      -- exists chunk. split; [|exact Hchunk].
      eapply Mem.valid_access_alloc_other; eauto.
     intros. destruct H. admit.
  - inv Hfun.
    constructor.
    intros l o ef te ts efs rt vs efs' Hte Heq_type Htes.
    destruct (H l o ef te ts efs rt vs efs') as [fd [Hfind [Hnorepet [Hlen [Hargs Hrt]]]]]; auto.
    admit. admit.
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

Definition get_chunk (t : type) : option bmemory_chunk :=
  match t with
  | Vtype pt => match pt with
               | Tlong _ _ => Some BMint64
               | Tint I8 Unsigned _ =>  Some BMint8unsigned
               | Tint I8 Signed _ =>  Some BMint8signed
               | Tint I16 Unsigned _ =>  Some BMint16unsigned
               | Tint I16 Signed _ =>  Some BMint16signed
               | Tbool => Some BMbool
               | _ => Some BMint32
               end
  | _ => chunk_of_type t
  end.


Print chunk_of_type.

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
  admit.
Admitted.

Lemma store_well_typed_preserve : forall cenv Gamma Sigma bge vm m b m',
store_well_typed cenv Gamma Sigma bge vm m ->
(forall v chunk t ofs, typeof_value v t /\
get_chunk t = Some chunk /\
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
      destruct H as [l' [t' [v0 [Hvm [Heq [HSigma Hderef]]]]]].
      exists l', t', v0.
      split; [exact Hvm | split; [exact Heq | split; [exact HSigma |]]].
      inv Hderef.
      * apply deref_addr_value with chunk v; eauto.
        specialize H0 with v0 chunk t' (Ptrofs.zero).  destruct H0 as [Htyv [Hchunk Hstore]]. simpl in *.
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
        simpl in *. 
Admitted.

(*
  access_mode_type (get_data_type pt) =
  By_value (transl_bchunk_cchunk chunk)
*)
(* I think we can prove this and make the well formedness definition simpler *)
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
exists v0. Search deref_loc. Print deref_loc. Locate deref_loc.
Print type_is_volatile.
apply deref_addr_value with chunk v; auto.
- induction (get_data_type pt) eqn:Eqpt; simpl in *; try congruence.
    + unfold access_mode_prim. 
      induction p eqn:Eqp. simpl in *; try congruence; try (injection H0; intros).
      subst.  auto.
    + destruct i; destruct s; injection H0; intros; subst; auto.
      injection H0; intros; subst; auto. 
unfold Mptr. Transparent Archi.ptr64. unfold Archi.ptr64.
injection H0. intros. subst. auto. 
admit.
destruct (type_is_volatile (transBeePL_type (get_data_type pt))) eqn:Eqdt; auto.
unfold type_is_volatile in Eqdt. 
apply Mem.load_valid_access in hload. admit.
eapply load_not_error in resbv. inv resbv. apply hload.
Admitted.




(* I think we can prove this and make the well formedness definition simpler *)
(* I think we can prove this and make the well formedness definition simpler *)
Lemma safe_assgn_valid_pointers : forall cenv Gamma Sigma bge vm m x ofs pt v chunk,
store_well_typed cenv Gamma Sigma bge vm m ->
PTree.get x Sigma = Some (Ptrtype pt) ->
get_chunk (get_data_type pt) = Some chunk ->
Mem.valid_access m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) Freeable ->
exists bf m', assign_addr bge (get_data_type pt) m x ofs bf v m' v /\ store_well_typed cenv Gamma Sigma bge vm m'.
Proof.
  intros. exists Full.
  assert(exists v : value, deref_addr bge (get_data_type pt) m x ofs Full v).
  apply safe_deref_valid_pointers with (Sigma := Sigma) (chunk := chunk); auto.
  apply Mem.valid_access_freeable_any with (p:= Writable) in H2.
  eapply Mem.valid_access_store with (v := trans_bvalue_cvalue v) in H2.
  destruct H2 as [m' Hstore]. exists m'. split.
  - Locate assign_addr. 

(*exists m'.
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
get_chunk t = Some chunk /\
Mem.storev (transl_bchunk_cchunk chunk) ml.1 (trans_bvalue_cvalue (Vloc ml.2 Ptrofs.zero)) v' = Some m' /\
store_well_typed cenv Gamma Sigma bge vm m'.
Proof.

(*
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
admit.*) *)  
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
+ intros. simpl in *. destruct a. Search PTree.set.
  Locate Memory.mem. Transparent Memory.mem. unfold Memory.mem in m.
  Search Mem.alloc. Search chunk_of_type.
  destruct (chunk_of_type t) eqn:EqChunktyp.
  - assert( exists (m' : Mem.mem') (b : Values.block),
         Mem.alloc m 0 (sizeof_type bge t) = (m', b)).
    apply mem_alloc_total.
    destruct H0 as [m' [b' H0]].  Search PTree.set.
  exists (PTree.set i (b', t) vm).
  exists m'. exists (PTree.set b' t Sigma).
  simpl. split.
    * Locate BeePL.alloc_variables.
      eapply BeePL.alloc_variables_con.
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
             apply H1. Search Mem.loadv. admit.
          ++ apply H6.
       ** apply deref_loc_volatile with chunk tr v; auto.
          Search Events.volatile_load. admit.
        ** apply deref_addr_reference; auto.
        ** apply deref_addr_copy; auto.
           constructor. intros.
           apply H3 in H1. destruct H1 as [l' [v' [Hvm [Hfind [HSigma Hderef]]]]].
           exists l'. exists t0. exists v'.
           split; auto. admit.
           split. auto.
           split. auto.
           admit.
   * split. destruct H2. inv H2.
     constructor.
     -- intros.
Admitted.

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
           Search bind_variables. destruct a.
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
