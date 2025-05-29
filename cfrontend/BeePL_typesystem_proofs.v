Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import compcert.common.Errors Initializersproof Cstrategy BeePL_auxlemmas Coqlib Errors Memory.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import BeePL_sem BeePL_typesystem BeePL_compiler_proofs BeePL_values BeePL_notations.

From mathcomp Require Import all_ssreflect.

(**** Well formedness ****)

(*** Well formed var ***)
Inductive well_formed_var (Gamma : ty_context) (Sigma : store_context) (bge : BeePL.genv) (vm : vmap) (m : Memory.mem) : Prop :=
| store_well_typed_lvar : (forall x t,
                           Gamma ! x = Some t ->
                           (exists l' t' v ofs, vm ! x = Some (l', t') /\
                           t = t' /\ PTree.get l' Sigma = Some t /\ 
                                                  deref_addr t m l' ofs Full v)) ->
                          well_formed_var Gamma Sigma bge vm m
| store_well_typed_gvar : (forall x t,
                          Gamma ! x = Some t ->
                          (exists l' ofs v, vm ! x = None /\ Genv.find_symbol bge x = Some l' /\ 
                                            PTree.get l' Sigma = Some t /\ 
                                            deref_addr t m l' ofs Full v)) ->
                         well_formed_var Gamma Sigma bge vm m.

(*** Well formed loc (coming from ref, not variables) ***)
Inductive well_formed_loc (Sigma : store_context) (bge : BeePL.genv) (vm : vmap) (m : Memory.mem) : Prop :=
| store_well_typed_loc : (forall x ofs t, PTree.get x Sigma = Some (Ptrtype t) /\ 
                                               type_is_volatile (transBeePL_type (get_data_type t)) = false ->
                          (exists chunk, Mem.valid_access m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) Freeable /\
                                         chunk_of_type (get_data_type t) = Some chunk)) ->
                          well_formed_loc Sigma bge vm m.

(*** Well formed function ***)
Inductive well_formed_function (cenv : bcomposite_env) (Gamma : ty_context) (Sigma : store_context) (bge : BeePL.genv) (vm : vmap) (m : Memory.mem) : Prop :=
| store_well_typed_fn : (forall l o ef te ts efs rt vs efs', 
                         type_expr cenv Gamma Sigma (Val (Vloc l o) te) ef te -> 
                         eq_type te (Ptrtype (Fptype ts efs rt)) || eq_type te (Ftype ts efs rt) ->
                         type_exprs cenv Gamma Sigma vs efs' ts ->
                         exists fd, Genv.find_funct bge (trans_bvalue_cvalue (Vloc l o)) = Some (Internal fd) /\
                                    list_norepet (fd.(fn_args) ++ fd.(BeePL.fn_vars)) /\ 
                                    length fd.(fn_args) = length (extract_values_exprs vs) /\
                                    ts = (unzip2 fd.(fn_args)) /\ rt = get_rt_fundef (Internal fd)) ->
                        well_formed_function cenv Gamma Sigma bge vm m.

(** Well-Typed Store **)
(* A store st is well-typed with respect to a store typing context Sigma if the
   term at each location l in vm has the type at location l in store typing context
   and there exists a value in the memory at that location. *)
(* It is more evolved due to two maps used in CompCert for retrieving data from the memory *)
(* Since we only allow pointers through references, it is safe to say that if there exists a 
   location in memory then it is also safe to deref that location *)
(* Mem.valid_pointer ensures that the location l with ofset ofs is nonempty in memory m *)
Definition store_well_typed (cenv : bcomposite_env) (Gamma : ty_context) (Sigma : store_context) 
                            (bge : BeePL.genv) (vm : vmap) (m : Memory.mem) : Prop :=
well_formed_var Gamma Sigma bge vm m /\ well_formed_loc Sigma bge vm m /\ well_formed_function cenv Gamma Sigma bge vm m.

(* Complete me: Easy *)
Definition store_well_typed_ext : forall cenv Gamma Sigma bge vm m x l t,
store_well_typed cenv Gamma Sigma bge vm m ->
store_well_typed cenv Gamma Sigma bge (PTree.set x (l, t) vm) m.
Proof.
move=> cenv Gamma Sigma bge vm m x l t hw. case: hw=> [] h1 [] h2 h3.
constructor.
+ constructor. inversion h1.
  + move=> x' t' hxt. move: (H x' t' hxt)=> [] l' [] t'' [] v [] o [] hvm [] hteq [] hs [] hd.
Admitted.   

(* Complete me : Easy *)
Definition store_well_typed_mem_alloc : forall cenv Gamma Sigma bge vm m lo hi m' b,
store_well_typed cenv Gamma Sigma bge vm m ->
Mem.alloc m lo hi = (m', b) ->
store_well_typed cenv Gamma Sigma bge vm m'.
Proof.
Admitted.
 
Lemma mem_alloc_total :
forall m lo hi, exists m' b, Mem.alloc m lo hi = (m', b).
Proof.
intros. destruct (Mem.alloc m lo hi) as [m' b]. eauto.
Qed.

Lemma chunk_fits_allocation : forall p t chunk,
chunk_of_type t = Some chunk ->
size_chunk (transl_bchunk_cchunk chunk) <= sizeof_type (prog_comp_env p) t.
Proof.
move=> p t chunk. case: t=> [| | | | pt | ptr | bt] //=.
+ move=> pr. case: pr=> //=. 
  + by case: chunk=> //=.
  + move=> sz s a. by case: sz=> //=; case: s=> //=; case: chunk=> //=. 
  move=> s a. by case: chunk=> //=.
move=> ptr. by case: chunk=> //=.
Qed.

Lemma storev_succeeds_on_fresh_alloc : forall m chunk v sz,
let (m1, b) := Mem.alloc m 0 sz in
size_chunk  (transl_bchunk_cchunk chunk) <= sz ->
exists m', Mem.storev  (transl_bchunk_cchunk chunk) m1 (Values.Vptr b Ptrofs.zero) v = Some m'.
Proof.
Admitted.

Lemma store_well_typed_preserve : forall cenv Gamma Sigma bge vm m chunk b v t m',
store_well_typed cenv Gamma Sigma bge vm m ->
typeof_value v t ->
chunk_of_type t = Some chunk ->
Mem.storev (transl_bchunk_cchunk chunk) m (Values.Vptr b Ptrofs.zero) (trans_bvalue_cvalue v) = Some m' ->
store_well_typed cenv Gamma Sigma bge vm m'.
Proof.
Admitted.

(* I think we can prove this and make the well formedness definition simpler *)
Lemma safe_deref_valid_pointers : forall Sigma m x ofs pt chunk, 
PTree.get x Sigma = Some (Ptrtype pt) ->
type_is_volatile (transBeePL_type (get_data_type pt)) = false ->
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
Lemma safe_assgn_valid_pointers : forall Sigma bge m x ofs pt v chunk, 
PTree.get x Sigma = Some (Ptrtype pt) ->
type_is_volatile (transBeePL_type (get_data_type pt)) = false ->
chunk_of_type (get_data_type pt) = Some chunk ->
Mem.valid_access m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) Freeable ->
exists bf m', assign_addr bge (get_data_type pt) m x ofs bf v m' v.
Proof.
move=> Sigma bge m x ofs h bt a hs hv. 
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
Admitted.

Lemma get_type_fundef : forall cenv Gamma Sigma (bge: BeePL.genv) fd l o ef te ts efs rt,
type_expr cenv Gamma Sigma (Val (Vloc l o) te) ef te -> 
eq_type te (Ptrtype (Fptype ts efs rt)) || eq_type te (Ftype ts efs rt) ->
Genv.find_funct bge (trans_bvalue_cvalue (Vloc l o)) = Some (Internal fd) ->
BeePL.type_of_fundef (Internal fd) = Ftype (unzip2 fd.(fn_args)) (get_effect_fundef (Internal fd)) (get_rt_fundef (Internal fd)).
Proof.
move=> cenv Gamma Sigma bge fd l o ef te ts efs rt hte hteq hg. by case:fd hg=> //=.
Qed.

(*** Proving theorems related to type system for small step semantics of BeePL ***)

(* Progress for small step semantics *)
(* A well typed expression is never stuck,
   it either evaluates to a value or can continue executing. *) 
(* Progress for small step semantics *)
(* A well typed expression is never stuck,
   it either evaluates to a value or can continue executing. *)
Lemma progress_ssem_expr_exprs:
(forall cenv Gamma Sigma es efs ts bge p vm m, type_exprs cenv Gamma Sigma es efs ts ->
                                               store_well_typed cenv Gamma Sigma bge vm m ->
                                               is_values es \/ exists m' vm' es',
                                                               ssem_exprs bge p vm m es m' vm' es' /\
                                                               store_well_typed cenv Gamma Sigma bge vm' m') /\
(forall cenv Gamma Sigma e ef t bge p vm m, type_expr cenv Gamma Sigma e ef t ->
                                            store_well_typed cenv Gamma Sigma bge vm m ->
                                            is_value e \/ exists m' vm' e', 
                                                          ssem_expr bge p vm m e m' vm' e' /\
                                                          store_well_typed cenv Gamma Sigma bge vm' m').
Proof.
suff : (forall cenv Gamma Sigma es efs ts, type_exprs cenv Gamma Sigma es efs ts ->
                                      forall bge p vm m, store_well_typed cenv Gamma Sigma bge vm m ->
                                                       is_values es \/ (exists m' vm' es',
                                                       ssem_exprs bge p vm m es m' vm' es' /\
                                                       store_well_typed cenv Gamma Sigma bge vm' m')) /\
(forall cenv Gamma Sigma e ef t, type_expr cenv Gamma Sigma e ef t ->
                            forall bge p vm m, store_well_typed cenv Gamma Sigma bge vm m ->
                                             is_value e \/ (exists m' vm' e', 
                                                           ssem_expr bge p vm m e m' vm' e' /\
                                                           store_well_typed cenv Gamma Sigma bge vm' m')).
+ move=> [] hwt1 hwt2. split=> //=.
  + move=> cenv Gamma Sigma es efs ts bge p vm m htes hw.
    by move: (hwt1 cenv Gamma Sigma es efs ts htes bge p vm m hw).
  move=> cenv Gamma Sigma e ef t bge p vm m hte hw. 
  by move: (hwt2 cenv Gamma Sigma e ef t hte bge p vm m hw).
apply type_exprs_type_expr_ind_mut=> //=.
(* val unit *)
+ move=> cenv Gamma Sigma bge vm m hw. by left.
(* val bool *)
+ move=> cenv Gamma Sigma b bge vm m hw. by left.
(* val int *)
+ move=> cenv Gamma Sigma i sz s a bge vm m hw. by left.
(* val long *)
+ move=> cenv Gamma Sigma i s a bge vm m hw. by left.
(* val loc *)
+ move=> cenv Gamma Sigma l ofs h t a bge vm m hw. by left.
(* val option *)
+ move=> cenv Gamma Sigma o pt bge p vm m hw. by left.
(* var *)
+ move=> cenv Gamma Sigma v t hteq bge p vm m hw; subst. right. 
  rewrite /store_well_typed in hw. case: hw=> [] hw1 [] hw2 hw3.
  inversion hw1.
  + move: (H v t hteq)=> [] l' [] t' [] v' [] ofs.
    move=> [] hvm [] hteq' [] hs hd; subst.
    exists m. exists vm. exists (Val v' t'). split=> //=.
    eapply ssem_lvar. + by apply hvm. + by apply hd.
  (* gvar *)
  move: (H v t hteq).
  move=> [] l' [] ofs [] v' [] hs [] hg [] hs' hd. 
  exists m. exists vm. exists (Val v' t). split=> //=. 
  apply ssem_gbvar with l' ofs. + by apply hs. + by apply hg.
  by apply hd.
(* const int *)
+ move=> cenv Gamma Sigma t sz a i bge p vm m hw. right.
  exists m. exists vm. exists (Val (Vint i) (Vtype (Tint t sz a))). 
  split=> //=. by apply ssem_consti.
(* const long *)
+ move=> cenv Gamma Sigma t s i bge p vm m hw. right.
  exists m. exists vm. exists (Val (Vint64 i) (Vtype (Tlong t s))). 
  split=> //=. by apply ssem_constl.
(* const uint *)
+ move=> cenv Gamma Sigma bge p vm m. right; subst.
  exists m. exists vm. exists (Val (Vunit) tunit). split=> //=. by apply ssem_constu.
(* app *)
+ move=> cenv Gamma Sigma e te es rt efs ts ef efs' hte hin hteq htes hin' bge p vm m hw. 
  move: (hin bge p vm m hw)=> [].
  (* function location e is a value *)
  + move=> hve. case: e hte hin hve=> //= v t hte hin hve. case: v hte hin=> //=.
    (* unit *)
    + admit. (* provable *)
    (* bool *)
    + admit. (* provable *)
    (* int *)
    + admit. (* provable *)
    (* long *)
    + admit. (* provable *)
    (* loc : right case *)
    + move=> l o hte /= hin. move: (hin bge p vm m hw)=> hine.
      move: (hin' bge p vm m hw)=> [].
      (* es is val *)   
      + move=> hvs. pose proof hw as hsw.
        rewrite /store_well_typed in hw. case: hw=> [] hw1 [] hw2 hw3.
        inversion hw3. have [h [bt [a [h1 [h2 h3]]]]] := type_infer_loc cenv Gamma Sigma l o ef t te hte; subst.
        move: (H l o ef (Ptrtype (Reftype h bt a)) ts efs rt es efs' hte hteq htes)=> [] fd [] hg [] hl [] hd [] h1 h2.
        have [vm' [m' [ha hwa]]] := alloc_variables_wf cenv Gamma Sigma bge vm m (fn_args fd ++ BeePL.fn_vars fd) hsw hl.
        have [m'' [hb hwb]]:= bind_variables_wf cenv Gamma Sigma bge vm' m' (fn_args fd) (extract_values_exprs es) hwa hd.
        right. exists m''. exists vm'. exists fd.(BeePL.fn_body). by split=> //=. 
     (* es not a value *)
     + move=> [] m' [] vm' [] es' [] hes' hw'. right. exists m'. exists vm'. exists (App (Val (Vloc l o) t) es' rt).
       split=> //=. have [h [bt [a [h1 [h2 h3]]]]] := type_infer_loc cenv Gamma Sigma l o ef t te hte; subst. by apply ssem_app2.
   (* otpion *)
   admit. (* provable *)
  (* e is not a value *)
  admit. (* provable *)
(* ref *)
+ move=> cenv Gamma Sigma e ef h bt a hte hin hvo bge p vm m hw.
  move: (hin bge p vm m hw)=> [] he.
  (* is value *)
  + right. case: e hte hin he=> //= v t hte hin _.
    have hvt := type_rel_typeof_val cenv Gamma Sigma v ef t (construct_type_btype bt) hte.
    have [m' [b] ha] := mem_alloc_total m 0 (sizeof_type (prog_comp_env p) t).
    have hw'' := store_well_typed_mem_alloc cenv Gamma Sigma bge vm m 0 (sizeof_type (prog_comp_env p) t) m' b hw ha. 
    have [m'' [] chunk [] v' [] htv [] hc [] hs hws] := ref_allocation_succeeds cenv Gamma Sigma p bge vm m v t (m', b) hw hvt ha. 
    exists m''. exists vm. 
    exists (Val (Vloc b Ptrofs.zero) (Ptrtype (Reftype h bt a))). split=> //=.
    apply type_val_reflx in hte; subst.
    apply ssem_ref2 with (Mem.alloc m 0 (sizeof_type (prog_comp_env p) (construct_type_btype bt))) chunk Sigma
    (extend_context Sigma (Mem.alloc m 0 (sizeof_type (prog_comp_env p) (construct_type_btype bt))).2 (Ptrtype (Reftype h bt a))).
    + by auto.
    + by apply hc.
    + rewrite ha /=. by apply hs.
    rewrite ha /=. by rewrite /extend_context.
  (* step *)
  right. move: he. move=> [] m' [] vm' [] e' [] he hv. exists m'.
  exists vm'. exists (Prim Ref [:: e'] (Ptrtype (Reftype h bt a))). 
  split=> //=. by apply ssem_ref1.
(* deref *)
+ move=> cenv Gamma Sigma e ef pt h hte hin ho hvo bge p vm m hw.
  move: (hin bge p vm m hw)=> [].
  (* is value *)
  + move=> hv. right. rewrite /is_value in hv. case: e hv hte hin=> v t //= _. case: v=> //=.
    (* unit *)
    + move=> hte hin.
      have := type_infer_vunit cenv Gamma Sigma ef t (Ptrtype pt) hte; subst. by move=> [] h1 h2 //=.
    (* bool *)
    + move=> b hte hin.
      have := type_infer_vbool cenv Gamma Sigma ef b t (Ptrtype pt) hte; subst. by move=> [] h1 h2 //=.
    (* int *)
    + move=> i hte hin. 
      by have [h1 [sz] [s] [] h2 h3] := type_infer_int cenv Gamma Sigma i ef t (Ptrtype pt) hte; subst.
    (* long *)
    + move=> l hte hin. 
      by have [s [] a' [] h1 h2] := type_infer_long cenv Gamma Sigma l ef t (Ptrtype pt) hte.
    (* loc *)
    + move=> l ofs hte hin. pose proof hw as hsw. case: hw=> [] hw1 [] hw2 hw3.
      have [h' [bt [a [m' [hpt hl ]]]]] := type_infer_loc cenv Gamma Sigma l ofs 
                                                ef t (Ptrtype pt) hte; subst.
      inversion hw2. case: hpt=> [] hpteq; subst.
      have hand : Sigma ! l = Some (Ptrtype (Reftype h' bt a)) /\ type_is_volatile (transBeePL_type (get_data_type ((Reftype h' bt a)))) = false.
      + by split=> //=.  move: (H l ofs (Reftype h' bt a) hand)=> [] chunk [] hvl hc.
      have [v hd]:= safe_deref_valid_pointers Sigma m l ofs (Reftype h' bt a) chunk hl hvo hc hvl.
      exists m. exists vm. exists (Val v (get_data_type (Reftype h' bt a))). split.
      by apply ssem_deref2 with Full. by apply hsw.
    (* option *) (* deref does not allow pointer coming from option type until it is gone through match *)
    + move=> o hte hin.
      have [pt' [h1 h2]] := type_infer_option cenv Gamma Sigma ef o t (Ptrtype pt) hte.
      case: h2=> h2'. by rewrite h2' in ho.
  (* step *)
  move: (hin bge p vm m hw)=> hin'. move=> [] m' [] vm' [] e' [] he hs. right.
  exists m'. exists vm'. exists (Prim Deref [:: e'] (get_data_type pt)). split=> //=. 
  apply ssem_deref1. by apply he.
(*
(* massgn *)
+ move=> Gamma Sigma e e' h bt ef a ef' hte hin hte' hin' bge vm m hw. 
  right. move: (hin bge vm m hw)=> [].
  (* value e *)
  + move=> hv. case: e hte hin hv=> //= v t. case: v=> //=.
    (* unit *)
    + move=> hte.  
      by have [h1 h2] := type_infer_vunit Gamma Sigma ef t (Reftype h (Bprim bt) a) hte; subst.
    (* bool *)
    + move=> b hte hin.
      by have [h1 h2] := type_infer_vbool Gamma Sigma ef b t (Reftype h (Bprim bt) a) hte; subst.
    (* int *)
    + move=> i hte. 
       by have [h1 [sz] [s] [] h2 h3] := type_infer_int Gamma Sigma i ef t (Reftype h (Bprim bt) a) hte; subst.
    (* long *)
    + move=> l hte. 
      by have [s [] a' [] h1 h2] := type_infer_long Gamma Sigma l ef t (Reftype h (Bprim bt) a) hte.
    (* loc *)
    move=> l ofs hte hin _. move: (hin' bge vm m hw)=> [] hv'.
    (* value e' *)
    + case: e' hte' hin' hv'=> //= v' t' hte' hin' _. rewrite /store_well_typed in hw. 
       have [h' [] bt' [] a' [] h1 [] [] h11 h12 h13 hs] := type_infer_loc Gamma Sigma l ofs 
                                                ef t (Reftype h (Bprim bt) a) hte; subst.
      move: (hw Gamma l). case hg: Gamma ! l=> [ t''| ] //=.
      + case hvm : vm ! l => [[ l1 t1] | ] //=.
        + move=> [] h1 [] h2 [] v [] ofs' [] hd [] hv hp; subst. rewrite h2 in hs. 
          case: hs=> hs; subst.
          by inversion hp.
      move=> [] l' [] ofs' [] v [] hg' [] hs' [] hd [] hv hp. rewrite hg' in hs. case: hs=> hs; subst.
      by inversion hp.
    move=> hwd. move: (hwd ofs h' bt a' hs)=> [] hvp [] hd ha. 
    move: (ha v')=> [] bf [] m' [] ha' hv'.      
    exists m'. exists vm. exists (Val Vunit (Ptype Tunit)). *)
    (*have hteq := type_val_reflx Gamma Sigma v' t' ef' (Ptype bt) hte'; subst. split=> //=.
    + by apply ssem_massgn3 with bf. 
    by have := assign_preserves_store_well_typed Sigma bge vm m bt l ofs bf v' m' hw ha' hv'.
   (* e' steps *)
   move: hv'. move=> [] m' [] vm' [] e'' [] he'' hs. exists m'. exists vm'.
   exists (Prim Massgn [:: Val (Vloc l ofs) t; e''] (Ptype Tunit)).
   have hteq := type_val_reflx Gamma Sigma (Vloc l ofs) t ef 
                 (Reftype h (Bprim bt) a) hte; subst. split=> //=. by apply ssem_massgn2. 
  (* e steps *)
  move=> [] m' [] vm' [] e'' [] he'' hs. exists m'. exists vm'.
  exists (Prim Massgn [:: e''; e'] (Ptype Tunit)). split=> //=. by apply ssem_massgn1. 
(* uop *)
+ move=> Gamma Sigma op e ef t hf hf' hte hin bge vm m hw. right.
  move: (hin bge vm m hw)=> [] hv.
  (* value e *)
  + case: e hte hin hv=> //= v t' hte hin _. exists m. exists vm.
    have [hwts hwt] := well_typed_success. 
    have hteq := type_val_reflx Gamma Sigma v t' ef t hte; subst.
    have htuop := type_uop_inject Gamma Sigma (Val v t) t ef op hf hf' hte.
    move: (hwt Gamma Sigma (Val v t) ef t hte)=> [] ct [] g [] i hct.
    have [v' hsop] := well_formed_uop Gamma Sigma bge vm v ef t op m ct g i htuop hct hw.
    have [v'' hbv] := trans_value_uop_success Gamma Sigma ef t op v ct g g i m v' hte hct hsop. 
    exists (Val v'' t). split=> //=. apply ssem_uop2 with v' ct g g i. + by apply hct.
    + by apply hsop. by apply hbv.
  (* step *)
  move: hv. move=> [] m' [] vm' [] e' [] he' hs'. exists m'. exists vm'.
  exists (Prim (Uop op) [:: e'] t). 
  have hteq := type_rel_typeof Gamma Sigma e ef t hte; subst. split=> //=. by apply ssem_uop1.
(* bop *)
+ move=> Gamma Sigma op e ef t e' hf hf' hte hin hte' hin' bge vm m hw. right.
  move: (hin bge vm m hw)=> [] hv.
  (* value e *)
  + case: e hte hin hv=> //= v t' hte hin _. move:(hin' bge vm m hw)=> [] hv'.
    (* value e' *)
    + case: e' hte' hin' hv'=> //= v' t'' hte' hin' _.
      have hteq := type_val_reflx Gamma Sigma v t' ef t hte; subst.
      have hteq' := type_val_reflx Gamma Sigma v' t'' ef t hte'; subst.
      have [hwt1 hwt2] := well_typed_success. 
      move: (hwt2 Gamma Sigma (Val v t) ef t hte)=> [] ct1 [] g [] i hct1.
      move: (hwt2 Gamma Sigma (Val v' t) ef t hte')=> [] ct2 [] g' [] i' hct2.
      have htop := type_bop_inject Gamma Sigma (Val v t) (Val v' t) t ef op hf hf' hte hte'.
      have [v'' hsop] := well_formed_bop Gamma Sigma bge vm (BeePL.genv_cenv bge) v v' ef t op 
                         m ct1 g i htop hct1 hw.
      have [v''' htv] := trans_value_bop_success Gamma Sigma bge (BeePL.genv_cenv bge) vm 
                         op v v' ef t ct1 g i m v'' htop hct1 hw hsop.
      exists m. exists vm. exists (Val v''' t). split=> //=. 
      by apply ssem_bop3 with (BeePL.genv_cenv bge) v'' ct1 g g i.
    (* e' steps *)
    move: hv'. move=> [] m' [] vm' [] e'' [] he'' hs. exists m'. exists vm'. 
    have hteq := type_val_reflx Gamma Sigma v t' ef t hte; subst.
    exists (Prim (Bop op) [:: Val v t; e''] t). split=> //=. by apply ssem_bop2. 
  (* e steps *)
  move: hv. move=> [] m' [] vm' [] e'' [] he'' hs. exists m'. exists vm'. 
  have hteq := type_rel_typeof Gamma Sigma e ef t hte; subst.
  exists (Prim (Bop op) [:: e''; e'] (typeof_expr e)). split=> //=. by apply ssem_bop1. 
(* bind *)
+ move=> Gamma Sigma x t e e' t' ef ef' hte hin hte' hin' bge vm m hw. right.
  move: (hin bge vm m hw)=> [] hv.
  (* value e *)
  + case: e hte hin hv=> //= v tv hte hin _. exists m. exists vm. exists (subst x (Val v tv) e').
    have hteq := type_rel_typeof (extend_context Gamma x t) Sigma e' ef' t' hte'; subst. 
    have hteq' := type_rel_typeof Gamma Sigma (Val v tv) ef t hte; subst. split=> //=.
    by apply ssem_bind2.
  (* e steps *)
  move: hv. move=> [] m' [] vm' [] e'' [] he'' hs. exists m'. exists vm'. exists (Bind x t e'' e' t').
  have hteq := type_rel_typeof (extend_context Gamma x t) Sigma e' ef' t' hte'; subst. split=> //=.
  by apply ssem_bind1.
(* cond *)
+ move=> Gamma Sigma e1 e2 e3 tb t ef1 ef2 hte1 hin htbv hte2 hin' hte3 hin'' bge vm m hw.
  right. move: (hin bge vm m hw)=> [] hv.
  (* value e1 *)
  + case: e1 hte1 hin hv=> //= v t' hte1 hin _. exists m. exists vm. exists e2.
    have hteq := type_rel_typeof Gamma Sigma e2 ef2 t hte2; subst. 
    have [hwt1 hwt2] := well_typed_success. move: (hwt2 Gamma Sigma (Val v t') ef1 tb hte1).
    move=> [] ct [] g [] i hct. split=> //=.
    apply ssem_ctrue with g ct g i. 
    + by have hteq := type_val_reflx Gamma Sigma v t' ef1 tb hte1; subst.
    have hteq := type_val_reflx Gamma Sigma v t' ef1 tb hte1; subst.
    by have := type_bool_val Gamma Sigma v tb ef1 ct m true hte1 htbv.
  (* e1 steps *) 
  move: hv. move=> [] m' [] vm' [] e1' [] he1' hs. exists m'. exists vm'.
  exists (Cond e1' e2 e3 t). have hteq := type_rel_typeof Gamma Sigma e2 ef2 t hte2; subst.
  split=> //=. by apply ssem_cond.
(* unit *)
+ move=> Gamma Sigma bge vm m hw. right. exists m. exists vm. exists (Val Vunit (Ptype Tunit)).
  split=> //=. by apply ssem_ut.
(* addr *)
+ move=> Gamma Sigma l ofs h bt a hs bge vm m hw. right.
  exists m. exists vm. exists (Val (Vloc l.(lname) ofs) (Reftype h bt a)). split=> //=. by apply ssem_adr.
(* eapp *)
+ move=> Gamma Sigma exf ts es ef rt hrt [] hut hft htseq hts hin bge vm m hw; subst.
  right. admit. (* aslso add success of external call as hypothesis in Events.v *)
(* nil *)
+ move=> Gamma Sigma bge vm m hw. by left.
(* cons *)
move=> Gamma Sigma e es ef efs t ts hte hin htes hins bge vm m hw.
move: (hin bge vm m hw)=> [] hv.
(* value e *)
+ move: (hins bge vm m hw)=> [] hvs.
  (* value es *)
  + left. by rewrite /andb hv. 
  (* es steps *)
  move: hvs. move=> [] m' [] vm' [] es' [] hes hs. right.
  case: e hte hin hv=> //= v t' hte hin _. exists m'. exists vm'.
  exists (Val v t' :: es'). split=> //=. by apply ssem_cons2.
move: hv. move=> [] m' [] vm' [] e' [] he' hs. right.
exists m'. exists vm'. exists (e' :: es). split=> //=. by apply ssem_cons1.*)
Admitted.

Lemma not_ptr_cval : forall cv bv, 
trans_cvalue_bvalue cv = OK bv ->
is_vloc bv = false -> 
Values.is_vptr cv = false.
Proof.
move=> cv bv. rewrite /trans_cvalue_bvalue /=.
case: cv=> //=.
by move=> b p [] h; subst.
Qed.

(**** Substitution preserves typing ****)
Lemma subst_preservation : forall cenv Gamma Sigma x t se e ef' ef t', 
type_expr cenv (extend_context Gamma x t) Sigma e ef' t' ->
type_expr cenv Gamma Sigma se ef t ->
type_expr cenv Gamma Sigma (subst x se e) (ef ++ ef') t'.
Proof.
Admitted.

(* Generalize it to take into account all cases in one lemma *)
Lemma exf_ret_extract_int : forall bt ct,
bt <> tunit ->
is_funtype bt = false -> 
transBeePL_type bt = ct ->
rettype_of_type ct = AST.Tint ->
exists sz s a, bt = Vtype (Tint sz s a).
Proof.
(*move=> sg bt ct g' i htu htf ht hp. case: bt htu htf ht=> //=.
(* prim *)
+ move=> p. case: p=> //=.
  (* int *)
  + move=> sz s a hut _ [] h1 h2; subst. exists sz. exists s. by exists a.
  move=> s a hut _ [] h1 h2; subst. by rewrite /proj_rettype /= in hp.
(* ref *)
move=> h b a hut. case: b hut=> //= p hut.
case: p hut =>//=.  + move=> hut _ [] h1 h2; subst. by rewrite /proj_rettype /= in hp.
+ move=> sz s a' hut _ [] h1 h2; subst. by rewrite  /proj_rettype /= in hp.
move=> s a' hut _ [] h1 h2; subst. by rewrite /proj_rettype /= in hp.
Qed.*) Admitted.

Lemma exf_ret_extract_long_ref : forall bt ct,
bt <> tunit ->
is_funtype bt = false -> 
transBeePL_type bt = ct ->
rettype_of_type ct = AST.Tlong ->
if Ctypes.is_pointer ct
then (exists h t a, bt = Ptrtype (Reftype h t a))
else (exists s a, bt = Vtype (Tlong s a)).
Proof.
(*move=> g bt ct g' i htu htf ht hp. case: bt htu htf ht=> //=.
(* prim *)
+ move=> p. case: p=> //=.
  (* int *)
  + move=> sz s a hut _ [] h1 h2; subst. 
    rewrite /rettype_of_type /= in hp. case: sz hp hut=> //=.
    + by case: s=> //=.
    by case: s=> //=.
  move=> s a hut _ [] h1 h2; subst. rewrite /=. exists s. by exists a.
(* ref *)
move=> h b a hut _. case: b hut=> //= p hut.
case: p hut =>//=.  
+ move=> hut [] h1 h2; subst. rewrite /rettype_of_type /= in hp.
  rewrite /Tptr in hp. move: hp. case: Archi.ptr64=> //=. rewrite /=.
  exists h. exists (Bprim Tunit). by exists a.
+ move=> sz s a' hut [] h1 h2; subst. rewrite /rettype_of_type /= in hp.
  rewrite /Tptr in hp. move: hp. case: Archi.ptr64=> //=. rewrite /=.
  exists h. exists  (Bprim (Tint sz s a')). by exists a.
move=> s a' hut [] h1 h2; subst. rewrite /rettype_of_type /= in hp.
rewrite /Tptr in hp. move: hp. case: Archi.ptr64=> //=. rewrite /=.
exists h. exists (Bprim (Tlong s a')). by exists a.
Qed.*) Admitted.

(**** External call result has the same type as present in the signature *)
Lemma well_typed_res_ext : forall cenv Gamma Sigma bge bge' exf cef vm m m' vs vres bv ef t,
(get_rt_eapp exf) <> tunit ->
is_funtype (get_rt_eapp exf) = false ->
befunction_to_cefunction exf = cef ->
Events.external_call cef bge vs m t vres m' ->
trans_cvalue_bvalue vres = OK bv ->
type_expr cenv Gamma Sigma (Val bv (get_rt_eapp exf)) (get_ef_eapp exf ++ ef) (get_rt_eapp exf) /\
store_well_typed cenv Gamma Sigma bge' vm m'.
Proof. 
(*move=> Gamma Sigma bge bge' exf g cef g' i' vm m m' vs vres bv ef t hut hft hcf hext hv.
have hcvs := Events.external_call_well_typed cef bge vs m t vres m' hext.
rewrite /befunction_to_cefunction in hcf. case hexf: exf hcf=> [exn sig ] //=.
rewrite /bind /=. case hsig: (bsig_to_csig sig g) hut hft=> [ | cexf cs ca] /= hut /= hft //=.
move=> [] h1 h2; subst. 
case: bv hv=> //=.
(* unit 4 *)
+ by case: vres hext hcvs=> //=.
(* int 3 *)
+ move=> i. case: vres hext hcvs=> //= i1 hext hcvs [] hieq; subst. 
  case: sig hsig hft hut=> //= bts bef brt bcc /=. 
  case: cexf hext hcvs=> //= cts cef crt ccc /=. rewrite /proj_sig_res /=.
  case: cef ccc=> //=.
  (* typ 9 *)
  + move=> t' hext. case: t' hext=> //=.
    (* int 10 *)
    + move=> hext _. rewrite /bsig_to_csig /bind /=.
      case hts : (transBeePL_types transBeePL_type bts g)=> [err | cts' gs gis] //=.
      case ht: (transBeePL_type brt gs)=> [err1 | ct1 gs1 gis1] //=. 
      move=> [] h1 h2 h3 h4 hft hut; subst. 
      have [sz [] s [] a hbrt] := exf_ret_extract_int gs brt ct1 g' gis1 hut hft ht h2.
      rewrite hbrt. split=> //=. 
      + have hn : type_expr Gamma Sigma (Val (Vint i) (Ptype (Tint sz s a))) [::] 
                  (Ptype (Tint sz s a)).
        + by apply ty_vali. 
      have hs := sub_effect_nil (bef ++ ef). 
      by have := ty_sub Gamma Sigma (Val (Vint i) (Ptype (Tint sz s a))) nil (Ptype (Tint sz s a))
                 (bef ++ ef) hn hs.
    (* 11 *)
    + move=> hext _. rewrite /bsig_to_csig /bind /=.
      case hts : (transBeePL_types transBeePL_type bts g)=> [err | cts' gs gis] //=.
      case ht: (transBeePL_type brt gs)=> [err1 | ct1 gs1 gis1] //=. 
      move=> [] h1 h2 h3 h4 hft hut; subst. case: ct1 ht h2=> //=.
      + move=> sz s a ht. have hbrt:= transBeePL_type_int brt gs g' gis1 sz s a ht.
        rewrite hbrt. move=> h. by apply ty_vali.
      move=> f a hbrt. by have hf := no_btype_to_float brt gs f a g' gis1.
     move=> hext _. rewrite /bsig_to_csig /bind /=.
     case hts : (transBeePL_types transBeePL_type bts g)=> [err | cts' gs gis] //=.
     case ht: (transBeePL_type brt gs)=> [err1 | ct1 gs1 gis1] //=. 
     move=> [] h1 h2 h3 h4 hft hut; subst. case: ct1 ht h2=> //=.
     + move=> sz s a ht. have hbrt:= transBeePL_type_int brt gs g' gis1 sz s a ht.
       rewrite hbrt. move=> h. by apply ty_vali.
     move=> f a hbrt. by have hf := no_btype_to_float brt gs f a g' gis1.
  (* 8 *)
  + move=> hext _. rewrite /bsig_to_csig /= /bind /=.
    case hts : (transBeePL_types transBeePL_type bts g)=> [err | cts' gs gis] //=.
    case ht: (transBeePL_type brt gs)=> [err1 | ct1 gs1 gis1] //=. 
    move=> [] h1 h2 h3 h4 hft hut; subst. case: ct1 ht h2=> //=.
    + move=> sz s a ht. have hbrt:= transBeePL_type_int brt gs g' gis1 sz s a ht.
      rewrite hbrt. move=> h. by apply ty_vali.
    move=> f a ht. by have hf := no_btype_to_float brt gs f a g' gis1.
  (* 7 *)
  + move=> hext _. rewrite /bsig_to_csig /= /bind /=.
    case hts : (transBeePL_types transBeePL_type bts g)=> [err | cts' gs gis] //=.
    case ht: (transBeePL_type brt gs)=> [err1 | ct1 gs1 gis1] //=. 
    move=> [] h1 h2 h3 h4 hft hut; subst. case: ct1 ht h2=> //=.
    + move=> sz s a ht. have hbrt:= transBeePL_type_int brt gs g' gis1 sz s a ht.
      rewrite hbrt. move=> h. by apply ty_vali.
    move=> f a ht. by have hf := no_btype_to_float brt gs f a g' gis1.
  (* 6 *)
  + move=> hext _. rewrite /bsig_to_csig /= /bind /=.
    case hts : (transBeePL_types transBeePL_type bts g)=> [err | cts' gs gis] //=.
    case ht: (transBeePL_type brt gs)=> [err1 | ct1 gs1 gis1] //=. 
    move=> [] h1 h2 h3 h4 hft hut; subst. case: ct1 ht h2=> //=.
    + move=> sz s a ht. have hbrt:= transBeePL_type_int brt gs g' gis1 sz s a ht.
      rewrite hbrt. move=> h. by apply ty_vali.
    move=> f a ht. by have hf := no_btype_to_float brt gs f a g' gis1.
  (* 5 *)
  + move=> hext _. rewrite /bsig_to_csig /= /bind /=.
    case hts : (transBeePL_types transBeePL_type bts g)=> [err | cts' gs gis] //=.
    case ht: (transBeePL_type brt gs)=> [err1 | ct1 gs1 gis1] //=. 
    move=> [] h1 h2 h3 h4 hft hut; subst. case: ct1 ht h2=> //=.
    + move=> sz s a ht. have hbrt:= transBeePL_type_int brt gs g' gis1 sz s a ht.
      rewrite hbrt. move=> h. by apply ty_vali.
    move=> f a ht. by have hf := no_btype_to_float brt gs f a g' gis1.
  + (* 4 *)
    move=> hext _. rewrite /bsig_to_csig /= /bind /=.
    case hts : (transBeePL_types transBeePL_type bts g)=> [err | cts' gs gis] //=.
    case ht: (transBeePL_type brt gs)=> [err1 | ct1 gs1 gis1] //=. 
    move=> [] h1 h2 h3 h4 hft hut; subst. case: ct1 ht h2=> //=.
    + move=> sz s a ht. have hbrt:= transBeePL_type_int brt gs g' gis1 sz s a ht.
      rewrite hbrt. move=> h. by apply ty_vali.
    move=> f a ht. by have hf := no_btype_to_float brt gs f a g' gis1.
   move=> hext _. rewrite /bsig_to_csig /= /bind /=.
   case hts : (transBeePL_types transBeePL_type bts g)=> [err | cts' gs gis] //=.
   case ht: (transBeePL_type brt gs)=> [err1 | ct1 gs1 gis1] //=. 
   move=> [] h1 h2 h3 h4 hft hut; subst. case: ct1 ht h2=> //=.
   + move=> ht _. by have hbrt := transBeePL_type_void brt gs g' gis1 ht.
   + move=> sz s a ht. have hbrt:= transBeePL_type_int brt gs g' gis1 sz s a ht.
     rewrite hbrt. move=> h. by apply ty_vali.
   + move=> f a ht. by have hf := no_btype_to_float brt gs f a g' gis1. 
   + move=> t' z a ht. by have hf := no_btype_to_array brt t' z a gs g' gis1.
   + move=> ts t1 ct ht _. 
     have [bt [] ef' [] rt hbrt] := transBeePL_type_function brt ts t1 ct gs g' gis1 ht.
     by rewrite hbrt in hft.
   + move=> h a ht. by have := no_btype_to_struct brt h a gs g' gis1.
   + move=> h a ht. by have := no_btype_to_union brt h a gs g' gis1.
 (* long *)
 + move=> i. case: vres hext hcvs=> //= i1 hext hcvs [] hieq; subst. 
   case: sig hsig hft hut=> //= bts bef brt bcc /=. 
   case: cexf hext hcvs=> //= cts cef crt ccc /=. rewrite /proj_sig_res /=.
   case: cef ccc=> //=.
   (* typ 9 *)
  + move=> t' hext. case: t' hext=> //=.
    + move=> hext _. rewrite /bsig_to_csig /bind /=.
      case hts : (transBeePL_types transBeePL_type bts g)=> [err | cts' gs gis] //=.
      case ht: (transBeePL_type brt gs)=> [err1 | ct1 gs1 gis1] //=.
      move=> [] h1 h2 h3 h4 hut hft; subst. 
      have /= htlp := exf_ret_extract_long_ref gs brt ct1 g' gis1 hft hut ht h2.
      case: ct1 ht h2 htlp=> //=.
      + move=> sz s a. by case: sz=> //=; case: s=> //=.
      + move=> s a ht _ [] s' [] a' hbrt. rewrite hbrt. by apply ty_vall.
      + move=> fsz a ht. by have ht' := no_btype_to_float brt gs fsz a g' gis1.
      move=> t' a ht heq [] h [] bt [] a' hbrt. admit. (* because in C they treat pointer as long/int *)
   move=> hext _. rewrite /bsig_to_csig /bind /=.
   case hts : (transBeePL_types transBeePL_type bts g)=> [err | cts' gs gis] //=.
   case ht: (transBeePL_type brt gs)=> [err1 | ct1 gs1 gis1] //=.
   move=> [] h1 h2 h3 h4 hut hft; subst. case: ct1 ht h2=> //=.
   + move=> sz s a. by case: sz=> //=; case: s=> //=.
   move=> fsz a ht. by have hf := no_btype_to_float brt gs fsz a g' gis1.
move=> loc ofs. case: vres hext hcvs=> //= loc' ofs'.  
case: sig hsig hft hut=> //= bts bef brt bcc /=. rewrite /bsig_to_csig /= /bind /proj_sig_res /=.
case hts : (transBeePL_types transBeePL_type bts g)=> [err | cts' gs gis] //=.
case ht: (transBeePL_type brt gs)=> [err1 | ct1 gs1 gis1] //=.
move=> [] h1 h2 hft hut /=; subst. rewrite /proj_rettype /=.
case: ct1 ht=> //=.
+ move=> sz s a. by case: sz=> //=; case: s=> //=.
+ move=> s a ht hext hp [] h1 h2; subst. admit. (* because in C they treat pointer as long/int *)
+ move=> fsz a ht. by have ht' := no_btype_to_float brt gs fsz a g' gis1.
move=> t' a ht. have [h [] bt [] a' hpt]:= transBeePL_type_ref brt t' a gs g' gis1 ht.
move=> hext hm [] h1 h2; subst. apply ty_valloc.*)
Admitted.

(* we need extra assertion that value cannot be a pointer because 
   in C, they allow it and we use deref_addr from CompCert *)
Lemma well_typed_val_expr : forall cenv Gamma Sigma v t ef bf m l ofs,
deref_addr t m l ofs bf v ->
is_vloc v = false ->
type_expr cenv Gamma Sigma (Val v t) ef t.
Proof.
(*move=> cenv bge Gamma Sigma v t ef bf m l ofs hd hw. 
case hv: v hd=> [ | b | i | i64 | l' ofs'| o] //=; subst.
(* unit *)
+ move=> hd. case: t hd=> //=.
  + move=> p. case: p=> //=.
    + move=> hd. have hn : type_expr cenv Gamma Sigma (Val Vunit tunit) [::] tunit.
      + by apply ty_valu.
      have hs := sub_effect_nil ef. 
      by have := ty_sub cenv Gamma Sigma (Val Vunit tunit) nil tunit ef hn hs.
    + move=> sz s a hd _.
      have := wderef_addr_val_ty bge (Ptype (Tint sz s a)) m l ofs bf Vunit hd hw erefl.
      rewrite /wtype_of_type /=.  admit. (* weird coq behavior *)
    move=> s a hd _.
    have := wderef_addr_val_ty bge (Ptype (Tlong s a)) m l ofs bf Vunit hd hw erefl.
    admit. (* weird coq behavior *)
  move=> es e t hd _.
  have /= := wderef_addr_val_ty bge (Ftype es e t) m l ofs bf Vunit hd erefl erefl.
  admit. (* weird coq behavior *)
(* int *)
+ move=> hd. inversion hd; subst.
  (* not volatile *)
  + case: t hd H H0 hw'=> //=.
    + move=> p. case: p=> //=.
      (* Tint: good case *)
      + move=> sz s a hd hm hv _. 
        have hn : type_expr Gamma Sigma (Val (Vint i) (Ptype (Tint sz s a))) [::] 
                  (Ptype (Tint sz s a)).
        + by apply ty_vali. have hs := sub_effect_nil ef. 
        by have := ty_sub Gamma Sigma (Val (Vint i) (Ptype (Tint sz s a))) nil (Ptype (Tint sz s a))
                ef hn hs.
      (* Tlong : bad case *)
      move=> s a hd [] hc hv _. 
      by have := wderef_addr_val_ty bge (Ptype (Tlong s a)) m l ofs Full (Vint i) hd hw erefl.
  (* volatile *)
  case: t hd H H0 hw'=> //=.
  + move=> p. case: p=> //=.
    (* Tint: good case *)
    + move=> sz s a hd hm hv _. 
      have hn : type_expr Gamma Sigma (Val (Vint i) (Ptype (Tint sz s a))) [::] 
                  (Ptype (Tint sz s a)).
      + by apply ty_vali. have hs := sub_effect_nil ef. 
      by have := ty_sub Gamma Sigma (Val (Vint i) (Ptype (Tint sz s a))) nil (Ptype (Tint sz s a))
                ef hn hs.
    (* Tlong : bad case *)
    move=> s a hd [] hc hv _. 
    by have /= := wderef_addr_val_ty bge (Ptype (Tlong s a)) m l ofs Full (Vint i) hd hw erefl.
(* long *)
move=> hd. inversion hd; subst.
(* not volatile *)
+ case: t hd H H0 hw'=> //=.
  + move=> p. case: p=> //=.
    (* Tint: not good case *)
    + move=> sz s a hd hm hv _. 
      by have /= := wderef_addr_val_ty bge (Ptype (Tint sz s a)) m l ofs Full 
                    (Vint64 i64) hd erefl erefl. 
    (* Tlong : good case *)
    move=> s a hd [] hc hv _. 
    have hn : type_expr Gamma Sigma (Val (Vint64 i64) (Ptype (Tlong s a))) [::] 
                  (Ptype (Tlong s a)).
    + by apply ty_vall. have hs := sub_effect_nil ef. 
    by have := ty_sub Gamma Sigma (Val (Vint64 i64) (Ptype (Tlong s a))) nil (Ptype (Tlong s a))
                ef hn hs.
(* volatile *)
case: t hd H H0 hw'=> //=.
+ move=> p. case: p=> //=.
  (* Tint: not good case *)
  + move=> sz s a hd hm hv _. 
  by have /= := wderef_addr_val_ty bge (Ptype (Tint sz s a)) m l ofs Full (Vint64 i64) hd erefl erefl. 
  (* Tlong : good case *)
  move=> s a hd [] hc hv _. 
  have hn : type_expr Gamma Sigma (Val (Vint64 i64) (Ptype (Tlong s a))) [::] 
                  (Ptype (Tlong s a)).
  + by apply ty_vall. have hs := sub_effect_nil ef. 
  by have := ty_sub Gamma Sigma (Val (Vint64 i64) (Ptype (Tlong s a))) nil (Ptype (Tlong s a))
                ef hn hs.
(* Tref : not good case *)
move=> hd.
by have /= := wderef_addr_val_ty bge t m l ofs bf (Vloc l' ofs') hd.*)
Admitted.

(*** Preservation for small-step semantics ***)
(* If a program starts well-typed, it remains well-typed throughout execution,
   an evaluation does not produce type errors.*)
Lemma preservation_ssem_expr_exprs: 
(forall cenv Gamma Sigma es efs ts bge p vm m vm' m' es', 
    type_exprs cenv Gamma Sigma es efs ts ->
    store_well_typed cenv Gamma Sigma bge vm m ->
    ssem_exprs bge p vm m es m' vm' es' ->
    exists efs', type_exprs cenv Gamma Sigma es' efs' ts /\ 
                 sub_effect efs' efs /\
                 store_well_typed cenv Gamma Sigma bge vm' m') /\
(forall cenv Gamma Sigma e ef t bge p vm m vm' m' e', 
    type_expr cenv Gamma Sigma e ef t ->
    store_well_typed cenv Gamma Sigma bge vm m ->
    ssem_expr bge p vm m e m' vm' e' ->
    exists ef', type_expr cenv Gamma Sigma e' ef' t /\ sub_effect ef' ef /\
               store_well_typed cenv Gamma Sigma bge vm' m').
Proof.
suff : (forall cenv Gamma Sigma es efs ts, type_exprs cenv Gamma Sigma es efs ts ->
                                      forall bge p vm m vm' m' es', 
                                      store_well_typed cenv Gamma Sigma bge vm m ->
                                      ssem_exprs bge p vm m es m' vm' es' ->
                                      exists efs', type_exprs cenv Gamma Sigma es' efs' ts /\ 
                                      sub_effect efs' efs /\
                                      store_well_typed cenv Gamma Sigma bge vm' m') /\
       (forall cenv Gamma Sigma e ef t, type_expr cenv Gamma Sigma e ef t ->
                                   forall bge p vm m vm' m' e', 
                                   store_well_typed cenv Gamma Sigma bge vm m ->
                                   ssem_expr bge p vm m e m' vm' e' ->
                                   exists ef', type_expr cenv Gamma Sigma e' ef' t /\
                                   sub_effect ef' ef /\
                                   store_well_typed cenv Gamma Sigma bge vm' m').
+ move=> [] ih ih'. split=> //=.
  + admit.
  admit.
apply type_exprs_type_expr_ind_mut=> //=.
(* val unit *)
+ move=> cenv Gamma Sigma bge p vm m vm' m' e' hw he.  exists nil.
  by inversion he; subst; split=> //=. 
(* val bool *)
+ move=> cenv Gamma Sigma b bge p vm m vm' m' e' hw he. exists nil.
  by inversion he; subst; split=> //=. 
(* val int *)
+ move=> cenv Gamma Sigma i sz s a bge p vm m vm' m' e' hw he. exists nil.
  by inversion he; subst; split=> //=.
(* val long *)
+ move=> cenv Gamma Sigma i s a bge p vm m vm' m' e' hw he. exists nil.
  by inversion he; subst; split=> //=.
(* val loc *)
+ move=> cenv Gamma Sigma l ofs h t a hs bge p vm m vm' m' e' hw he. exists nil.
  by inversion he; subst; split=> //=.
(* var *)
+ admit.
(* const int *)
+ (*move=> Gamma Sigma t sz s a i bge vm m vm' m' e' he; subst.
  inversion he; subst; split=> //=. by apply ty_vali.*) admit.
(* const long *)
+ (*move=> Gamma Sigma t s a i bge vm m vm' m' e' he; subst.
  inversion he; subst; split=> //=. by apply ty_vall.*) admit.
(* const unit *)
+ (* move=> Gamma Sigma t bge vm m vm' m' e' he; subst.
  inversion he; subst; split=> //=. by apply ty_valu.*) admit.
(* app *)
+ (*move=> Gamma Sigma e es rt efs ts ef efs' hte hin htes hin' bge vm m vm' m' e' hw he. 
  inversion he; subst; split=> //=. apply ty_app with ts.
  (* step case *) 
  + by move: (hin bge vm m vm' m' e'0 hw H7)=> [] h1 h2.
  + by apply htes.
  + by move: (hin bge vm m vm' m' e'0 hw H7)=> [] h1 h2.
  admit. (* hard case *) admit.*) admit.
(* ref *)
+ admit.
(* deref *)
+ admit.
(*(* massgn *)
+ move=> Gamma Sigma e e' h t ef a ef' hte hin hte' hin' bge vm m vm' m' e'' hw he.
  inversion he; subst.
  (* step *)
  + move: (hin bge vm m vm' m' e1' hw H6)=> [] hte1' hw'; split=>//=.
    apply ty_massgn with t a. + by apply hte1'. by apply hte'.
  (* value *)
  move: (hin' bge vm m vm' m' e2' hw H6)=> [] h' hw';split=> //=. 
  apply ty_massgn with t a.
  + by apply hte.
  + by apply h'.
  split=> //=.  
  + have htu : type_expr Gamma Sigma (Val Vunit (Ptype Tunit)) nil (Ptype Tunit). + by apply ty_valu.
    have hs : sub_effect [::] (ef ++ ef' ++ [:: Write h]). + by apply sub_effect_nil.
    by have := ty_sub Gamma Sigma (Val Vunit (Ptype Tunit)) nil (Ptype Tunit)  
            (ef ++ ef' ++ [:: Write h]) htu hs.
  by have := assign_preserves_store_well_typed Sigma bge vm' m t0 l ofs bf v m' hw H3 H7.
(* uop *)
+ move=> Gamma Sigma op e ef t hrt hut hte hin bge vm m vm' m' e' hw he.
  inversion he; subst.
  (* step *)
  + move: (hin bge vm m vm' m' e'0 hw H7)=> [] h1 h2. 
    split=> //=. apply ty_uop. + by apply hrt. + by apply hut.
    by apply h1.
  (* value *)
  + by have := val_uop_type_preserve Gamma Sigma ef t op v ct g g' i m' 
            v' v'' hte H4 H8 H9.
(* bop *)
+ move=> Gamma Sigma op e ef t e' hrt hut hte hin hte' hin' bge vm m vm' m' e'' hw he.
  inversion he; subst.
  (* step *)       
  + move: (hin bge vm m vm' m' e1' hw H8)=> [] hte1' hw'; split=> //=. by apply ty_bop.
  (* value *)
  move: (hin' bge vm m vm' m' e2' hw H8)=> [] h1 h2. 
  split=> //=. apply ty_bop. + by apply hrt. + by apply hut. + by apply hte.
  by apply h1.
  split=> //=. have htop := type_bop_inject Gamma Sigma (Val v1 t) (Val v2 t) t ef op hrt hut hte hte'.
  by have := val_bop_type_preserve Gamma Sigma cenv op v1 v2 ef t ct g g' i m'
          v v' htop H8 H9 H10.
(* bind *)
+ move=> Gamma Sigma x t e e' t' ef ef' hte hin htx hin' bge vm m vm' m' e'' hw he''.
  inversion he''; subst.
  (* step *)
  + move: (hin bge vm m vm' m' e1' hw H9)=> [] hte1' hw'; split=> //=. by apply ty_bind.
  (* value *)
  by have := subst_preservation Gamma Sigma x t (Val v1 t) e' ef' ef (typeof_expr e') htx hte.
(* cond *)
+ move=> Gamma Sigma e1 e2 e3 tb t ef1 ef2 hte1 hin1 htb hte2 hin2 hte3 hin3 bge vm m vm' m' e'
         hw he. inversion he; subst.
  (* step e1 *)
  + move: (hin1 bge vm m vm' m' e1' hw H8)=> [] hin1' hw'; split=> //=. 
    by apply ty_cond with tb; auto.
  (* e1 is true *)
  + split=> //=. apply ty_sub with ef2.
    + by apply hte2. 
    by apply suffix_sub_effect.
  (* e1 is false *)
  split=> //=. apply ty_sub with ef2.
  + by apply hte3.
  by apply suffix_sub_effect.
(* unit *)
+ move=> Gamma Sigma bge vm m vm' m' e' hw he. inversion he; subst; split=> //=.
  by apply ty_valu.
(* addr *)
+ move=> Gamma Sigma l ofs h t' a hs bge vm m vm' m' e' hw he. inversion he; subst.
  split=> //=. by apply ty_valloc.
(* ext *)
+ move=> Gamma Sigma exf ts es ef rt hrt [] hut hft hts htes hin bge vm m vm' m' e' hw he; subst.
  inversion he; subst. move: (hin bge vm m vm' m'0 vs hw H5)=> [] h1 h2. 
  by have [h11 h12] := well_typed_res_ext Gamma Sigma bge bge exf g cef g' i' vm' m'0 m'
          (transBeePL_values_cvalues (extract_values_exprs vs)) vres bv ef t hut hft H9 H10 H11.
(* sub *)
+ move=> Gamma Sigma e ef t ef' hte hin hs bge vm m vm' m' e' hw he.
  move: (hin bge vm m vm' m' e' hw he)=> [] he'' hw'; split=> //=.
  by apply ty_sub with ef.
(* nil *)
+ move=> Gamma Sigma bge vm m vm' m' es' hw hes. inversion hes; subst; split=> //=. 
  by apply ty_nil.
(* cons *)
move=> Gamma Sigma e es ef efs t ts hte hin htes hins bge vm m vm' m' es' hw hes.
inversion hes; subst.
+ move: (hin bge vm m vm' m' e' hw H6)=> [] h11 h12; split=> //=. by apply ty_cons. 
move: (hins bge vm m vm' m' vs hw H6)=> [] h11 h12. split=> //=. apply ty_cons.
+ by move: (hin bge vm m vm' m' (Val v t0)).
by apply h11.*)
Admitted.

(**** Multi step preservation ****)
Lemma multi_preservation_ssem_expr_exprs: 
(forall cenv Gamma Sigma es efs ts bge p vm m vm' m' es' n, 
    type_exprs cenv Gamma Sigma es efs ts ->
    store_well_typed cenv Gamma Sigma bge vm m ->
    ssem_closures bge p vm m es n m' vm' es' ->
    exists efs', type_exprs cenv Gamma Sigma es' efs' ts /\ 
                 sub_effect efs' efs /\
                 store_well_typed cenv Gamma Sigma bge vm' m') /\
(forall cenv Gamma Sigma e ef t bge p vm m vm' m' e' n, 
    type_expr cenv Gamma Sigma e ef t ->
    store_well_typed cenv Gamma Sigma bge vm m ->
    ssem_closure bge p vm m e n m' vm' e' ->
    exists ef', type_expr cenv Gamma Sigma e' ef' t /\ sub_effect ef' ef /\
               store_well_typed cenv Gamma Sigma bge vm' m').
Proof.
Admitted.

(* Stateful effects cannot be discarded :
   Expressions like ref, deref, massgn cannot discard the stateful effect even in the case 
   where it reduces to value *)
Lemma stateful_effects_preserved : 
(forall cenv Gamma Sigma es efs ts bge p vm m vm' m' es' efs' ts', 
        type_exprs cenv Gamma Sigma es efs ts ->
        is_stateful_exprs es = true /\ is_stateful_effect efs = true ->
        ssem_exprs bge p vm m es m' vm' es' ->
        type_exprs cenv Gamma Sigma es' efs' ts' ->
        is_stateful_effect efs') /\
(forall cenv Gamma Sigma e ef t bge p vm m vm' m' e' ef' t', 
        type_expr cenv Gamma Sigma e ef t ->
        is_stateful_expr e = true /\ is_stateful_effect ef = true ->
        ssem_expr bge p vm m e m' vm' e' ->
        type_expr cenv Gamma Sigma e' ef' t' ->
        is_stateful_effect ef').
Proof.
suff : (forall cenv Gamma Sigma es efs ts, 
        type_exprs cenv Gamma Sigma es efs ts ->
        forall bge p vm m vm' m' es' efs' ts', 
        is_stateful_exprs es = true /\ is_stateful_effect efs = true ->
        ssem_exprs bge p vm m es m' vm' es' ->
        type_exprs cenv Gamma Sigma es' efs' ts' ->
        is_stateful_effect efs') /\
        (forall cenv Gamma Sigma e ef t, 
        type_expr cenv Gamma Sigma e ef t ->
        forall bge p vm m vm' m' e' ef' t', 
        is_stateful_expr e = true /\ is_stateful_effect ef = true ->
        ssem_expr bge p vm m e m' vm' e' ->
        type_expr cenv Gamma Sigma e' ef' t' ->
        is_stateful_effect ef').
+ move=> [] ih ih'. admit.
Admitted.


(***** Normalization ******)
(* A well typed program takes multistep to produce a value *)
Lemma normalization :
(forall cenv Gamma Sigma es efs ts bge p vm m m' vm' es' n, 
 type_exprs cenv Gamma Sigma es efs ts ->
 store_well_typed cenv Gamma Sigma bge vm m ->
 ssem_closures bge p vm m es n m' vm' es' 
 /\ is_values es' 
 /\ store_well_typed cenv Gamma Sigma bge vm' m') /\
(forall cenv Gamma Sigma e ef t bge p vm m m' vm' e' n, 
 type_expr cenv Gamma Sigma e ef t ->
 store_well_typed cenv Gamma Sigma bge vm m ->
 ssem_closure bge p vm m e n m' vm' e' /\ is_value e /\
 store_well_typed cenv Gamma Sigma bge vm' m').
Proof.
Admitted.

(***** With respect to big step semantics *****)

(*
(* Complete me *) (* Medium level *)
Lemma cval_bval_type_eq : forall v ct v' bt g g' i,
Values.Val.has_type v (typ_of_type ct) ->
transC_val_bplvalue v = Errors.OK v' ->
transBeePL_type bt g = SimplExpr.Res ct g' i ->
wtypeof_value v' (wtype_of_type bt). 
Proof.
Admitted.

(* Complete Me *)
Lemma uop_type_preserve : forall uop v ct m v',
Cop.sem_unary_operation uop v ct m = Some v' ->
Values.Val.has_type v' (typ_of_type ct).
Proof.
Admitted.

(* Complete Me *)
Lemma eq_uop_types : forall uop t g g' i v ct m v' v'',
transBeePL_type t g = SimplExpr.Res ct g' i ->
Cop.sem_unary_operation uop v ct m = Some v' ->
Values.Val.has_type v' (typ_of_type ct) ->
transC_val_bplvalue v' = Errors.OK v'' -> 
wtypeof_value v'' (wtype_of_type t).
Proof.
Admitted.

(* Complete Me *)
Lemma bop_type_preserve : forall bge bop v1 ct1 v2 ct2 m v,
Cop.sem_binary_operation bge bop v1 ct1 v2 ct2 m = Some v ->
Values.Val.has_type v (typ_of_type ct1) /\
Values.Val.has_type v (typ_of_type ct2).
Proof.
Admitted.

Lemma eq_bop_types : forall cenv v1 t1 g g' i v2 t2 g'' i' ct1 ct2 op m v v',
transBeePL_type t1 g = SimplExpr.Res ct1 g' i ->
transBeePL_type t2 g' = SimplExpr.Res ct2 g'' i' ->
Cop.sem_binary_operation cenv op v1 ct1 v2 ct2 m = Some v ->
transC_val_bplvalue v = Errors.OK v' ->
Values.Val.has_type v (typ_of_type ct1) ->
Values.Val.has_type v (typ_of_type ct2) ->
wtypeof_value v' (wtype_of_type t1) /\ wtypeof_value v' (wtype_of_type t2).
Proof.
Admitted.

Lemma type_to_wtype : forall v t,
typeof_value v t ->
wtypeof_value v (wtype_of_type t).
Proof.
move=> v t. case: t=> //=.
+ move=> p. case: p=> //=.
  + move=> i s a. by case: v=> //=.
  move=> s a. by case: v=> //=.
+ move=> h b a. by case: v=> //=.
move=> es e t. by case: v=> //=.
Qed. *)
    
(*** Definition memory_well_formedness : forall Sigma l, m, 
     Sigma ! l = Reftype h bt a -> 
     deref m bt l = v ->
     v != loc. ***)   

(**** Lemma memory_preserve : forall 
      well_formed Sigma l m ->
      sem m e m' e' ->
      well_formed Sigma l m' ****)

(**** Add codnitions in semantics for division in BeePL 
      https://people.rennes.inria.fr/Frederic.Besson/compcertSFI.pdf *****)

(**** Runtime rejection : add exit ****)

 



