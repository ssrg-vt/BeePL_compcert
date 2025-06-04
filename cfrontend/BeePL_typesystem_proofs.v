Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import compcert.common.Errors Initializersproof Cstrategy BeePL_auxlemmas Coqlib Errors Memory.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import BeePL_sem BeePL_typesystem BeePL_compiler_proofs BeePL_values BeePL_notations.
Require Import BeePL_memory_proofs BeePL_operators_proofs.

From mathcomp Require Import all_ssreflect.

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
(* val unit *) (* complete *)
+ move=> cenv Gamma Sigma bge vm m hw. by left.
(* val bool *) (* complete *)
+ move=> cenv Gamma Sigma b bge vm m hw. by left.
(* val int *) (* complete *)
+ move=> cenv Gamma Sigma i sz s a bge vm m hw. by left.
(* val long *) (* complete *)
+ move=> cenv Gamma Sigma i s a bge vm m hw. by left.
(* val loc *) (* complete *)
+ move=> cenv Gamma Sigma l ofs h t a bge vm m hw. by left.
(* val option *) (* complete *)
+ move=> cenv Gamma Sigma o pt bge p vm m hw. by left.
(* var *) (* complete *)
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
(* const int *) (* complete *)
+ move=> cenv Gamma Sigma t sz a i bge p vm m hw. right.
  exists m. exists vm. exists (Val (Vint i) (Vtype (Tint t sz a))). 
  split=> //=. by apply ssem_consti.
(* const long *) (* complete *)
+ move=> cenv Gamma Sigma t s i bge p vm m hw. right.
  exists m. exists vm. exists (Val (Vint64 i) (Vtype (Tlong t s))). 
  split=> //=. by apply ssem_constl.
(* const uint *) (* complete *)
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
  exists (Prim Massgn [:: e''; e'] (Ptype Tunit)). split=> //=. by apply ssem_massgn1. *)
admit.
(* notbool *) (* complete *)
+ move=> cenv Gamma Sigma e ef hte hin bge p vm m hw. 
  move: (hin bge p vm m hw)=> [].
  (* value *)
  + move=> hv. right. case: e hte hin hv=> //= v t hte hin _.
    have hteq := type_val_reflx cenv Gamma Sigma v t ef (Vtype Tbool) hte; subst.
    have [v' [v'' [hs [hd hv]]]] := well_formed_notbool cenv Gamma Sigma bge vm m v ef hw hte.
    exists m. exists vm. exists (Val v'' (Vtype Tbool)). split=> //=.
    apply ssem_uop2 with v' (transBeePL_type (Vtype Tbool)); auto.
  (* step *)
  move=> [] m' [] vm' [] e' [] he' hw'. right.
  exists m'. exists vm'. exists (Prim (Uop Cop.Onotbool) [:: e'] (typeof_expr e)). split=> //=.
  have h := type_rel_typeof cenv Gamma Sigma e ef (Vtype Tbool) hte. rewrite -h.
  by apply ssem_uop1. 
(* notint *) (* complete *)
+ move=> cenv Gamma Sigma e ef t hteq hte hin bge p vm m hw. 
  move: (hin bge p vm m hw)=> [].
  (* value *)
  + move=> hv. right. case: e hte hin hv=> //= v t' hte hin _.
    have hte' := type_val_reflx cenv Gamma Sigma v t' ef t hte; subst.
    have [v' [v'' [ho [hd hv]]]] :=  well_formed_notint cenv Gamma Sigma bge vm m v t ef hw hte hteq.
    exists m. exists vm. exists (Val v'' t). split=> //=.
    apply ssem_uop2 with v' (transBeePL_type t); auto.
  (* step *)
  move=> [] m' [] vm' [] e' [] he' hw'. right.
  exists m'. exists vm'. exists (Prim (Uop Cop.Onotint) [:: e'] (typeof_expr e)). split=> //=.
  have h := type_rel_typeof cenv Gamma Sigma e ef t hte. rewrite -h.
  by apply ssem_uop1.
(* neg *) (* complete *)
+ move=> cenv Gamma Sigma e ef t hteq hte hin bge p vm m hw. 
  move: (hin bge p vm m hw)=> [].
  (* value *)
  + move=> hv. right. case: e hte hin hv=> //= v t' hte hin _.
    have hte' := type_val_reflx cenv Gamma Sigma v t' ef t hte; subst.
    have [v' [v'' [ho [hd hv]]]] :=  well_formed_neg cenv Gamma Sigma bge vm m v t ef hw hte hteq.
    exists m. exists vm. exists (Val v'' t). split=> //=.
    apply ssem_uop2 with v' (transBeePL_type t); auto.
  (* step *)
  move=> [] m' [] vm' [] e' [] he' hw'. right.
  exists m'. exists vm'. exists (Prim (Uop Cop.Oneg) [:: e'] (typeof_expr e)). split=> //=.
  have h := type_rel_typeof cenv Gamma Sigma e ef t hte. rewrite -h.
  by apply ssem_uop1.
(* Oadd *)
+ move=> cenv Gamma Sigma e ef1 ef2 t e'' ht hte hin hte'' hin' bge p vm m hw.
  move: (hin bge p vm m hw)=> []. have [zv hr] := construct_zero t ht.
  (* e is a value *)
  + move=> hv. case: e hte hin hv=> //= v1 t1 hte hin _.
    move: (hin' bge p vm m hw)=> [].
    (* e' is a value *)
    + move=> hv'. case: e'' hte'' hin' hv'=> //= v2 t2 hte'' hin' hv'. right.
      have hte' := type_val_reflx cenv Gamma Sigma v1 t1 ef1 t hte; subst.
      have hte' := type_val_reflx cenv Gamma Sigma v2 t2 ef2 t hte''; subst.
      have [v' [v'' [ho [] hun htv ]]] := well_formed_add (bcomposite_composite_env cenv) cenv Gamma 
                       Sigma bge vm m v1 t ef1 v2 ef2 hw hte hte'' ht.
      have [s hs] := signedness_exists t ht.
      exists m. exists vm. exists (Val v'' t). split=> //=. 
      + by apply ssem_bop3_safe with (bcomposite_composite_env cenv) v'
        (transBeePL_type t) s; auto. 
    (* step *)
    move=> [] m' [] vm' [] e' [] he' hw'. right.
    exists m'. exists vm'. exists (Prim (Bop Cop.Oadd) [:: Val v1 t1; e'] t1). 
    split=> //=. have h := type_rel_typeof cenv Gamma Sigma (Val v1 t1) ef1 t hte. 
    rewrite -h. by apply ssem_bop2.
  (* step *)
  move=> [] m' [] vm' [] e' [] he' hw'. right.
  exists m'. exists vm'. exists (Prim (Bop Cop.Oadd) [:: e'; e''] (typeof_expr e)). 
  split=> //=. have h := type_rel_typeof cenv Gamma Sigma e ef1 t hte. 
  rewrite -h. by apply ssem_bop1.
(* Osub *)
+ move=> cenv Gamma Sigma e ef1 ef2 t e'' ht hte hin hte'' hin' bge p vm m hw.
  move: (hin bge p vm m hw)=> []. have [zv hr] := construct_zero t ht.
  (* e is a value *)
  + move=> hv. case: e hte hin hv=> //= v1 t1 hte hin _.
    move: (hin' bge p vm m hw)=> [].
    (* e' is a value *)
    + move=> hv'. case: e'' hte'' hin' hv'=> //= v2 t2 hte'' hin' hv'. right.
      have hte' := type_val_reflx cenv Gamma Sigma v1 t1 ef1 t hte; subst.
      have hte' := type_val_reflx cenv Gamma Sigma v2 t2 ef2 t hte''; subst.
      have [v' [v'' [ho [] hun htv ]]] := well_formed_sub (bcomposite_composite_env cenv) cenv Gamma 
                       Sigma bge vm m v1 t ef1 v2 ef2 hw hte hte'' ht.
      have [s hs] := signedness_exists t ht.
      exists m. exists vm. exists (Val v'' t). split=> //=. 
      + by apply ssem_bop3_safe with (bcomposite_composite_env cenv) v'
        (transBeePL_type t) s; auto. 
    (* step *)
    move=> [] m' [] vm' [] e' [] he' hw'. right.
    exists m'. exists vm'. exists (Prim (Bop Cop.Osub) [:: Val v1 t1; e'] t1). 
    split=> //=. have h := type_rel_typeof cenv Gamma Sigma (Val v1 t1) ef1 t hte. 
    rewrite -h. by apply ssem_bop2.
  (* step *)
  move=> [] m' [] vm' [] e' [] he' hw'. right.
  exists m'. exists vm'. exists (Prim (Bop Cop.Osub) [:: e'; e''] (typeof_expr e)). 
  split=> //=. have h := type_rel_typeof cenv Gamma Sigma e ef1 t hte. 
  rewrite -h. by apply ssem_bop1.
(* Omul *)
+ move=> cenv Gamma Sigma e ef1 ef2 t e'' ht hte hin hte'' hin' bge p vm m hw.
  move: (hin bge p vm m hw)=> []. have [zv hr] := construct_zero t ht.
  (* e is a value *)
  + move=> hv. case: e hte hin hv=> //= v1 t1 hte hin _.
    move: (hin' bge p vm m hw)=> [].
    (* e' is a value *)
    + move=> hv'. case: e'' hte'' hin' hv'=> //= v2 t2 hte'' hin' hv'. right.
      have hte' := type_val_reflx cenv Gamma Sigma v1 t1 ef1 t hte; subst.
      have hte' := type_val_reflx cenv Gamma Sigma v2 t2 ef2 t hte''; subst.
      have [v' [v'' [ho [] hun htv ]]] := well_formed_mul (bcomposite_composite_env cenv) cenv Gamma 
                       Sigma bge vm m v1 t ef1 v2 ef2 hw hte hte'' ht.
      have [s hs] := signedness_exists t ht.
      exists m. exists vm. exists (Val v'' t). split=> //=. 
      + by apply ssem_bop3_safe with (bcomposite_composite_env cenv) v'
        (transBeePL_type t) s; auto. 
    (* step *)
    move=> [] m' [] vm' [] e' [] he' hw'. right.
    exists m'. exists vm'. exists (Prim (Bop Cop.Omul) [:: Val v1 t1; e'] t1). 
    split=> //=. have h := type_rel_typeof cenv Gamma Sigma (Val v1 t1) ef1 t hte. 
    rewrite -h. by apply ssem_bop2.
  (* step *)
  move=> [] m' [] vm' [] e' [] he' hw'. right.
  exists m'. exists vm'. exists (Prim (Bop Cop.Omul) [:: e'; e''] (typeof_expr e)). 
  split=> //=. have h := type_rel_typeof cenv Gamma Sigma e ef1 t hte. 
  rewrite -h. by apply ssem_bop1.
(* Odiv *)
+ move=> cenv Gamma Sigma e ef1 ef2 t e'' ht hte hin hte'' hin' bge p vm m hw.
  move: (hin bge p vm m hw)=> []. have [zv hr] := construct_zero t ht.
  (* e is a value *)
  + move=> hv. case: e hte hin hv=> //= v1 t1 hte hin _.
    move: (hin' bge p vm m hw)=> [].
    (* e' is a value *)
    + move=> hv'. case: e'' hte'' hin' hv'=> //= v2 t2 hte'' hin' hv'. right.
      have hte' := type_val_reflx cenv Gamma Sigma v1 t1 ef1 t hte; subst.
      have hte' := type_val_reflx cenv Gamma Sigma v2 t2 ef2 t hte''; subst.
      have [s hs] := signedness_exists t ht.
      case hc: (check_unsafe_op Cop.Odiv s v1 v2)=> [| ]//=.
      + exists m. exists vm. exists (Val zv t). split=> //=.
        by apply ssem_bop3_unsafe with (transBeePL_type t) s; auto.
      have [v' [v'' [ho [hu h]]]]:= well_formed_div (bcomposite_composite_env cenv) cenv Gamma Sigma bge vm m v1 t ef1
              v2 ef2 s hw hte hte'' ht hs hc.
     exists m. exists vm. exists (Val v'' t). split=> //=.
     by apply ssem_bop3_safe with (bcomposite_composite_env cenv) v'
        (transBeePL_type t) s; auto. 
    (* step *)
    move=> [] m' [] vm' [] e' [] he' hw'. right.
    exists m'. exists vm'. exists (Prim (Bop Cop.Odiv) [:: Val v1 t1; e'] t1). 
    split=> //=. have h := type_rel_typeof cenv Gamma Sigma (Val v1 t1) ef1 t hte. 
    rewrite -h. by apply ssem_bop2.
  (* step *)
  move=> [] m' [] vm' [] e' [] he' hw'. right.
  exists m'. exists vm'. exists (Prim (Bop Cop.Odiv) [:: e'; e''] (typeof_expr e)). 
  split=> //=. have h := type_rel_typeof cenv Gamma Sigma e ef1 t hte. 
  rewrite -h. by apply ssem_bop1.

(*
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



 



