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
  + move: (H v t hteq)=> [] l' [] t' [] v'.
    move=> [] hvm [] hteq' [] hs hd; subst.
    exists m. exists vm. exists (Val v' t'). split=> //=.
    eapply ssem_lvar. + by apply hvm. + by apply hd.
  (* gvar *)
  move: (H v t hteq).
  move=> [] l' [] v' [] hs [] hg [] hs' hd. 
  exists m. exists vm. exists (Val v' t). split=> //=. 
  apply ssem_gbvar with l'. + by apply hs. + by apply hg.
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
+ move=> cenv Gamma Sigma e ef h bt a hte hin bge p vm m hw.
  move: (hin bge p vm m hw)=> [] he.
  (* is value *)
  + right. case: e hte hin he=> //= v t hte hin _.
    have hvt := type_rel_typeof_val cenv Gamma Sigma v ef t (construct_type_btype bt) hte.
    have [m' [b] ha] := mem_alloc_total m 0 (sizeof_type (prog_comp_env p) t).
    have hw'' := store_well_typed_mem_alloc cenv Gamma Sigma bge vm m 0 (sizeof_type (prog_comp_env p) t) m' b hw ha. 
    have [m'' [] chunk [] v' [] htv [] hc [] hs hws] := ref_allocation_succeeds cenv Gamma Sigma p bge vm m v t (m', b) hw hvt ha. 
    exists m''. exists vm. 
    exists (Val (Vloc (Mem.alloc m 0 (sizeof_type (prog_comp_env p) (construct_type_btype bt))).2 Ptrofs.zero) 
              (Ptrtype (Reftype h bt a))). split=> //=.
    apply type_val_reflx in hte; subst.
    apply ssem_ref2 with chunk (Mem.alloc m 0 (sizeof_type (prog_comp_env p) (construct_type_btype bt))).2 Sigma
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
+ move=> cenv Gamma Sigma e ef pt h hte hin ho bge p vm m hw.
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
      case: H=> H1 H2. move: (H1 l ofs (Reftype h' bt a) hl)=> [] chunk [] hvl hc.
      have [v hd] := safe_deref_valid_pointers bge Sigma m l ofs (Reftype h' bt a) chunk hl hc hvl.
      exists m. exists vm. exists (Val v (get_data_type (Reftype h' bt a))). split.
      by apply ssem_deref2. by apply hsw.
    (* option *) (* deref does not allow pointer coming from option type until it is gone through match *)
    + move=> o hte hin.
      have [pt' [h1 h2]] := type_infer_option cenv Gamma Sigma ef o t (Ptrtype pt) hte.
      case: h2=> h2'. by rewrite h2' in ho.
  (* step *)
  move: (hin bge p vm m hw)=> hin'. move=> [] m' [] vm' [] e' [] he hs. right.
  exists m'. exists vm'. exists (Prim Deref [:: e'] (get_data_type pt)). split=> //=. 
  apply ssem_deref1. by apply he.
(* massgn *)
+ move=> cenv Gamma Sigma e e' h pt ef ef' hte hin ho hte' hin' bge p vm m hw. right.
  move: (hin bge p vm m hw)=> [].
  (* e is a value *)
  + move=> hve. case: e hte hin hve=> //= v t hte hin _.
    case: v hte hin=> //=.
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
    (* ptr *)
    + move=> l ofs hte hin. move: (hin' bge p vm m hw)=> [].
      (* e' is a value *)
      + move=> hv'. pose proof hw as hsw. case: hw=> [] hw1 [] hw2 hw3.
        have [h' [bt [a [m' [hpt hl ]]]]] := type_infer_loc cenv Gamma Sigma l ofs 
                                                ef t (Ptrtype pt) hte; subst.
        inversion hw2. case: hpt=> [] hpteq; subst.
        case: H=> H1 H2. move: (H1 l ofs (Reftype h' bt a) hl)=> [] chunk [] hvl hc.
        case: e' hte' hin' hv'=> //= v t hte' hin' _. case: bt ho hin hte hl hc hte'=> //= pt _ hin hte hl [] hc hte'; subst.
        have [bf [m' [ha hw']]] := safe_assgn_valid_pointers cenv Gamma Sigma bge vm m l ofs (Reftype h' (Bprim pt) a) v (chunk_of_ptype pt) hsw hl erefl hvl. 
        exists m'. exists vm. exists (Val Vunit Utype). split=> //=.
        have hteq := type_val_reflx cenv Gamma Sigma v t ef' (Vtype pt) hte'; subst.
        have hteq: (get_data_type (Reftype h' (Bprim pt) a)) = (Vtype pt). + by auto; subst.
        by apply ssem_massgn3 with bf.
      (* e' steps *)
      move=> [] m' [] vm' [] e'' [] he'' hw'. exists m'. exists vm'. exists (Prim Massgn [:: Val (Vloc l ofs) t; e''] tunit).
      split=> //=. 
      have hteq := type_val_reflx cenv Gamma Sigma (Vloc l ofs) t ef (Ptrtype pt) hte; subst.         
      by apply ssem_massgn2. 
    (* option *) (* massgn does not allow pointer coming from option type until it is gone through match *)
    + move=> o hte hin.
      have [pt' [h1 h2]] := type_infer_option cenv Gamma Sigma ef o t (Ptrtype pt) hte.
      case: h2=> h2'. by rewrite h2' in ho.
 (* e steps *)
 move=> [] m' [] vm' [] e'' [] he'' hw'. exists m'. exists vm'. 
 exists (Prim Massgn [:: e''; e'] tunit). split=> //=.
 by apply ssem_massgn1.
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
(* Omod *)
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
      case hc: (check_unsafe_op Cop.Omod s v1 v2)=> [| ]//=.
      + exists m. exists vm. exists (Val zv t). split=> //=.
        by apply ssem_bop3_unsafe with (transBeePL_type t) s; auto.
      have [v' [v'' [ho [hu h]]]]:= well_formed_mod (bcomposite_composite_env cenv) cenv Gamma Sigma bge vm m v1 t ef1
              v2 ef2 s hw hte hte'' ht hs hc.
     exists m. exists vm. exists (Val v'' t). split=> //=.
     by apply ssem_bop3_safe with (bcomposite_composite_env cenv) v'
        (transBeePL_type t) s; auto. 
    (* step *)
    move=> [] m' [] vm' [] e' [] he' hw'. right.
    exists m'. exists vm'. exists (Prim (Bop Cop.Omod) [:: Val v1 t1; e'] t1). 
    split=> //=. have h := type_rel_typeof cenv Gamma Sigma (Val v1 t1) ef1 t hte. 
    rewrite -h. by apply ssem_bop2.
  (* step *)
  move=> [] m' [] vm' [] e' [] he' hw'. right.
  exists m'. exists vm'. exists (Prim (Bop Cop.Omod) [:: e'; e''] (typeof_expr e)). 
  split=> //=. have h := type_rel_typeof cenv Gamma Sigma e ef1 t hte. 
  rewrite -h. by apply ssem_bop1.
(* Oand *)
+ admit. (* provable *)
(* Oor *)
+ admit. (* provable *)
(* Oxor *)
+ admit. (* provable *)
(* Oshl *)
+ admit.
(* Oshr *)
+ admit.
(* Oeq *)
+ admit. (* provable *)
(* One *)
+ admit. (* provable *)
(* Olt *)
+ admit. (* provable *)
(* Ogt *)
+ admit. (* provable *)
(* Ole *)
+ admit. (* provable *)
(* Oge *)
+ admit. (* provable *)
(* Bind *)
+ admit.
(* Cond *)
+ move=> cenv Gamma Sigma e1 e2 e3 t ef1 ef2 hte1 hin1 hte2 hin2 hte3 hin3 bge p vm m hw.
  right. move: (hin1 bge p vm m hw)=> [].
  (* e1 is value *)
  + move=> hv1. case: e1 hte1 hin1 hv1=> //= v1 t1. case: v1=> //=.
    + move=> ht. have [h1 h2] := type_infer_vunit cenv Gamma Sigma ef1 t1 (Vtype Tbool) ht; subst.
      by inversion ht.
    + move=> b ht hin1 _. case: b ht hin1=> //= ht hin1.
      (* true *)
      + exists m. exists vm. exists e2. split=> //=.
        have hte2' := type_rel_typeof cenv Gamma Sigma e2 ef2 t hte2; subst.
        have h := type_val_reflx cenv Gamma Sigma (Vbool true) t1 ef1 (Vtype Tbool) ht; subst.
        by apply ssem_ctrue.
      (* false *)
      exists m. exists vm. exists e3. split=> //=.
      have hte2' := type_rel_typeof cenv Gamma Sigma e3 ef2 t hte3; subst.
      have h := type_val_reflx cenv Gamma Sigma (Vbool false) t1 ef1 (Vtype Tbool) ht; subst.
      by apply ssem_cfalse.
    (* int *)
    + move=> i hte hin. 
      by have [h1 [sz] [s] [] h2 h3] := type_infer_int cenv Gamma Sigma i ef1 t1 (Vtype Tbool) hte; subst.
    (* long *)
    + move=> l hte hin. 
      by have [s [] a' [] h1 h2] := type_infer_long cenv Gamma Sigma l ef1 t1 (Vtype Tbool) hte.
    (* loc *)
    + move=> l ofs hte hin.
      have [h [bt [a [h1 [h2 h3]]]]] := type_infer_loc cenv Gamma Sigma l ofs ef1 t1 (Vtype Tbool) hte; subst.
      by inversion hte.
    (* option *)
    move=> o hte hin _.
    have [pt [h1 h2]] := type_infer_option cenv Gamma Sigma ef1 o t1 (Vtype Tbool) hte; subst. by inversion hte.
 (* e1 steps *)
 move=> [] m' [] vm' [] e1' [] he' hw'. exists m'. exists vm'. exists (Cond e1' e2 e3 t). split=> //=.
 have hte2' := type_rel_typeof cenv Gamma Sigma e2 ef2 t hte2; subst. by apply ssem_cond.
(* Unit *)
+ move=> cenv Gamma Sigma bge p vm m hw. right. exists m. exists vm. exists (Val Vunit Utype). split=> //=.
  by apply ssem_ut.
(* Addr *)
+ move=> cenv Gamma Sigma l ofs h t a hl bge p vm m hw. right.
  exists m. exists vm. exists (Val (Vloc l.(lname) ofs) (Ptrtype (Reftype h t a))). split=> //=.
  by apply ssem_adr.
(* Sinit *)
+ admit.
(* Sfield *)
+ admit.
(* For *)
+ (*move=> cenv Gamma Sigma e1 e2 d e ef1 t1 ef2 t2 fv1 fv2 fv ef t hte1 hin1 hte2 hin2 hte hin hteq hteq' hf1 hf2 hf3 hd1 hd2.
  move=> bge p vm m hw. right. move: (hin1 bge p vm m hw)=> [].
  (* e1 is a value *)
  + move=> hv1. case: e1 hte1 hin1 hf1 hv1=> //= v tv hte1 hin1 hf1 _; subst. 
    move: (hin2 bge p vm m hw)=> [].
    (* e2 is a value *)
    + move=> hv2. case: e2 hte2 hin2 hd2 hv2=> //= v' tv' hte2 hin2 hd2 _; subst.*)
      
  admit.
(* Enone *)
+ admit.
(* Esome *)
+ admit.
(* Match *)
+ admit.
(* nil *)
+ admit.
admit.
Admitted.

(**** Substitution preserves typing ****)
Lemma subst_preservation : forall cenv Gamma Sigma x t se e ef' ef t', 
type_expr cenv (extend_context Gamma x t) Sigma e ef' t' ->
type_expr cenv Gamma Sigma se ef t ->
exists ef'', type_expr cenv Gamma Sigma (subst x se e) ef'' t' /\ sub_effect ef'' (ef ++ ef').
Proof.
move=> cenv Gamma Sigma x t se e. move: cenv Gamma Sigma se x t.
induction e=> //=. 
(* val *)
+ admit.
(* var *)
+ move=> cenv Gamma Sigma se x t1 ef' ef yt hte htse. case: ifP=> //=.
  (* x = y *)
  + move=> h. exists ef. admit. (* provable *)
  admit. (* provable *)
(* const *)
+ admit. (* provable *)
(* app *)
+ move=> cenv Gamma Sigma se x t1 ef' ef t' hta htse. 
  admit. (* not provable, as we have no information about the effect of body of the function *)
(* prim *)
+ move=> cenv Gamma Sigma se x t1 ef' ef t2. case: b=> //=.
 (* ref *)
 + move=> hte htse. inversion hte; subst.
   exists (ef0 ++ [:: Alloc h]). split=> //=.
   + apply ty_ref.
Admitted.

(* we need extra assertion that value cannot be a pointer because 
   in C, they allow it and we use deref_addr from CompCert *)
Lemma well_typed_val_expr : forall cenv Gamma Sigma v t ef bf m l ofs,
deref_addr cenv t m l ofs bf v ->
type_expr cenv Gamma Sigma (Val v t) ef t.
Proof.
(*move=> cenv Gamma Sigma v t ef bf m l ofs hd.
case: v hd=>[ | b | i | i64 | l' ofs'| o] hd //=; subst.
(* unit *)
+ have ht : type_expr cenv Gamma Sigma (Val Vunit tunit) nil tunit.  
  + by apply ty_valu. *)

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
(* val option *)
+ move=> cenv Gamma Sigma o t bge p vm m vm' m' e' hw he. by inversion he.
(* var *)
+ move=> cenv Gamma Sigma x t hxt bge p vm m vm' m' e' hw he. inversion he; subst.
  (* local *)
  + exists nil. split=> //=. admit.
  (* global *)
  + exists nil. split=> //=. (*by apply well_typed_val_expr with Full m' l ofs.*) admit.
(* const int *)
+ move=> Gamma Sigma t sz s a i bge p vm m vm' m' e' hw he; subst.
  inversion he; subst. exists nil. split=> //=. by apply ty_vali. 
(* const long *)
+ move=> Gamma Sigma t s a i bge p vm m vm' m' e' hw he; subst.
  inversion he; subst. exists nil. split=> //=. by apply ty_vall. 
(* const unit *)
+ move=> Gamma Sigma t bge p vm m vm' m' e' hw he; subst.
  inversion he; subst; exists nil. split=> //=. by apply ty_valu.  
(* app *)
+ (*move=> Gamma Sigma e es rt efs ts ef efs' hte hin htes hin' bge vm m vm' m' e' hw he. 
  inversion he; subst; split=> //=. apply ty_app with ts.
  (* step case *) 
  + by move: (hin bge vm m vm' m' e'0 hw H7)=> [] h1 h2.
  + by apply htes.
  + by move: (hin bge vm m vm' m' e'0 hw H7)=> [] h1 h2.
  admit. (* hard case *) admit.*) admit.
(* ref *)
+ move=> cenv Gamma Sigma e ef h bt a hte hin bge p vm m vm' m' e' hw he.
  inversion he; subst.
  + admit.
  exists nil. split=> //=. 
  + apply ty_valloc. case: hw=> hw1 [] hw2 hw3.
    inversion hw2. case: H=> h1 h2. admit.
  split=> //=. + by apply sub_effect_nil.
  admit.
(* deref *)
+ 
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



 



