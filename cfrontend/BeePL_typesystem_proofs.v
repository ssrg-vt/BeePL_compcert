Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import compcert.common.Errors Initializersproof Cstrategy BeePL_auxlemmas Coqlib Errors Memory.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import BeePL_sem BeePL_typesystem BeePL_safety BeePL_compiler_proofs.

From mathcomp Require Import all_ssreflect.

(* A well-typed uop always has a semantics that leads to a value. *)
Lemma well_typed_uop : forall Gamma Sigma bge vm v ef t uop m ct g i,
type_expr Gamma Sigma (Prim (Uop uop) ((Val v t) :: nil) t) ef t ->
transBeePL_type t g = Res ct g i ->
interp_safe_conds (gen_safe_cond_expr (Val v t)) Sigma bge vm m ->
exists v', Cop.sem_unary_operation uop (transBeePL_value_cvalue v) ct m = Some v'.
Proof.
move=> Gamma Sigma bge vm v ef t uop m ct g i htv. case: v htv=> //=. 
(* unit *)
+ move=> htv. inversion htv; subst. inversion H8; subst.
  rewrite /transBeePL_type /=. move=> [] hct hw; subst.
  by case: uop htv=> //=.
(* int *)
+ move=> i' hvt. inversion hvt; subst. inversion H8; subst. 
  rewrite /transBeePL_type. move=> [] hct; subst.
  case: uop hvt=> //=.
  (* sem_notbool *)
  + rewrite /Cop.sem_notbool /option_map /=. 
    case hop: (Cop.bool_val (Values.Vint i') (Ctypes.Tint sz s a) m)=> [ vo | ] //=.
    by exists (Values.Val.of_bool (~~ vo)).
  move: hop. rewrite /Cop.bool_val /=. case hc: (Cop.classify_bool (Ctypes.Tint sz s a))=> //=.
  + rewrite /Cop.classify_bool /= in hc. move: hc. by case: sz H4 H6 H7 H8=> //=.
  + rewrite /Cop.classify_bool /= in hc. move: hc. by case: sz H4 H6 H7 H8=> //=.
  + rewrite /Cop.classify_bool /= in hc. move: hc. by case: sz H4 H6 H7 H8=> //=.
  rewrite /Cop.classify_bool /= in hc. move: hc. by case: sz H4 H6 H7 H8=> //=.
  (* sem_notint *)
  + rewrite /Cop.sem_notint /Cop.classify_notint. case: sz H4 H6 H7 H8=> //=.
    + move=> hvt. by exists (Values.Vint (Int.not i')).
    + move=> hvt. by exists  (Values.Vint (Int.not i')).
    + case: s=> //=.
      + by exists (Values.Vint (Int.not i')).
      by exists (Values.Vint (Int.not i')).
    by exists (Values.Vint (Int.not i')).
  (* sem_neg *)
  + rewrite /Cop.sem_neg /Cop.classify_neg. case: sz H4 H6 H7 H8=> //=.
    + by exists (Values.Vint (Int.neg i')).
    + by exists (Values.Vint (Int.neg i')).
    + case: s=> //=. + by exists (Values.Vint (Int.neg i')).
      by exists (Values.Vint (Int.neg i')).
    by exists (Values.Vint (Int.neg i')).
  (* sem_absfloat *)
  + rewrite /Cop.sem_absfloat /Cop.classify_neg /=. case: sz H4 H6 H7 H8=> //=.
    + by exists (Values.Vfloat (Floats.Float.abs (Floats.Float.of_int i'))).
    + by exists (Values.Vfloat (Floats.Float.abs (Floats.Float.of_int i'))).
    + case: s=> //=. + by exists (Values.Vfloat (Floats.Float.abs (Floats.Float.of_int i'))).
      by exists (Values.Vfloat (Floats.Float.abs (Floats.Float.of_intu i'))).
    by exists (Values.Vfloat (Floats.Float.abs (Floats.Float.of_int i'))).
(* long *)
+ move=> i' hvt. inversion hvt; subst. inversion H8; subst. 
  rewrite /transBeePL_type. move=> [] hct; subst.
  case: uop hvt=> //=.
  (* sem_notbool *)
  + rewrite /Cop.sem_notbool /option_map /=. 
    by exists (Values.Val.of_bool (~~ ~~ Int64.eq i' Int64.zero)).
  (* sem_notint *)
  + rewrite /Cop.sem_notint /Cop.classify_notint. by exists (Values.Vlong (Int64.not i')).
  (* sem_neg *)
  + rewrite /Cop.sem_neg /Cop.classify_neg. by exists (Values.Vlong (Int64.neg i')).
  (* sem_absfloat *)
  + rewrite /Cop.sem_absfloat /Cop.classify_neg /=. 
    by exists (Values.Vfloat (Floats.Float.abs (Cop.cast_long_float s i'))).
(* ptr *)
move=> p ofs hvt. inversion hvt; subst. inversion H8; subst. case: uop hvt=> //=.
Qed.

(* Complete Me : Easy *)
Lemma trans_value_uop_success : forall Gamma Sigma ef t uop v ct g g' i m v', 
type_expr Gamma Sigma (Val v t) ef t ->
transBeePL_type t g = Res ct g' i ->
Cop.sem_unary_operation uop (transBeePL_value_cvalue v) ct m = Some v' ->
exists v'', transC_val_bplvalue v' = OK v''.
Proof.
(*move=> Gamma Sigma ef t uop v ct g g' i m v' htv hct hop. case: v htv hop=> //=.
(* int *)
+ case: t hct=> //=.
  + move=> p. case: p=> //=.
    + move=> [] h1 h2; subst. rewrite /Cop.sem_unary_operation. by case: uop=> //=.
    + move=> sz s a [] h1 h2; subst. rewrite /Cop.sem_unary_operation. case: uop=> //=.
      + rewrite /Cop.sem_notbool /= /option_map /=.
        case hv: ( Cop.bool_val (Values.Vint (Int.repr 0)) (Ctypes.Tint sz s a) m)=> [ va | ] //=.
        move=> ht [] hv'; subst. rewrite /Cop.bool_val in hv. 
        case hv' : (Cop.classify_bool (Ctypes.Tint sz s a)) hv=> //=.
        move=> [] h; subst. rewrite /transC_val_bplvalue /= /Values.Val.of_bool /=.
        case hc: ((if ~~ ~~ Int.eq (Int.repr 0) Int.zero then Values.Vtrue else Values.Vfalse))=> //=.
        by eexists.*)
Admitted.

(* Complete Me : Medium *) (* Hint : Follow similar proof style like well_typed_uop *)
(* A well-typed bop always has a semantics that leads to a value. *)
Lemma well_typed_bop : forall Gamma Sigma bge vm bcmp v1 v2 ef t bop m ct g i,
type_expr Gamma Sigma (Prim (Bop bop) (Val v1 t:: Val v2 t :: nil) t) ef t ->
transBeePL_type t g = Res ct g i ->
interp_safe_conds (gen_safe_cond_expr (Prim (Bop bop) (Val v1 t:: Val v2 t :: nil) t)) Sigma bge vm m ->
exists v', Cop.sem_binary_operation bcmp bop (transBeePL_value_cvalue v1) ct 
                                             (transBeePL_value_cvalue v2) ct m = Some v'.
Proof.
Admitted.

(* Complete Me : Medium *)
Lemma trans_value_bop_success : forall Gamma Sigma bge bcmp vm bop v1 v2 ef t ct g i m v', 
type_expr Gamma Sigma (Prim (Bop bop) (Val v1 t:: Val v2 t :: nil) t) ef t ->
transBeePL_type t g = Res ct g i ->
interp_safe_conds (gen_safe_cond_expr (Prim (Bop bop) (Val v1 t:: Val v2 t :: nil) t)) Sigma bge vm m ->
Cop.sem_binary_operation bcmp bop (transBeePL_value_cvalue v1) ct 
                                  (transBeePL_value_cvalue v2) ct m = Some v' ->
exists v'', transC_val_bplvalue v' = OK v''.
Proof.
Admitted.

Lemma type_uop_inject : forall Gamma Sigma e t ef op,
is_reftype t = false ->
is_unittype t = false ->
type_expr Gamma Sigma e ef t ->
type_expr Gamma Sigma (Prim (Uop op) [::e] t) ef t. 
Proof.
move=> Gamma Sigma e t ef op hte. by apply ty_prim_uop.
Qed.

Lemma type_bop_inject : forall Gamma Sigma e1 e2 t ef op,
is_reftype t = false ->
is_unittype t = false ->
type_expr Gamma Sigma e1 ef t ->
type_expr Gamma Sigma e2 ef t ->
type_expr Gamma Sigma (Prim (Bop op) [::e1; e2] t) ef t. 
Proof.
move=> Gamma Sigma e1 e2 t ef op hte. by apply ty_prim_bop.
Qed.

(* Complete Me : Medium  *)
Lemma val_uop_type_preserve : forall Gamma Sigma ef t uop v ct g g' i m v' v'', 
type_expr Gamma Sigma (Val v t) ef t ->
transBeePL_type t g = Res ct g' i ->
Cop.sem_unary_operation uop (transBeePL_value_cvalue v) ct m = Some v' ->
transC_val_bplvalue v' = OK v'' ->
type_expr Gamma Sigma (Val v'' t) ef t.
Proof.
Admitted.

(* Complete Me : Medium *)
Lemma val_bop_type_preserve : forall Gamma Sigma bcmp bop v1 v2 ef t ct g g' i m v' v'', 
type_expr Gamma Sigma (Prim (Bop bop) (Val v1 t:: Val v2 t :: nil) t) ef t ->
transBeePL_type t g = Res ct g' i ->
Cop.sem_binary_operation bcmp bop (transBeePL_value_cvalue v1) ct 
                                  (transBeePL_value_cvalue v2) ct m = Some v' ->
transC_val_bplvalue v' = OK v'' ->
type_expr Gamma Sigma (Val v'' t) ef t .
Proof.
Admitted.

Lemma type_bool_val : forall Gamma Sigma v t ef ct m b,
type_expr Gamma Sigma (Val v t) ef t ->
type_bool t ->
Cop.bool_val (transBeePL_value_cvalue v) ct m = Some b.
Proof.
move=> Gamma Sigma v t ef ct m b hte.
Admitted.

(*** Proving theorems related to type system for small step semantics of BeePL ***)

(* Progress for small step semantics *)
(* A well typed expression is never stuck,
   it either evaluates to a value or can continue executing. *) 
Lemma progress_ssem_expr_exprs:
(forall Gamma Sigma es efs ts bge vm m, type_exprs Gamma Sigma es efs ts ->
                                        interp_safe_conds (flatten (map gen_safe_cond_expr es)) Sigma bge vm m ->
                                        is_values es \/ exists m' vm' es',
                                                        ssem_exprs bge vm m es m' vm' es') /\
(forall Gamma Sigma e ef t bge vm m , type_expr Gamma Sigma e ef t ->
                                     interp_safe_conds (gen_safe_cond_expr e) Sigma bge vm m ->
                                     is_value e \/ exists m' vm' e', 
                                                      ssem_expr bge vm m e m' vm' e').
Proof.
suff : (forall Gamma Sigma es efs ts, type_exprs Gamma Sigma es efs ts ->
                                      forall bge vm m, interp_safe_conds (flatten (map gen_safe_cond_expr es)) Sigma bge vm m ->
                                                       is_values es \/ exists m' vm' es',
                                                       ssem_exprs bge vm m es m' vm' es') /\
(forall Gamma Sigma e ef t, type_expr Gamma Sigma e ef t ->
                            forall bge vm m, interp_safe_conds (gen_safe_cond_expr e) Sigma bge vm m ->
                                             is_value e \/ exists m' vm' e', 
                                                           ssem_expr bge vm m e m' vm' e').
+ move=> [] hwt1 hwt2. split=> //=.
  + move=> Gamma Sigma es efs ts bge vm m htes hw.
    by move: (hwt1 Gamma Sigma es efs ts htes bge vm m hw).
  move=> Gamma Sigma e ef t bge vm m hte hw. 
  by move: (hwt2 Gamma Sigma e ef t hte bge vm m hw).
apply type_exprs_type_expr_ind_mut=> //=.
(* val unit *)
+ move=> Gamma Sigma ef bge vm m hw. by left.
(* val int *)
+ move=> Gamma Sigma ef i sz s a bge vm m hw. by left.
(* val long *)
+ move=> Gamma Sigma ef i s a bge vm m hw. by left.
(* val loc *)
+ move=> Gamma Sigma ef l ofs h t a bge vm m hw. by left.
(* var *)
+ move=> Gamma Sigma v t hteq bge vm m hw; subst. right.
  case: hw=> hw _. 
  (* lvar *)
  + rewrite /is_defined_var in hw. case hc: (vm ! v) hw=> [ [l t'] | ] //=.
    (* lvar *) 
    + move=> [] heq [] hs [] ofs [] v' [] hl hd; subst.
      exists m. exists vm. exists (Val v' t'). by apply ssem_lvar with l ofs. 
  (* gvar *)
  move=> [] hs [] l' [] ofs [] v' [] hg [] hl hd.
  exists m. exists vm. exists (Val v' t). by apply ssem_gbvar with l' ofs.
(* const int *)
+ move=> Gamma Sigma t sz s a i ht bge vm m hw. right.
  exists m. exists vm. exists (Val (Vint i) t). by apply ssem_consti.
(* const long *)
+ move=> Gamma Sigma t s a i ht bge vm m hw. right.
  exists m. exists vm. exists (Val (Vint64 i) t). by apply ssem_constl.
(* const uint *)
+ move=> Gamma Sigma t hteq bge vm m. right; subst.
  exists m. exists vm. exists (Val (Vunit) (Ptype Tunit)). by apply ssem_constu.
(* app *)
+ move=> Gamma Sigma e es rt efs ts ef efs' hte hin htes hin' bge vm m hw. right.
  have [hw1 hw2] := interp_safe_conds_concat (gen_safe_cond_expr e) 
                                   (flatten [seq gen_safe_cond_expr i | i <- es]) Sigma bge vm m hw.
  move: (hin bge vm m hw1)=> [] hv.
  (* value e *)
  + admit. (* tough *)
  (* e steps *)
  move: hv. move=> [] m' [] vm' [] e' he'.
  exists m'. exists vm'. exists (App e' es rt). by apply ssem_app1.
(* ref *) (* tough *)
+ (*move=> Gamma Sigma e ef h bt a hte hin bge vm m hw. 
  move: (hin bge vm m hw)=> [] he.
  (* is value *)
  + admit. (* need to evolve well formedness for store typing more *)
  (* step *)
  right. move: he. move=> [] m' [] vm' [] e' he. exists m'.
  exists vm'. exists (Prim Ref [:: e'] (Reftype h (Bprim bt) a)). by apply ssem_ref1.*)
  admit.
(* deref *)
+ move=> Gamma Sigma e ef h bt a hte hin bge vm m hw.
  have [hw1 /= [] hw2] := interp_safe_conds_concat (gen_safe_cond_expr e) 
                          [:: Valid_deref e] Sigma bge vm m hw.
  move: (hin bge vm m hw1)=> [] {hw}.
  (* is value *)
  + move=> hv. right. rewrite /is_value in hv. 
    case: e hv hte hin hw1 hw2=> v t //= _. case: v=> //=.
    move=> l ofs hte hin _ hw. rewrite /valid_deref in hw.
    move: hw. rewrite /is_pointer /=. move=> hw. 
    move: (hw l ofs bt h a)=> [] hs [] hvp [] v [] hl hd. exists m. exists vm.
    have /= hteq:= type_rel_typeof Gamma Sigma (Val (Vloc l ofs) t) ef 
                     (Reftype h (Bprim bt) a) hte; subst.
    exists (Val v (Ptype bt)). by apply ssem_deref2 with Full. 
  (* step *)
  + move: (hin bge vm m hw1)=> hin'. move=> [] m' [] vm' [] e' he. right.
    exists m'. exists vm'. exists (Prim Deref [:: e'] (Ptype bt)). apply ssem_deref1. 
    by apply he.
(* massgn *)
+ move=> Gamma Sigma e e' h bt ef a ef' hte hin hte' hin' bge vm m hw. right.
  rewrite catA in hw.
  have [hw1 hw2] := interp_safe_conds_concat ((gen_safe_cond_expr e) ++ (gen_safe_cond_expr e'))
          [:: Valid_assgn e e'] Sigma bge vm m hw.
  have [hw1' hw2'] := interp_safe_conds_concat (gen_safe_cond_expr e) 
                      (gen_safe_cond_expr e') Sigma bge vm m hw1.
  move: (hin bge vm m hw1')=> [] {hw} {hw1}.
  (* value e *)
  + move=> hv. case: e hte hin hv hw2 hw1'=> //= v t. case: v=> //=.
    (* unit *)
    + move=> hte. by inversion hte.
    (* int *)
    + move=> i hte. by inversion hte.
    (* long *)
    + move=> l hte. by inversion hte.
    (* loc *)
    move=> l ofs hte hin _. move: (hin' bge vm m hw2')=> [] hv'.
    (* value e' *)
    + case: e' hte' hin' hv' hw2'=> //= v' t' hte' hin' _ _ [] hw2' _ _. 
      rewrite /valid_assgn /= in hw2'.  
      move: (hw2' l ofs h bt a v')=> [] hs [] hp [] bf [] m' [] hl ha. 
      exists m'. exists vm. exists (Val Vunit (Ptype Tunit)). 
      have hteq := type_val_reflx Gamma Sigma v' t' ef' (Ptype bt) hte'; subst.
      have /= hteq:= type_rel_typeof Gamma Sigma (Val (Vloc l ofs) t) 
                       ef (Reftype h (Bprim bt) a) hte; subst.
      by apply ssem_massgn3 with bf. 
    (* e' steps *)
    move: hv'. move=> [] m' [] vm' [] e'' he''. exists m'. exists vm'.
    exists (Prim Massgn [:: Val (Vloc l ofs) t; e''] (Ptype Tunit)).
    have hteq := type_val_reflx Gamma Sigma (Vloc l ofs) t ef 
                 (Reftype h (Bprim bt) a) hte; subst. apply ssem_massgn2. by apply he''.
  (* e steps *)
  move=> [] m' [] vm' [] e'' he''. exists m'. exists vm'.
  exists (Prim Massgn [:: e''; e'] (Ptype Tunit)). apply ssem_massgn1. by apply he''.
(* uop *)
+ move=> Gamma Sigma op e ef t hf hf' hte hin bge vm m hw. right.
  move: (hin bge vm m hw)=> [] hv.
  (* value e *)
  + case: e hte hin hv hw=> //= v t' hte hin _ _. exists m. exists vm.
    have [hwts hwt] := well_typed_success. 
    have hteq := type_val_reflx Gamma Sigma v t' ef t hte; subst.
    have htuop := type_uop_inject Gamma Sigma (Val v t) t ef op hf hf' hte.
    move: (hwt Gamma Sigma (Val v t) ef t hte)=> [] ct [] g [] i hct.
    have hwv : interp_safe_conds (gen_safe_cond_expr (Val v t)) Sigma bge vm m. + by rewrite /=.
    have [v' hsop] := well_typed_uop Gamma Sigma bge vm v ef t op m ct g i htuop hct hwv.
    have [v'' hbv] := trans_value_uop_success Gamma Sigma ef t op v ct g g i m v' hte hct hsop. 
    exists (Val v'' t). apply ssem_uop2 with v' ct g g i. + by apply hct.
    + by apply hsop. by apply hbv.
  (* step *)
  move: hv. move=> [] m' [] vm' [] e' he'. exists m'. exists vm'.
  exists (Prim (Uop op) [:: e'] t). 
  have hteq := type_rel_typeof Gamma Sigma e ef t hte; subst. by apply ssem_uop1.
(* bop *)
+ move=> Gamma Sigma op e ef t e' hf hf' hte hin hte' hin' bge vm m hw. right.
  rewrite catA in hw.
  have [hw1 hw2] := interp_safe_conds_concat (gen_safe_cond_expr e ++ gen_safe_cond_expr e') 
                    (gen_safe_cond_bop op e e') Sigma bge vm m hw. 
  have [hw1' hw2'] := interp_safe_conds_concat (gen_safe_cond_expr e) 
                      (gen_safe_cond_expr e') Sigma bge vm m hw1.
  move: (hin bge vm m hw1')=> [] hv {hw} {hw1}.
  (* value e *)
  + case: e hte hin hv hw2 hw1'=> //= v t' hte hin _ hw1' _. 
    move:(hin' bge vm m hw2')=> [] hv'.
    (* value e' *)
    + case: e' hte' hin' hv' hw2' hw1'=> //= v' t'' hte' hin' _ _ hw1'.
      have hteq := type_val_reflx Gamma Sigma v t' ef t hte; subst.
      have hteq' := type_val_reflx Gamma Sigma v' t'' ef t hte'; subst.
      have [hwt1 hwt2] := well_typed_success. 
      move: (hwt2 Gamma Sigma (Val v t) ef t hte)=> [] ct1 [] g [] i hct1.
      move: (hwt2 Gamma Sigma (Val v' t) ef t hte')=> [] ct2 [] g' [] i' hct2.
      have htop := type_bop_inject Gamma Sigma (Val v t) (Val v' t) t ef op hf hf' hte hte'.
      have /= hwv: interp_safe_conds (gen_safe_cond_expr (Prim (Bop op) [:: Val v t; Val v' t] t)) 
                Sigma bge vm m. + rewrite /=. by apply hw1'.
      have [v'' hsop] := well_typed_bop Gamma Sigma bge vm (BeePL.genv_cenv bge) v v' ef t op 
                             m ct1 g i htop hct1 hwv.
      have [v''' htv] := trans_value_bop_success Gamma Sigma bge (BeePL.genv_cenv bge) vm op v v' ef t
                             ct1 g i m v'' htop hct1 hwv hsop. 
      exists m. exists vm. exists (Val v''' t). 
      apply ssem_bop3 with (BeePL.genv_cenv bge) v'' ct1 g g i. + by apply hct1.
      + by apply hsop. by apply htv.
    (* e' steps *)
    move: hv'. move=> [] m' [] vm' [] e'' he''. exists m'. exists vm'. 
    have hteq := type_val_reflx Gamma Sigma v t' ef t hte; subst.
    exists (Prim (Bop op) [:: Val v t; e''] t). apply ssem_bop2. by apply he''.
  (* e steps *)
  move: hv. move=> [] m' [] vm' [] e'' he''. exists m'. exists vm'. 
  have hteq := type_rel_typeof Gamma Sigma e ef t hte; subst.
  exists (Prim (Bop op) [:: e''; e'] (typeof_expr e)). apply ssem_bop1. by apply he''.
(* bind *)
+ move=> Gamma Sigma x t e e' t' ef ef' hte hin hte' hin' bge vm m hw. right.
  have [hw1 hw2]:= interp_safe_conds_concat (gen_safe_cond_expr e) (gen_safe_cond_expr e') Sigma bge vm m hw.
  move: (hin bge vm m hw1)=> [] hv {hw}.
  (* value e *)
  + case: e hte hin hv hw1=> //= v tv hte hin _. exists m. exists vm. exists (subst x (Val v tv) e').
    have hteq := type_rel_typeof (extend_context Gamma x t) Sigma e' ef' t' hte'; subst. 
    have hteq' := type_rel_typeof Gamma Sigma (Val v tv) ef t hte; subst.
    by apply ssem_bind2.
  (* e steps *)
  move: hv. move=> [] m' [] vm' [] e'' he''. exists m'. exists vm'. exists (Bind x t e'' e' t').
  have hteq := type_rel_typeof (extend_context Gamma x t) Sigma e' ef' t' hte'; subst. 
  by apply ssem_bind1.
(* cond *)
+ move=> Gamma Sigma e1 e2 e3 tb t ef1 ef2 ef3 ef1' ef2' ef3' hte1 hin hs1 htb
         hte2 hin'' hs2 hte3 hin2 hs3 bge vm m hw. 
  rewrite catA in hw.
  have [hw1 hw2]:= interp_safe_conds_concat (gen_safe_cond_expr e1 ++ gen_safe_cond_expr e2) (gen_safe_cond_expr e3)
          Sigma bge vm m hw.
  have [hw1' hw2'] := interp_safe_conds_concat (gen_safe_cond_expr e1) (gen_safe_cond_expr e2) Sigma bge vm m hw1.
  right. move: (hin bge vm m hw1')=> [] hv {hw} {hw1}.
  (* value e1 *)
  + case: e1 hte1 hin hv hw1'=> //= v t' hte1 hin _. exists m. exists vm. exists e2.
    have hteq := type_rel_typeof Gamma Sigma e2 ef2 t hte2; subst. 
    have [hwt1 hwt2] := well_typed_success. move: (hwt2 Gamma Sigma (Val v t') ef1 tb hte1).
    move=> [] ct [] g [] i hct.
    apply ssem_ctrue with g ct g i. 
    + by have hteq := type_val_reflx Gamma Sigma v t' ef1 tb hte1; subst.
    have hteq := type_val_reflx Gamma Sigma v t' ef1 tb hte1; subst.
    by have := type_bool_val Gamma Sigma v tb ef1 ct m true hte1 htb.
  (* e1 steps *) 
  move: hv. move=> [] m' [] vm' [] e1' he1'. exists m'. exists vm'.
  exists (Cond e1' e2 e3 t). have hteq := type_rel_typeof Gamma Sigma e2 ef2 t hte2; subst.
  by apply ssem_cond.
(* unit *)
+ move=> Gamma Sigma bge vm m hw. right. exists m. exists vm. exists (Val Vunit (Ptype Tunit)).
  by apply ssem_ut.
(* addr *)
+ move=> Gamma Sigma l ofs h t' a hs bge vm m hw. right.
  exists m. exists vm. exists (Val (Vloc l.(lname) ofs) (Reftype h t' a)). by apply ssem_adr.
(* ext *)
+ admit.
(* nil *)
+ move=> Gamma Sigma bge vm m hw. by left.
(* cons *)
move=> Gamma Sigma e es ef efs t ts hte hin htes hins bge vm m hw.
have [hw1 hw2] := interp_safe_conds_concat (gen_safe_cond_expr e) 
                    (flatten [seq gen_safe_cond_expr i | i <- es]) Sigma bge vm m hw.
move: (hin bge vm m hw1)=> [] hv {hw}.
(* value e *)
+ move: (hins bge vm m hw2)=> [] hvs.
  (* value es *)
  + left. by rewrite /andb hv. 
  (* es steps *)
  move: hvs. move=> [] m' [] vm' [] es' hes. right.
  case: e hte hin hv hw1=> //= v t' hte hin _. exists m'. exists vm'.
  exists (Val v t' :: es'). by apply ssem_cons2.
move: hv. move=> [] m' [] vm' [] e' he'. right.
exists m'. exists vm'. exists (e' :: es). by apply ssem_cons1.
Admitted.

(* Complete me *) (* Medium level *)
Lemma wderef_addr_val_ty : forall bge ty m l ofs bf v,
deref_addr bge ty m l ofs bf v ->
is_vloc v = false ->
wtypeof_value v (wtype_of_type ty).
Proof.
move=> bge ty m l ofs bf v hd hv. inversion hd; subst.
+ rewrite /Mem.loadv /= in H2.
  have hvt := Mem.load_type m (transl_bchunk_cchunk chunk) l 
              (Ptrofs.unsigned ofs) v0 H1.
  have hwt := wbty_chunk_rel ty chunk H.
  rewrite /wtypeof_value /= hwt /wtypeof_chunk /=. 
  by case: chunk H H1 hvt hwt=> //=; case: v hd H2 hv=> //=; case: v0=> //=.
+ admit. (* complete me for the case of volatile load *)
by case: ty hd H=> //= p. 
Admitted.

(* we need extra assertion that value cannot be a pointer because 
   in C, they allow it and we use deref_addr from CompCert *)
Lemma well_typed_val_expr : forall bge Gamma Sigma v t ef bf m l ofs,
deref_addr bge t m l ofs bf v ->
is_vloc v = false ->
type_expr Gamma Sigma (Val v t) ef t.
Proof.
move=> bge Gamma Sigma v t ef bf m l ofs hd hv. 
case hv: v hv=> [ | i | i64 | l' ofs'] //=; subst.
(* unit *)
+ move=> hf. case: t hd=> //=.
  + move=> p. case: p=> //=.
    + move=> hd. by apply ty_valu.
    + move=> sz s a hd. 
      have := wderef_addr_val_ty bge (Ptype (Tint sz s a)) m l ofs bf Vunit hd erefl.
      rewrite /wtype_of_type /=. admit. (* weird coq behavior *)
    move=> s a hd.
    have := wderef_addr_val_ty bge (Ptype (Tlong s a)) m l ofs bf Vunit hd erefl.
    admit. (* weird coq behavior *)
  move=> h b a hd.
  have /= := wderef_addr_val_ty bge (Reftype h b a) m l ofs bf Vunit hd erefl.
  admit. (* weird coq behavior *)
  move=> es e t hd.
  have /= := wderef_addr_val_ty bge (Ftype es e t) m l ofs bf Vunit hd erefl.
  admit. (* weird coq behavior *)
(* int *)
+ move=> _. inversion hd; subst. 
  (* not volatile *)
  + case: t hd H H0=> //=.
    + move=> p. case: p=> //=.
      (* Tint: good case *)
      + move=> sz s a hd hm hv. by apply ty_vali. 
      (* Tlong : bad case *)
      move=> s a hd [] hc hv. 
      by have /= := wderef_addr_val_ty bge (Ptype (Tlong s a)) m l ofs Full (Vint i) hd.
    (* Tref : not good case *)
    move=> h b a hd [] hc hv .
    by have /= := wderef_addr_val_ty bge (Reftype h b a) m l ofs Full (Vint i) hd erefl. 
  (* volatile *)
  case: t hd H H0=> //=.
  + move=> p. case: p=> //=.
    (* Tint: good case *)
    + move=> sz s a hd hm hv. by apply ty_vali. 
    (* Tlong : bad case *)
    move=> s a hd [] hc hv. 
    by have /= := wderef_addr_val_ty bge (Ptype (Tlong s a)) m l ofs Full (Vint i) hd.
  (* Tref : not good case *)
  move=> h b a hd [] hc hv.
  by have /= := wderef_addr_val_ty bge (Reftype h b a) m l ofs Full (Vint i) hd erefl. 
(* long *)
move=> hf. inversion hd; subst.
(* not volatile *)
+ case: t hd H H0=> //=.
  + move=> p. case: p=> //=.
    (* Tint: not good case *)
    + move=> sz s a hd hm hv. 
      by have /= := wderef_addr_val_ty bge (Ptype (Tint sz s a)) m l ofs Full (Vint64 i64) hd. 
    (* Tlong : good case *)
    move=> s a hd [] hc hv. by apply ty_vall. 
  (* Tref : not good case *)
  move=> h b a hd [] hc hv.
  by have /= := wderef_addr_val_ty bge (Reftype h b a) m l ofs Full (Vint64 i64) hd erefl.
(* volatile *)
case: t hd H H0=> //=.
+ move=> p. case: p=> //=.
  (* Tint: not good case *)
  + move=> sz s a hd hm hv. 
  by have /= := wderef_addr_val_ty bge (Ptype (Tint sz s a)) m l ofs Full (Vint64 i64) hd. 
  (* Tlong : good case *)
  move=> s a hd [] hc hv. by apply ty_vall. 
(* Tref : not good case *)
move=> h b a hd [] hc hv.
by have /= := wderef_addr_val_ty bge (Reftype h b a) m l ofs Full (Vint64 i64) hd erefl. 
Admitted.

(**** Substitution preserves typing ****)
Lemma subst_preservation : forall Gamma Sigma x t se e ef' ef t', 
type_expr (extend_context Gamma x t) Sigma e ef' t' ->
type_expr Gamma Sigma se ef t ->
type_expr Gamma Sigma (subst x se e) (ef ++ ef') t'.
Proof.
Admitted.

(* Generalize it to take into account all cases in one lemma *)
Lemma exf_ret_extract_int : forall g bt ct g' i,
bt <> Ptype Tunit ->
is_funtype bt = false -> 
transBeePL_type bt g = Res ct g' i ->
rettype_of_type ct = AST.Tint ->
exists sz s a, bt = Ptype (Tint sz s a).
Proof.
move=> sg bt ct g' i htu htf ht hp. case: bt htu htf ht=> //=.
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
Qed.

Lemma exf_ret_extract_long_ref : forall g bt ct g' i,
bt <> Ptype Tunit ->
is_funtype bt = false -> 
transBeePL_type bt g = Res ct g' i ->
rettype_of_type ct = AST.Tlong ->
if Ctypes.is_pointer ct
then (exists h t a, bt = Reftype h t a)
else (exists s a, bt = Ptype (Tlong s a)).
Proof.
move=> g bt ct g' i htu htf ht hp. case: bt htu htf ht=> //=.
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
Qed.

(**** External call result has the same type as present in the signature *)
Lemma well_typed_res_ext : forall Gamma Sigma bge exf g cef g' i' m m' vs vres bv ef t,
(get_rt_eapp exf) <> Ptype Tunit ->
is_funtype (get_rt_eapp exf) = false ->
befunction_to_cefunction exf g = Res cef g' i' ->
Events.external_call cef bge vs m t vres m' ->
transC_val_bplvalue vres = OK bv ->
type_expr Gamma Sigma (Val bv (get_rt_eapp exf)) (get_ef_eapp exf ++ ef) (get_rt_eapp exf).
Proof.
move=> Gamma Sigma bge exf g cef g' i' m m' vs vres bv ef t hut hft hcf hext hv.
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
      rewrite hbrt. by apply ty_vali.
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
move=> hext hm [] h1 h2; subst. apply ty_valloc.
Admitted.

(*** Preservation for small-step semantics ***)
(* If a program starts well-typed, it remains well-typed throughout execution,
   an evaluation does not produce type errors.*)
Lemma preservation_ssem_expr_exprs: 
(forall Gamma Sigma es efs ts bge vm m vm' m' es', 
    type_exprs Gamma Sigma es efs ts ->
    (*interp_safe_conds (flatten (map gen_safe_cond_expr es)) Sigma bge vm m ->*)
    ssem_exprs bge vm m es m' vm' es' ->
    type_exprs Gamma Sigma es' efs ts) /\
(forall Gamma Sigma e ef t bge vm m vm' m' e', 
    type_expr Gamma Sigma e ef t ->
    (*interp_safe_conds (gen_safe_cond_expr e) Sigma bge vm m ->*)
    ssem_expr bge vm m e m' vm' e' ->
    type_expr Gamma Sigma e' ef t).
Proof.
suff : (forall Gamma Sigma es efs ts, type_exprs Gamma Sigma es efs ts ->
                                      forall bge vm m vm' m' es', 
                                      (*interp_safe_conds (flatten (map gen_safe_cond_expr es)) Sigma bge vm m ->*)
                                      ssem_exprs bge vm m es m' vm' es' ->
                                      type_exprs Gamma Sigma es' efs ts) /\
       (forall Gamma Sigma e ef t, type_expr Gamma Sigma e ef t ->
                                   forall bge vm m vm' m' e', 
                                   (*interp_safe_conds (gen_safe_cond_expr e) Sigma bge vm m ->*)
                                   ssem_expr bge vm m e m' vm' e' ->
                                   type_expr Gamma Sigma e' ef t).
+ move=> [] ih ih'. split=> //=.
  + move=> Gamma Sigma es efs ts bge vm m vm' m' es' hts hes.
    by move: (ih Gamma Sigma es efs ts hts bge vm m vm' m' es' hes).
  move=> Gamma Sigma e ef t bge vm m vm' m' e' ht he.
  by move: (ih' Gamma Sigma e ef t ht bge vm m vm' m' e' he).
apply type_exprs_type_expr_ind_mut=> //=.
(* val unit *)
+ move=> Gamma Sigma ef t vm m vm' m' e' he. 
  inversion he; subst. by apply ty_valu.
(* val int *)
+ move=> Gamma Sigma ef i sz s a bge vm m vm' m' e' he.
  inversion he; subst. by apply ty_vali.
(* val long *)
+ move=> Gamma Sigma ef i s a bge vm m vm' m' e' he.
  inversion he; subst. by apply ty_vall.
(* val loc *)
+ move=> Gamma Sigma ef l ofs h t a bge vm m vm' m' e' he.
  inversion he; subst. by apply ty_valloc.
(* var *)
+ move=> Gamma Sigma x t ht bge vm m vm' m' e' he. 
  inversion he; subst.
  + by have := well_typed_val_expr bge Gamma Sigma v t empty_effect Full m' l ofs H4 H8.
  by have := well_typed_val_expr bge Gamma Sigma v t empty_effect Full m' l ofs H5 H9.
(* const int *)
+ move=> Gamma Sigma t sz s a i ht bge vm m vm' m' e' he; subst.
  inversion he; subst. by apply ty_vali.
(* const long *)
+ move=> Gamma Sigma t s a i ht bge vm m vm' m' e' he; subst.
  inversion he; subst. by apply ty_vall.
(* const unit *)
+ move=> Gamma Sigma t ht bge vm m vm' m' e' he; subst.
  inversion he; subst. by apply ty_valu.
(* app *)
+ move=> Gamma Sigma e es rt efs ts ef efs' hte hin htes hins bge vm m vm' m' e' he.
  inversion he; subst. apply ty_app with ts.
  + by move: (hin bge vm m vm' m' e'0 H7).
  + by apply htes.
  admit. (* hard case *)
(* ref *)
+ admit.
(* deref *)
+ move=> Gamma Sigma e ef h bt a hte hin bge vm m vm' m' e' he.
  inversion he; subst.
  (* step *)
  + apply ty_prim_deref with a. by move: (hin bge vm m vm' m' e'0 H6).  
  (* val *)
  by have := well_typed_val_expr bge Gamma Sigma v (Ptype bt) (ef ++ [:: Read h]) bf m' l ofs H3 H7.
(* massgn *)
+ move=> Gamma Sigma e e' h t ef a ef' hte hin hte' hin' bge vm m vm' m' e'' he.
  inversion he; subst.
  (* step *)
  + move: (hin bge vm m vm' m' e1' H6)=> hte1'.
    apply ty_prim_massgn with t a. + by apply hte1'. by apply hte'.
  (* value *)
  apply ty_prim_massgn with t a.
  + by apply hte.
  + by move: (hin' bge vm m vm' m' e2' H6).
  by apply ty_valu.
(* uop *)
+ move=> Gamma Sigma op e ef t hrt hut hte hin bge vm m vm' m' e' he.
  inversion he; subst.
  (* step *)
  + apply ty_prim_uop. + by apply hrt. + by apply hut.
    by move: (hin bge vm m vm' m' e'0 H7).
  (* value *)
  + by have := val_uop_type_preserve Gamma Sigma ef t op v ct g g' i m' 
            v' v'' hte H4 H8 H9.
(* bop *)
+ move=> Gamma Sigma op e ef t e' hrt hut hte hin hte' hin' bge vm m vm' m' e'' he.
  inversion he; subst.
  (* step *)       
  + move: (hin bge vm m vm' m' e1' H8)=> hte1'. by apply ty_prim_bop.
  (* value *)
  apply ty_prim_bop. + by apply hrt. + by apply hut. + by apply hte.
  + by move: (hin' bge vm m vm' m' e2' H8).
  have htop := type_bop_inject Gamma Sigma (Val v1 t) (Val v2 t) t ef op hrt hut hte hte'.
  by have := val_bop_type_preserve Gamma Sigma cenv op v1 v2 ef t ct g g' i m'
          v v' htop H8 H9 H10.
(* bind *)
+ move=> Gamma Sigma x t e e' t' ef ef' hte hin htx hin' bge vm m vm' m' e'' he''.
  inversion he''; subst.
  (* step *)
  + move: (hin bge vm m vm' m' e1' H9)=> hte1'. by apply ty_bind.
  (* value *)
  by have := subst_preservation Gamma Sigma x t (Val v1 t) e' ef' ef (typeof_expr e') htx hte.
(* cond *)
+ move=> Gamma Sigma e1 e2 e3 tb t ef1 ef2 ef3 ef1' ef2' ef3' hte1 hin1 hs1 htb
         hte2 hin2 hs2 hte3 hin3 hs3 bge vm m vm' m' e' he. 
 inversion he; subst.
  (* step e1 *)
  + move: (hin1 bge vm m vm' m' e1' H8)=> hin1'. 
    by apply ty_cond with tb ef1 ef2 ef3; auto.
  (* e1 is val *)
  admit. (* we would need something like principal typing *)
  admit. (* we would need something like principal typing *)
(* unit *)
+ move=> Gamma Sigma bge vm m vm' m' e' he. inversion he; subst.
  by apply ty_valu.
(* addr *)
+ move=> Gamma Sigma l ofs h t' a hs bge vm m vm' m' e' he. inversion he; subst.
  by apply ty_valloc.
(* ext *)
+ move=> Gamma Sigma exf ts es ef rt hrt [] hut hft hts htes hin bge vm m vm' m' e' he; subst.
  inversion he; subst. 
  by have := well_typed_res_ext Gamma Sigma bge exf g cef g' i' m'0 m'
          (transBeePL_values_cvalues (extract_values_exprs vs)) vres bv ef t hut hft H9 H10 H11.
(* nil *)
+ move=> Gamma Sigma bge vm m vm' m' es' hes. inversion hes; subst. by apply ty_nil.
(* cons *)
move=> Gamma Sigma e es ef efs t ts hte hin htes hins bge vm m vm' m' es' hes.
inversion hes; subst.
+ apply ty_cons. 
  + by move: (hin bge vm m vm' m' e' H6).
  by apply htes.
apply ty_cons.
+ by move: (hin bge vm m vm' m' (Val v t0)).
by move: (hins bge vm m vm' m' vs H6).
Admitted.

(* Stateful effects cannot be discarded :
   Expressions like ref, deref, massgn cannot discard the stateful effect even in the case 
   where it reduces to value *)
Lemma stateful_effects_preserved : 
(forall Gamma Sigma es efs ts bge vm m vm' m' es' efs' ts', 
        type_exprs Gamma Sigma es efs ts ->
        is_stateful_exprs es = true /\ is_stateful_effect efs = true ->
        ssem_exprs bge vm m es m' vm' es' ->
        type_exprs Gamma Sigma es' efs' ts' ->
        is_stateful_effect efs') /\
(forall Gamma Sigma e ef t bge vm m vm' m' e' ef' t', 
        type_expr Gamma Sigma e ef t ->
        is_stateful_expr e = true /\ is_stateful_effect ef = true ->
        ssem_expr bge vm m e m' vm' e' ->
        type_expr Gamma Sigma e' ef' t' ->
        is_stateful_effect ef').
Proof.
suff : (forall Gamma Sigma es efs ts, 
        type_exprs Gamma Sigma es efs ts ->
        forall bge vm m vm' m' es' efs' ts', 
        is_stateful_exprs es = true /\ is_stateful_effect efs = true ->
        ssem_exprs bge vm m es m' vm' es' ->
        type_exprs Gamma Sigma es' efs' ts' ->
        is_stateful_effect efs') /\
        (forall Gamma Sigma e ef t, 
        type_expr Gamma Sigma e ef t ->
        forall bge vm m vm' m' e' ef' t', 
        is_stateful_expr e = true /\ is_stateful_effect ef = true ->
        ssem_expr bge vm m e m' vm' e' ->
        type_expr Gamma Sigma e' ef' t' ->
        is_stateful_effect ef').
+ move=> [] ih ih'. admit.
apply type_expr_indP=> //=.
Admitted.


(***** Normalization ******)
(* A well typed program takes multistep to produce a value *)
Lemma normalization :
(forall Gamma Sigma es efs ts bge vm m n m' vm' es', 
 type_exprs Gamma Sigma es efs ts ->
 interp_safe_conds (flatten (map gen_safe_cond_expr es)) Sigma bge vm m ->
 ssem_closures bge vm m es n m' vm' es' /\ is_values es') /\
(forall Gamma Sigma e ef t bge vm m n m' vm' e', 
 type_expr Gamma Sigma e ef t ->
 interp_safe_conds (gen_safe_cond_expr e) Sigma bge vm m ->
 ssem_closure bge vm m e n m' vm' e' /\ is_value e).
Proof.
Admitted.

(***** With respect to big step semantics *****)

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
Qed.
  
(*** Proving theorems related to type system for big step semantics of BeePL *)
Lemma subject_reduction_bsem_expr_exprs: 
(forall Gamma Sigma es efs ts bge vm m vm' m' vs, type_exprs Gamma Sigma es efs ts ->
                                                  bsem_exprs bge vm m es m' vm' vs ->
                                                  wtypeof_values vs (wtypes_of_types ts)) /\
(forall Gamma Sigma e ef t bge vm m vm' m' v, type_expr Gamma Sigma e ef t ->
                                              bsem_expr bge vm m e m' vm' v ->
                                              wtypeof_value v (wtype_of_type t)).
Proof.
suff : (forall Gamma Sigma es efs ts, type_exprs Gamma Sigma es efs ts ->
                                      forall bge vm m vm' m' vs, bsem_exprs bge vm m es m' vm' vs ->
                                                                 wtypeof_values vs (wtypes_of_types ts)) /\
       (forall Gamma Sigma e ef t, type_expr Gamma Sigma e ef t ->
                                   forall bge vm m vm' m' v, bsem_expr bge vm m e m' vm' v ->
                                                             wtypeof_value v (wtype_of_type t)).
+ move=> [] ih ih'. split=> //=.
  + move=> Gamma Sigma es efs ts bge vm m m' vm' vs hts hes. 
    by move: (ih Gamma Sigma es efs ts hts bge vm m m' vm' vs hes).
  move=> Gamma Sigma e ef t bge vm m m' vm' v ht he.
  by move: (ih' Gamma Sigma e ef t ht bge vm m m' vm' v he).
apply type_expr_indP => //=.
(* val unit *)
+ move=> Gamma Sigma ef bge vm m vm' m' v he. by inversion he; subst.
(* 
(* val *)
+ move=> Gamma Sigma v ef t bge vm m vm' m' v' he. inversion he; subst.
  case: t he H6=> //=.
  + move=> p. case: p=> //=.
    + move=> he hw. case: v' he hw=> //=.
      + move=> i he hw. by inversion hw.
      + move=> i he hw. by inversion hw.
      move=> l ofs he hw. by inversion hw.
    + move=> i s a he hw. case: v' he hw=> //=.
      + move=> i' he hw. by inversion hw.
      move=> l ofs he hw. by inversion hw.
    + move=> s a he hw. case: v' he hw=> //=.
      move=> i he hw. by inversion hw.
    move=> i h a he hw. case: v' he hw=> //= i' he hw. by inversion hw.
  move=> es e t he hw. case: v' he hw=> //= i he hw. by inversion hw.
(* var *)
+ move=> Gamma Sigma x t ht bge vm m vm' m' v hv. inversion hv; subst.
  (* local *)
  + have := wderef_addr_val_ty bge (Ptype t) m' l ofs Full v H7.
    by case: t ht hv H3 H7=> //=.
  (* global *)
  + have := wderef_addr_val_ty bge (Ptype t) m' l ofs Full v H8.
    by case: t ht hv H8=> //=.
(* const int *)
+ move=> Gamma Sigma t sz s i a hteq bge vm m vm' m' v hv. by inversion hv; subst.
(* const long *)
+ move=> Gamma Sigma t s i a hteq bge vm m vm' m' v hv. by inversion hv; subst.
(* const unit *)
+ move=> Gamma Sigma t hteq bge vm m vm' m' v hv. by inversion hv; subst.
(* app *)
+ move=> Gamma Sigma e es rt ef ef' ts ef'' hie hies bge vm m vm' m' v hv.
  inversion hv; subst. move: (hie bge vm m vm2 m2 (Vloc l Ptrofs.zero) H2)=> het.
  move: (hies bge vm3 m3 vm4 m4 vs H7)=> hest. inversion H4; subst.
  by have := type_to_wtype v (get_rt_fundef (Internal fd)) H16.
(* ref *)
+ move=> Gamma Sigma e ef h bt a hi bge vm m vm' m' v hv. by inversion hv; subst.
(* deref *)
+ move=> Gamma Sigma e ef h bt a hi bge vm m vm' m' v hv. inversion hv; subst.
  move: (hi bge vm m vm' m' (Vloc l ofs) H3)=> hlt. 
  have hvt := wderef_addr_val_ty bge (typeof_expr e) m l ofs bf v H7.
  by rewrite H0 /= in hvt.
(* massgn *)
+ move=> Gamma Sigma e1 e2 ef1 ef2 h bt a hi1 hi2 bge vm m vm' m' v hv.
  by inversion hv; subst. 
(* uop *)
+ move=> Gamma Sigma op e ef t he bge vm m vm' m' v hv. inversion hv; subst.
  have hvt' := uop_type_preserve op (transBeePL_value_cvalue v0) ct m' v' H9.
  by have := eq_uop_types op (typeof_expr e) g g' i (transBeePL_value_cvalue v0) ct m' v' v
             H5 H9 hvt' H10.
(* bop *)
+ move=> Gamma Sigma op e1 e2 ef t he1 he2 bge vm m vm' m' v hv. inversion hv; subst.
  have [hvt0 hvt0'] := bop_type_preserve cenv op (transBeePL_value_cvalue v1) ct1 
                       (transBeePL_value_cvalue v2) ct2 m' v0 H12.
  by have [hvt hvt'] := eq_bop_types cenv (transBeePL_value_cvalue v1) (typeof_expr e1) g g' i
          (transBeePL_value_cvalue v2) (typeof_expr e2) g'' i' ct1 ct2 op m' v0 v H7 H11 H12 H13 hvt0 hvt0'.
(* bind *)
+ move=> Gamma Sigma x t e e' t' ef ef' hie hie' bge vm m vm' m' v hv. inversion hv; subst.
  move: (hie bge vm m vm'0 m'0 v0 H9)=> hvt0. admit.
(* cond *)
+ move=> Gamma Sigma e1 e2 e3 ef1 ef2 ef3 tb t het1 hb het2 het3 bge vm m vm' m' v hv.
  inversion hv; subst.
  (* true *)
  + by move: (het2 bge vm'0 m'0 vm' m' v H11).
  (* false *)
  by move: (het3 bge vm'0 m'0 vm' m' v H11).
(* unit *)
+ move=> Gamma Sigma bge vm m vm' m' v he. by inversion he; subst.
(* addr *)
+ move=> Gamma Sigma l h t a ofs t' ht hteq bge vm m vm' m' v he.
  rewrite hteq /=. by inversion he; subst.
(* nil *)
+ move=> Gamma Sigma bge vm m vm' m' vs hv. by inversion hv; subst.
(* cons *)
move=> Gamma Sigma e es t ef ts efs hi his bge vm m vm' m' vs hv.
inversion hv; subst. move: (hi bge vm m vm'0 m'0 v H3) => hvt.
move: (his bge vm'0 m'0 vm' m' vs0 H7)=> hvts. by rewrite /typeof_values.*)
Admitted.  


(*Section Subject_Reduction.

Variable (bge : genv).
Variable (benv : vmap).

(* Subject reduction : Big step semantics *) 
Lemma subject_lredcution : forall m e l ofs Gamma Sigma ef t h a,
bsem_expr_slv bge benv m e l ofs ->
type_expr Gamma Sigma e ef (Reftype h t a) ->
PTree.get l.(lname) Sigma = Some (Reftype h t a).
Proof.
move=> m e l ofs Gamma Sigma ef t h a hl.
induction hl=> //= ht; subst; inversion ht; subst; symmetry.
by case: H7=> h1 h2 h3; subst.
Qed.

Lemma subject_rreduction : forall m e v Gamma Sigma ef t, 
bsem_expr_srv bge benv m e v ->
type_expr Gamma Sigma e ef t ->
wtypeof_value v (wtype_of_type t).
Proof.
move=> m e v Gamma Sigma ef t hr ht. move: Gamma Sigma ef t ht.
induction hr=> //=. 
(* Val *)
+ move=> Gamma Sigma ef t' ht. 
  inversion ht; subst; rewrite /wtypeof_value /= /wtype_of_type.
  case: t' ht H=> //=.  
  + move=> p. case: p=> //=.
    + case: v=> //=.
      + move=> i ht hw. by inversion hw.
      + move=> i ht hw. by inversion hw.
      move=> l ofs ht hw. by inversion hw.
    + move=> i s a ht hw. case: v ht hw=> //=.
      + move=> l ht hw. by inversion hw.
      move=> l ofs ht hw. by inversion hw. 
    + move=> s a ht hw. case: v ht hw=> //=.
      move=> l ht hw. by inversion hw.
    move=> h b a. case: v=> //= i ht hw. by inversion hw. 
  move=> h b a ht hw. case: v ht hw=> //= i ht hw. by inversion hw. 
(* Deref *)
+ move=> Gamma Sigma ef t' ht.
  inversion ht; subst. rewrite H7.
  have := subject_lredcution hm e l ofs Gamma Sigma ef0 (Bprim bt) h a H H9=> hlt. 
  by have := wderef_addr_val_ty bge (typeof_expr e) hm l.(lname) ofs l.(lbitfield) v H0.
(* Uop *)
+ move=> Gamma Sigma ef t' ht. inversion ht; subst.
  move: (IHhr Gamma Sigma ef (typeof_expr e) H10)=> hvt.
  have hvt' := uop_type_preserve uop (transBeePL_value_cvalue v) ct hm v' H1.
  by have := eq_uop_types uop (typeof_expr e) g g' i (transBeePL_value_cvalue v) ct hm v'
          v'' H H1 hvt' H2.
(* Bop *)
+ move=> Gamma Sigma ef t' ht; subst. inversion ht; subst.
  move: (IHhr1 Gamma Sigma ef t' H12)=> hvt1. move: (IHhr2 Gamma Sigma ef t' H13)=> hvt2.
  have [hvt hvt'] := bop_type_preserve bge bop (transBeePL_value_cvalue v1) ct1 
     (transBeePL_value_cvalue v2) ct2 hm v H2.
  by have := cval_bval_type_eq v ct1 v' (typeof_expr e1) g g' i hvt H3 H; case: H1=> [] h1 h2; subst.
Qed.

End Subject_Reduction.

(* Subject reduction : Small step semantics *)
(* A well-typed expression remains well-typed under top-level lreduction *)
(* Add invariant for well formedness for the store *)
Lemma slreduction : forall Gamma Sigma genv ef t vm e m e' m', 
type_expr Gamma Sigma e ef t ->
lreduction genv vm e m e' m' ->
type_expr Gamma Sigma e' ef t.
Proof.
(*move=> Gamma Sigma genv ef t vm e m e' m' ht he.
induction he=> //=.
+ inversion ht; subst. rewrite H0. apply ty_addr with h t0 a.
  rewrite /=. Print lreduction.
+ inversion ht; subst. rewrite H0. by apply ty_addr with h t0 a.
Qed.*) Admitted.
*)

    
    

 

