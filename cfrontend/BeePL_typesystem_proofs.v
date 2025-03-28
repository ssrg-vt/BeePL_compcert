Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import compcert.common.Errors Initializersproof Cstrategy BeePL_auxlemmas Coqlib Errors Memory.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import BeePL_sem BeePL_typesystem BeePL_compiler_proofs BeePL_values.

From mathcomp Require Import all_ssreflect.


(**** Well formedness ****)
(** Well-Typed Store **)
(* A store st is well-typed with respect to a store typing context Sigma if the
   term at each location l in vm has the type at location l in store typing context
   and there exists a value in the memory at that location. *)
(* It is more evolved due to two maps used in CompCert for retrieving data from the memory *)
(* Since we only allow pointers through references, it is safe to say that if there exists a 
   location in memory then it is also safe to deref that location *)
(* Mem.valid_pointer ensures that the location l with ofset ofs is nonempty in memory m *)
Definition store_well_typed (Sigma : store_context) 
                            (bge : BeePL.genv) (vm : vmap) (m : Memory.mem) :=
(forall Gamma l, match Gamma! l with 
                 |  Some t =>  match vm! l with 
                               | Some (l', t') => t = t' /\
                                                  PTree.get l Sigma = Some t /\ 
                                                  (exists v ofs, deref_addr bge t m l' ofs Full v /\ 
                                                                 is_vloc v = false /\
                                                                 is_reftype t = false)
                               | None => (exists l' ofs v, PTree.get l Sigma = Some t /\ 
                                                           Genv.find_symbol bge l = Some l' /\ 
                                                           deref_addr bge t m l' ofs Full v /\ 
                                                           is_vloc v = false /\
                                                           is_reftype t = false)
                               end
                 | None => (forall ofs h t a, PTree.get l Sigma = Some (Reftype h (Bprim t) a) ->
                                              Mem.valid_pointer m l (Ptrofs.unsigned ofs) /\
                                              ((exists v, deref_addr bge (Ptype t) m l ofs Full v /\ 
                                                          is_vloc v = false) /\
                                               (forall v, (exists bf m', assign_addr bge (Ptype t) m l ofs bf v m' v /\
                                                                         is_vloc v = false))))
                 end).

(*** Definition memory_well_formedness : forall Sigma l, m, 
     Sigma ! l = Reftype h bt a -> 
     deref m bt l = v ->
     v != loc. ***)

(* A well-typed uop always has a semantics that leads to a value. *)
Lemma well_formed_uop : forall Gamma Sigma bge vm v ef t uop m ct g i,
type_expr Gamma Sigma (Prim (Uop uop) ((Val v t) :: nil) t) ef t ->
transBeePL_type t g = Res ct g i ->
store_well_typed Sigma bge vm m ->
exists v', Cop.sem_unary_operation uop (transBeePL_value_cvalue v) ct m = Some v'.
Proof.
move=> Gamma Sigma bge vm v ef t uop m ct g i htv. 
elim: v htv=> //=. 
(* unit *)
+ move=> htv. have [h1 [h2 [h3 [ef' h4]]]] := type_infer_uop Gamma Sigma (Val Vunit t) uop t ef t htv.
  have [h11 h12] := type_infer_vunit Gamma Sigma ef' t t h4; subst.
  rewrite /transBeePL_type /=. move=> [] hct hw; subst. by case: uop htv=> //=.
(* int *)
+ move=> i' hvt. have [h1 [h2 [h3 [ef' h4]]]] := type_infer_uop Gamma Sigma (Val (Vint i') t) uop t ef t hvt. 
  have [sz [] s [] a [] h11 h12]:= type_infer_int Gamma Sigma i' ef' t t h4; subst.
  rewrite /transBeePL_type. move=> [] hct; subst.
  case: uop hvt=> //=.
  (* sem_notbool *)
  + rewrite /Cop.sem_notbool /option_map /=. 
    case hop: (Cop.bool_val (Values.Vint i') (Ctypes.Tint sz s a) m)=> [ vo | ] //=.
    by exists (Values.Val.of_bool (~~ vo)).
  move: hop. rewrite /Cop.bool_val /=. case hc: (Cop.classify_bool (Ctypes.Tint sz s a))=> //=.
  + rewrite /Cop.classify_bool /= in hc. move: hc. by case: sz h3 h2 h1 h4 h12=> //=.
  + rewrite /Cop.classify_bool /= in hc. move: hc. by case: sz h3 h2 h1 h4 h12=> //=.
  + rewrite /Cop.classify_bool /= in hc. move: hc. by case: sz h3 h2 h1 h4 h12=> //=.
  rewrite /Cop.classify_bool /= in hc. move: hc. by case: sz h3 h2 h1 h4 h12=> //=.
  (* sem_notint *)
  + rewrite /Cop.sem_notint /Cop.classify_notint. case: sz h3 h2 h1 h4 h12=> //=.
    + move=> hvt. by exists (Values.Vint (Int.not i')).
    + move=> hvt. by exists  (Values.Vint (Int.not i')).
    + case: s=> //=.
      + by exists (Values.Vint (Int.not i')).
      by exists (Values.Vint (Int.not i')).
    by exists (Values.Vint (Int.not i')).
  (* sem_neg *)
  + rewrite /Cop.sem_neg /Cop.classify_neg. case: sz h3 h2 h1 h4 h12=> //=.
    + by exists (Values.Vint (Int.neg i')).
    + by exists (Values.Vint (Int.neg i')).
    + case: s=> //=. + by exists (Values.Vint (Int.neg i')).
      by exists (Values.Vint (Int.neg i')).
    by exists (Values.Vint (Int.neg i')).
  (* sem_absfloat *)
  + rewrite /Cop.sem_absfloat /Cop.classify_neg /=. case: sz h3 h2 h1 h4 h12=> //=.
    + by exists (Values.Vfloat (Floats.Float.abs (Floats.Float.of_int i'))).
    + by exists (Values.Vfloat (Floats.Float.abs (Floats.Float.of_int i'))).
    + case: s=> //=. + by exists (Values.Vfloat (Floats.Float.abs (Floats.Float.of_int i'))).
      by exists (Values.Vfloat (Floats.Float.abs (Floats.Float.of_intu i'))).
    by exists (Values.Vfloat (Floats.Float.abs (Floats.Float.of_int i'))).
(* long *)
+ move=> i' hvt. have [h1 [h2 [h3 [ef' h4]]]] := type_infer_uop Gamma Sigma (Val (Vint64 i') t) uop t ef t hvt. 
  have [s [] a [] h11 h12]:= type_infer_long Gamma Sigma i' ef' t t h4; subst.
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
move=> p ofs hvt. have [h1 [h2 [h3 [ef' h4]]]] := type_infer_uop Gamma Sigma (Val (Vloc p ofs) t) uop t ef t hvt. 
by have [h [] bt [] a [] h11 [] h12 hs]:= type_infer_loc Gamma Sigma p ofs ef' t t h4; subst.
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
(* ADD safety requirement in the semantics of div/mod/shift so that it never reaches overflow or division by zero *)
Lemma well_formed_bop : forall Gamma Sigma bge vm bcmp v1 v2 ef t bop m ct g i,
type_expr Gamma Sigma (Prim (Bop bop) ((Val v1 t) :: (Val v2 t) :: nil) t) ef t ->
transBeePL_type t g = Res ct g i ->
store_well_typed Sigma bge vm m ->
exists v', Cop.sem_binary_operation bcmp bop (transBeePL_value_cvalue v1) ct 
                                             (transBeePL_value_cvalue v2) ct m = Some v'.
Proof.
Admitted.

(* Complete Me : Medium *)
Lemma trans_value_bop_success : forall Gamma Sigma bge bcmp vm bop v1 v2 ef t ct g i m v', 
type_expr Gamma Sigma (Prim (Bop bop) (Val v1 t:: Val v2 t :: nil) t) ef t ->
transBeePL_type t g = Res ct g i ->
store_well_typed Sigma bge vm m ->
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
(*move=> Gamma Sigma e t ef op ef' hrt hut hte hs. apply ty_prim_uop. with ef.
Qed.*) Admitted.

Lemma type_bop_inject : forall Gamma Sigma e1 e2 t ef op,
is_reftype t = false ->
is_unittype t = false ->
type_expr Gamma Sigma e1 ef t ->
type_expr Gamma Sigma e2 ef t ->
type_expr Gamma Sigma (Prim (Bop op) [::e1; e2] t) ef t. 
Proof.
(*move=> Gamma Sigma e1 e2 t ef op ef' hrt hut ht1 ht2 hs. by apply ty_bop with ef.
Qed.*) Admitted.

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

Lemma assign_preserves_store_well_typed : forall Sigma bge vm m bt l ofs bf v m',
store_well_typed Sigma bge vm m ->
assign_addr bge (Ptype bt) m l ofs bf v m' v ->
is_vloc v = false ->
store_well_typed Sigma bge vm m'.
Proof.
Admitted.

(*** Proving theorems related to type system for small step semantics of BeePL ***)

(* Progress for small step semantics *)
(* A well typed expression is never stuck,
   it either evaluates to a value or can continue executing. *) 
(* Progress for small step semantics *)
(* A well typed expression is never stuck,
   it either evaluates to a value or can continue executing. *)
Lemma progress_ssem_expr_exprs:
(forall Gamma Sigma es efs ts bge vm m, type_exprs Gamma Sigma es efs ts ->
                                        store_well_typed Sigma bge vm m ->
                                        is_values es \/ exists m' vm' es',
                                                        ssem_exprs bge vm m es m' vm' es' /\
                                                        store_well_typed Sigma bge vm' m') /\
(forall Gamma Sigma e ef t bge vm m, type_expr Gamma Sigma e ef t ->
                                     store_well_typed Sigma bge vm m ->
                                     is_value e \/ exists m' vm' e', 
                                                   ssem_expr bge vm m e m' vm' e' /\
                                                   store_well_typed Sigma bge vm' m').
Proof.
suff : (forall Gamma Sigma es efs ts, type_exprs Gamma Sigma es efs ts ->
                                      forall bge vm m, store_well_typed Sigma bge vm m ->
                                                       is_values es \/ (exists m' vm' es',
                                                       ssem_exprs bge vm m es m' vm' es' /\
                                                       store_well_typed Sigma bge vm' m')) /\
(forall Gamma Sigma e ef t, type_expr Gamma Sigma e ef t ->
                            forall bge vm m, store_well_typed Sigma bge vm m ->
                                             is_value e \/ (exists m' vm' e', 
                                                           ssem_expr bge vm m e m' vm' e' /\
                                                           store_well_typed Sigma bge vm' m')).
+ move=> [] hwt1 hwt2. split=> //=.
  + move=> Gamma Sigma es efs ts bge vm m htes hw.
    by move: (hwt1 Gamma Sigma es efs ts htes bge vm m hw).
  move=> Gamma Sigma e ef t bge vm m hte hw. 
  by move: (hwt2 Gamma Sigma e ef t hte bge vm m hw).
apply type_exprs_type_expr_ind_mut=> //=.
(* val unit *)
+ move=> Gamma Sigma bge vm m hw. by left.
(* val int *)
+ move=> Gamma Sigma i sz s a bge vm m hw. by left.
(* val long *)
+ move=> Gamma Sigma i s a bge vm m hw. by left.
(* val loc *)
+ move=> Gamma Sigma l ofs h t a bge vm m hw. by left.
(* var *)
+ move=> Gamma Sigma v t hteq bge vm m hw; subst. right.
  rewrite /store_well_typed in hw. move: (hw (extend_context Gamma v t) v).
  rewrite hteq /=. case hvm: vm ! v=> [[l t'] | ] //=.
  (* lvar *)
  + move=> [] ht [] hs [] v' [] ofs [] hd hv; subst.
    exists m. exists vm. exists (Val v' t'). split=> //=. 
    eapply ssem_lvar. + by apply hvm. + by apply hd. by apply hv.
  (* gvar *)
  move=> [] l' [] ofs [] v' [] hs [] hg [] hd hv. 
  exists m. exists vm. exists (Val v' t). split=> //=. 
  apply ssem_gbvar with l' ofs. + by apply hvm. + by apply hg.
  + by apply hd. by apply hv.
(* const int *)
+ move=> Gamma Sigma t sz a i bge vm m hw. right.
  exists m. exists vm. exists (Val (Vint i) (Ptype (Tint t sz a))). 
  split=> //=. by apply ssem_consti.
(* const long *)
+ move=> Gamma Sigma t s i bge vm m hw. right.
  exists m. exists vm. exists (Val (Vint64 i) (Ptype (Tlong t s))). 
  split=> //=. by apply ssem_constl.
(* const uint *)
+ move=> Gamma Sigma bge vm m. right; subst.
  exists m. exists vm. exists (Val (Vunit) (Ptype Tunit)). split=> //=. by apply ssem_constu.
(* app *)
+ admit.
(* ref *)
+ move=> Gamma Sigma e ef h bt a hte hin bge vm m hw. 
  move: (hin bge vm m hw)=> [] he.
  (* is value *)
  + admit. (* need to evolve well formedness for store typing more *)
  (* step *)
  right. move: he. move=> [] m' [] vm' [] e' [] he hv. exists m'.
  exists vm'. exists (Prim Ref [:: e'] (Reftype h (Bprim bt) a)). 
  split=> //=. by apply ssem_ref1.
(* deref *)
+ move=> Gamma Sigma e ef h bt a hte hin bge vm m hw.
  move: (hin bge vm m hw)=> [].
  (* is value *)
  + move=> hv. right. rewrite /is_value in hv. case: e hv hte hin=> v t //= _. case: v=> //=.
    (* unit *)
    + move=> hte hin. 
      by have [h1 h2] := type_infer_vunit Gamma Sigma ef t (Reftype h (Bprim bt) a) hte; subst.
    (* int *)
    + move=> i hte hin. 
      by have [h1 [sz] [s] [] h2 h3] := type_infer_int Gamma Sigma i ef t (Reftype h (Bprim bt) a) hte; subst.
    (* long *)
    + move=> l hte hin. 
      by have [s [] a' [] h1 h2] := type_infer_long Gamma Sigma l ef t (Reftype h (Bprim bt) a) hte.
    (* loc *)
    move=> l ofs hte hin. rewrite /store_well_typed in hw. 
    have [h' [] bt' [] a' [] h1 [] [] h11 h12 h13 hs] := type_infer_loc Gamma Sigma l ofs 
                                                ef t (Reftype h (Bprim bt) a) hte; subst.
    move: (hw Gamma l). case hg: Gamma ! l=> [ t'| ] //=.
    + case hvm : vm ! l => [[ l1 t1] | ] //=.
      + move=> [] h1 [] h2 [] v [] ofs' [] hd [] hv hp; subst.
        rewrite h2 in hs. case: hs=> hs; subst.
        by inversion hp.
      move=> [] l' [] ofs' [] v [] hg' [] hs' [] hd [] hv hp. 
      rewrite hg' in hs. case: hs=> hs; subst.
      by inversion hp.
   move=> hwd. move: (hwd ofs h' bt a' hs)=> [] hvp [].
   move=> [] v [] hd hv ha. exists m. exists vm. exists (Val v (Ptype bt)). split=> //=.
   by apply ssem_deref2 with Full. 
  (* step *)
  move: (hin bge vm m hw)=> hin'. move=> [] m' [] vm' [] e' [] he hs. right.
  exists m'. exists vm'. exists (Prim Deref [:: e'] (Ptype bt)). split=> //=. 
  apply ssem_deref1. by apply he.
(* massgn *)
+ move=> Gamma Sigma e e' h bt ef a ef' hte hin hte' hin' bge vm m hw. 
  right. move: (hin bge vm m hw)=> [].
  (* value e *)
  + move=> hv. case: e hte hin hv=> //= v t. case: v=> //=.
    (* unit *)
    + move=> hte.  
      by have [h1 h2] := type_infer_vunit Gamma Sigma ef t (Reftype h (Bprim bt) a) hte; subst.
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
    exists m'. exists vm. exists (Val Vunit (Ptype Tunit)). 
    have hteq := type_val_reflx Gamma Sigma v' t' ef' (Ptype bt) hte'; subst. split=> //=.
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
exists m'. exists vm'. exists (e' :: es). split=> //=. by apply ssem_cons1.
Admitted.

Lemma not_ptr_cval : forall cv bv, 
transC_val_bplvalue cv = OK bv ->
is_vloc bv = false -> 
Values.is_vptr cv = false.
Proof.
move=> cv bv. rewrite /transC_val_bplvalue /=.
case: cv=> //=.
by move=> b p [] h; subst.
Qed.

Lemma wderef_addr_val_ty : forall bge ty m l ofs bf v,
deref_addr bge ty m l ofs bf v ->
is_vloc v = false ->
is_reftype ty = false ->
wtypeof_value v (wtype_of_type ty).
Proof.
move=> bge ty m l ofs bf v hd hv. inversion hd; subst.
+ rewrite /Mem.loadv /= in H2.
  have hvt := Mem.load_type m (transl_bchunk_cchunk chunk) l 
              (Ptrofs.unsigned ofs) v0 H1.
  have hct := not_ptr_cval v0 v H2 hv.
  case: v0 H1 H2 hvt hct=> //=.
  (* int *)
  + move=> i hl [] hveq /=. 
    case: chunk H hl=> //=; subst; case: ty hd H0=> //= p; by case: p=> //=.
  (* long *)
  + move=> i hl [] hveq /=.
    case: chunk H hl=> //=; subst; case: ty hd H0=> //= p. 
    by case: p=> //= sz s a; case: sz=> //=; case: s=> //=.
+ admit. (* complete me for the case of volatile load *)
by case: ty hd H=> //= p. 
Admitted.


(* we need extra assertion that value cannot be a pointer because 
   in C, they allow it and we use deref_addr from CompCert *)
Lemma well_typed_val_expr : forall bge Gamma Sigma v t ef bf m l ofs,
deref_addr bge t m l ofs bf v ->
is_vloc v = false ->
is_reftype t = false ->
type_expr Gamma Sigma (Val v t) ef t.
Proof.
move=> bge Gamma Sigma v t ef bf m l ofs hd hw hw'. 
case hv: v hd=> [ | i | i64 | l' ofs'] //=; subst.
(* unit *)
+ move=> hd. case: t hd hw'=> //=.
  + move=> p. case: p=> //=.
    + move=> hd. have hn : type_expr Gamma Sigma (Val Vunit (Ptype Tunit)) [::] (Ptype Tunit).
      + by apply ty_valu.
      have hs := sub_effect_nil ef. 
      by have := ty_sub Gamma Sigma (Val Vunit (Ptype Tunit)) nil (Ptype Tunit) ef hn hs.
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
by have /= := wderef_addr_val_ty bge t m l ofs bf (Vloc l' ofs') hd.
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
Lemma well_typed_res_ext : forall Gamma Sigma bge bge' exf g cef g' i' vm m m' vs vres bv ef t,
(get_rt_eapp exf) <> Ptype Tunit ->
is_funtype (get_rt_eapp exf) = false ->
befunction_to_cefunction exf g = Res cef g' i' ->
Events.external_call cef bge vs m t vres m' ->
transC_val_bplvalue vres = OK bv ->
type_expr Gamma Sigma (Val bv (get_rt_eapp exf)) (get_ef_eapp exf ++ ef) (get_rt_eapp exf) /\
store_well_typed Sigma bge' vm m'.
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


(*** Preservation for small-step semantics ***)
(* If a program starts well-typed, it remains well-typed throughout execution,
   an evaluation does not produce type errors.*)
Lemma preservation_ssem_expr_exprs: 
(forall Gamma Sigma es efs ts bge vm m vm' m' es', 
    type_exprs Gamma Sigma es efs ts ->
    store_well_typed Sigma bge vm m ->
    ssem_exprs bge vm m es m' vm' es' ->
    type_exprs Gamma Sigma es' efs ts /\
    store_well_typed Sigma bge vm' m') /\
(forall Gamma Sigma e ef t bge vm m vm' m' e', 
    type_expr Gamma Sigma e ef t ->
    store_well_typed Sigma bge vm m ->
    ssem_expr bge vm m e m' vm' e' ->
    type_expr Gamma Sigma e' ef t /\
    store_well_typed Sigma bge vm' m').
Proof.
suff : (forall Gamma Sigma es efs ts, type_exprs Gamma Sigma es efs ts ->
                                      forall bge vm m vm' m' es', 
                                      store_well_typed Sigma bge vm m ->
                                      ssem_exprs bge vm m es m' vm' es' ->
                                      type_exprs Gamma Sigma es' efs ts /\
                                      store_well_typed Sigma bge vm' m') /\
       (forall Gamma Sigma e ef t, type_expr Gamma Sigma e ef t ->
                                   forall bge vm m vm' m' e', 
                                   store_well_typed Sigma bge vm m ->
                                   ssem_expr bge vm m e m' vm' e' ->
                                   type_expr Gamma Sigma e' ef t /\
                                   store_well_typed Sigma bge vm' m').
+ move=> [] ih ih'. split=> //=.
  + move=> Gamma Sigma es efs ts bge vm m vm' m' es' hts hes.
    by move: (ih Gamma Sigma es efs ts hts bge vm m vm' m' es' hes).
  move=> Gamma Sigma e ef t bge vm m vm' m' e' ht he.
  by move: (ih' Gamma Sigma e ef t ht bge vm m vm' m' e' he).
apply type_exprs_type_expr_ind_mut=> //=.
(* val unit *)
+ move=> Gamma Sigma t vm m vm' m' e' hw he. 
  inversion he; subst; split=> //=. by apply ty_valu.
(* val int *)
+ move=> Gamma Sigma i sz s a bge vm m vm' m' e' hw he.
  inversion he; subst; split=> //=. by apply ty_vali.
(* val long *)
+ move=> Gamma Sigma i s a bge vm m vm' m' e' hw he.
  inversion he; subst; split=> //=. by apply ty_vall.
(* val loc *)
+ move=> Gamma Sigma l ofs h t a hs bge vm m vm' m' e' hw he.
  inversion he; subst; split=> //=. by apply ty_valloc.
(* var *)
+ move=> Gamma Sigma x t ht bge vm m vm' m' e' hw he. 
  inversion he; subst.
  + rewrite /store_well_typed in hw. move: (hw  (extend_context Gamma x t) x).
    rewrite ht /= H1 /=. move=> [] h1 [] h2 [] v'' [] ofs'' [] hd'' [] hv'' ht''.
    have h := well_typed_val_expr bge Gamma Sigma v t empty_effect Full m' l ofs H4 H8.
    by move: (h ht'').
  rewrite /store_well_typed in hw. move: (hw  (extend_context Gamma x t) x).
  rewrite ht /= H1 /=. move=> [] h1 [] h2 [] v'' [] ofs'' [] hd'' [] hv'' [] ht' ht''.
  have h := well_typed_val_expr bge Gamma Sigma v t empty_effect Full m' l ofs H5 H9.
  by move: (h ht'').
(* const int *)
+ move=> Gamma Sigma t sz s a i bge vm m vm' m' e' he; subst.
  inversion he; subst; split=> //=. by apply ty_vali.
(* const long *)
+ move=> Gamma Sigma t s a i bge vm m vm' m' e' he; subst.
  inversion he; subst; split=> //=. by apply ty_vall.
(* const unit *)
+ move=> Gamma Sigma t bge vm m vm' m' e' he; subst.
  inversion he; subst; split=> //=. by apply ty_valu.
(* app *)
+ move=> Gamma Sigma e es rt efs ts ef efs' hte hin htes hin' bge vm m vm' m' e' hw he. 
  inversion he; subst; split=> //=. apply ty_app with ts.
  (* step case *) 
  + by move: (hin bge vm m vm' m' e'0 hw H7)=> [] h1 h2.
  + by apply htes.
  + by move: (hin bge vm m vm' m' e'0 hw H7)=> [] h1 h2.
  admit. (* hard case *) admit.
(* ref *)
+ admit.
(* deref *)
+ move=> Gamma Sigma e ef h bt a hte hin bge vm m vm' m' e' hw he.
  inversion he; subst.
  (* step *)
  + move: (hin bge vm m vm' m' e'0 hw H6)=> [] h1 h2; split=> //=. 
    apply ty_deref with a. by apply h1.
  (* val *)
  split=> //=.
  by have htv := well_typed_val_expr bge Gamma Sigma v (Ptype bt) (ef ++ [:: Read h]) 
              bf m' l ofs H3 H7 erefl. 
(* massgn *)
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
by apply h11.
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
Admitted.


(***** Normalization ******)
(* A well typed program takes multistep to produce a value *)
Lemma normalization :
(forall Gamma Sigma es efs ts bge vm m n m' vm' es', 
 type_exprs Gamma Sigma es efs ts ->
 store_well_typed Sigma bge vm m ->
 ssem_closures bge vm m es n m' vm' es' /\ is_values es') /\
(forall Gamma Sigma e ef t bge vm m n m' vm' e', 
 type_expr Gamma Sigma e ef t ->
 store_well_typed Sigma bge vm m ->
 ssem_closure bge vm m e n m' vm' e' /\ is_value e).
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

 

