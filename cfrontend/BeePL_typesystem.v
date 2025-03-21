Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Globalenvs Coqlib Memory. 
Require Import Csyntax Csem SimplExpr Ctypes Memtype.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL BeePL_auxlemmas Errors BeePL_values.
From mathcomp Require Import all_ssreflect. 

Definition empty_effect : effect := nil. 

Definition type_bool (t : type) : Prop :=
classify_bool t <> bool_default.

Inductive type_expr : ty_context -> store_context -> expr -> effect -> type -> Prop :=
(*For all value expression, we can assume any effect type, including the empty effect *)
| ty_valu : forall Gamma Sigma,
            type_expr Gamma Sigma (Val Vunit (Ptype Tunit)) nil (Ptype Tunit)
| ty_vali : forall Gamma Sigma i sz s a,
            type_expr Gamma Sigma (Val (Vint i) (Ptype (Tint sz s a))) nil (Ptype (Tint sz s a))
| ty_vall : forall Gamma Sigma i s a,
            type_expr Gamma Sigma (Val (Vint64 i) (Ptype (Tlong s a))) nil (Ptype (Tlong s a))
| ty_valloc : forall Gamma Sigma l ofs h t a,
              PTree.get l Sigma = Some (Reftype h t a) ->
              type_expr Gamma Sigma (Val (Vloc l ofs) (Reftype h t a)) nil (Reftype h t a)
| ty_var : forall Gamma Sigma x t, 
           PTree.get x (extend_context Gamma x t) = Some t ->
           type_expr Gamma Sigma (Var x t) nil t
| ty_constint : forall Gamma Sigma sz s a i,
                type_expr Gamma Sigma (Const (ConsInt i) (Ptype (Tint sz s a))) nil (Ptype (Tint sz s a))
| ty_constlong : forall Gamma Sigma s a i,
                 type_expr Gamma Sigma (Const (ConsLong i) (Ptype (Tlong s a))) nil (Ptype (Tlong s a))
| ty_constunit : forall Gamma Sigma,
                 type_expr Gamma Sigma (Const (ConsUnit) (Ptype Tunit)) nil (Ptype Tunit)
(* Fix me *)
| ty_app : forall Gamma Sigma e es rt efs ts ef efs', 
           type_expr Gamma Sigma e ef (Ftype ts efs rt) -> 
           type_exprs Gamma Sigma es efs' ts -> 
           type_expr Gamma Sigma (App e es rt) (ef ++ efs ++ efs') rt

| ty_ref : forall Gamma Sigma e ef h bt a, 
           type_expr Gamma Sigma e ef (Ptype bt) ->
           type_expr Gamma Sigma (Prim Ref (e::nil) (Reftype h (Bprim bt) a)) (ef ++ (Alloc h :: nil)) (Reftype h (Bprim bt) a) 
| ty_deref : forall Gamma Sigma e ef h bt a, (* inner expression should be unrestricted as it will be used later *)
             type_expr Gamma Sigma e ef (Reftype h (Bprim bt) a) -> 
             type_expr Gamma Sigma (Prim Deref (e::nil) (Ptype bt)) (ef ++ (Read h :: nil)) (Ptype bt)
| ty_massgn : forall Gamma Sigma e e' h bt ef a ef', 
              type_expr Gamma Sigma e ef (Reftype h (Bprim bt) a) ->
              type_expr Gamma Sigma e' ef' (Ptype bt) ->
              type_expr Gamma Sigma (Prim Massgn (e::e'::nil) (Ptype Tunit)) (ef ++ ef' ++ (Write h :: nil)) (Ptype Tunit)
| ty_uop : forall Gamma Sigma op e ef t,
           is_reftype t = false ->
           is_unittype t = false ->
           type_expr Gamma Sigma e ef t ->
           type_expr Gamma Sigma (Prim (Uop op) (e::nil) t) ef t
| ty_bop : forall Gamma Sigma op e ef t e',
           is_reftype t = false ->
           is_unittype t = false ->
           type_expr Gamma Sigma e ef t ->
           type_expr Gamma Sigma e' ef t ->
           type_expr Gamma Sigma (Prim (Bop op) (e::e'::nil) t) ef t 
| ty_bind : forall Gamma Sigma x t e e' t' ef ef',
            type_expr Gamma Sigma e ef t ->
            type_expr (extend_context Gamma x t) Sigma e' ef' t' ->
            type_expr Gamma Sigma (Bind x t e e' t') (ef ++ ef') t'
| ty_cond : forall Gamma Sigma e1 e2 e3 tb t ef1 ef2, 
            type_expr Gamma Sigma e1 ef1 tb ->
            type_bool tb ->
            type_expr Gamma Sigma e2 ef2 t ->
            type_expr Gamma Sigma e3 ef2 t ->
            type_expr Gamma Sigma (Cond e1 e2 e3 t) (ef1 ++ ef2) t
| ty_unit : forall Gamma Sigma,
            type_expr Gamma Sigma (Unit (Ptype Tunit)) empty_effect (Ptype Tunit)
| ty_addr : forall Gamma Sigma l ofs h t a,
            PTree.get l.(lname) Sigma = Some (Reftype h t a) ->
            (*t' = (Reftype h t a) ->*)
            type_expr Gamma Sigma (Addr l ofs (Reftype h t a)) empty_effect (Reftype h t a) 
(* return type, arg types, and effect must agree with the signature
   eBPF helper functions never return a void type and a function  *)
| ty_ext : forall Gamma Sigma exf ts es ef rt,
           rt = get_rt_eapp exf ->
           rt <> Ptype Tunit /\ is_funtype rt = false -> 
           ts = get_at_eapp exf ->
           type_exprs Gamma Sigma es ef ts ->
           type_expr Gamma Sigma (Eapp exf ts es rt) ((get_ef_eapp exf) ++ ef) rt
| ty_sub : forall Gamma Sigma e ef t ef', 
           type_expr Gamma Sigma e ef t ->
           sub_effect ef ef' ->
           type_expr Gamma Sigma e ef' t
(* fix me : Run *)
(* fix me : Hexpr *)
(*| ty_hexpr : forall Gamma Sigma m e h ef t a, 
             type_expr Gamma Sigma e ef (Reftype h (Bprim t) a) ->
             type_expr Gamma Sigma (Hexpr m e (Reftype h (Bprim t) a)) ef (Reftype h (Bprim t) a)*)
(* fix me : Add typing rule for external function *)
with type_exprs : ty_context -> store_context -> list expr -> effect -> list type -> Prop :=
| ty_nil : forall Gamma Sigma,
           type_exprs Gamma Sigma nil nil nil
| ty_cons : forall Gamma Sigma e es ef efs t ts,
            type_expr Gamma Sigma e ef t ->
            type_exprs Gamma Sigma es efs ts ->
            type_exprs Gamma Sigma (e :: es) (ef ++ efs) (t :: ts).
           
Scheme type_expr_ind_mut := Induction for type_expr Sort Prop
  with type_exprs_ind_mut := Induction for type_exprs Sort Prop.
Combined Scheme type_exprs_type_expr_ind_mut from type_exprs_ind_mut, type_expr_ind_mut.

(* Value typing *)
(* A value does not produce any effect *)
Lemma value_typing : forall Gamma Sigma ef t v,
type_expr Gamma Sigma (Val v t) ef t ->
type_expr Gamma Sigma (Val v t) nil t. 
Proof.
move=> Gamma Sigma ef t v. move eq : (Val v t)=> v' ht.
elim: ht eq=> //=.
+ move=> Gamma' Sigma' [] h1; subst. by apply ty_valu.
+ move=> Gamma' Sigma' i sz s a [] h1; subst. by apply ty_vali.
+ move=> Gamma' Sigma' i s a [] h1; subst. by apply ty_vall.
move=> Gamma' Sigma' l ofs h bt a hs [] h1; subst. by apply ty_valloc. 
Qed.

Lemma type_infer_vunit: forall Gamma Sigma ef t t', 
type_expr Gamma Sigma (Val Vunit t) ef t' ->
t = Ptype Tunit /\ t' = Ptype Tunit.
Proof.
move=> Gamma Sigma ef t t'. 
move eq : (Val Vunit t)=> v ht. elim: ht eq=>//=.
by move=> Gamma' Sigma' [] h; subst.
Qed.

Lemma type_infer_int: forall Gamma Sigma i ef t t', 
type_expr Gamma Sigma (Val (Vint i) t) ef t' ->
(exists sz s a, t = Ptype (Tint sz s a) /\ t' = Ptype (Tint sz s a)).
Proof.
move=> Gamma Sigma i ef t t'. 
move eq : (Val (Vint i) t)=> v ht. 
elim: ht eq=>//=. move=> Gamma' Sigma' i' sz' s' a' [] h1 h2; subst. 
by exists sz', s', a'.
Qed.

Lemma type_infer_long: forall Gamma Sigma i ef t t', 
type_expr Gamma Sigma (Val (Vint64 i) t) ef t' ->
(exists s a, t = Ptype (Tlong s a) /\ t' = Ptype (Tlong s a)).
Proof.
move=> Gamma Sigma i ef t t'. 
move eq : (Val (Vint64 i) t)=> v ht. 
elim: ht eq=>//=. move=> Gamma' Sigma' i' s' a' [] h2 h3; subst.
by exists s', a'.
Qed.

Lemma type_infer_loc: forall Gamma Sigma l ofs ef t t', 
type_expr Gamma Sigma (Val (Vloc l ofs) t) ef t' ->
(exists h bt a, t = Reftype h bt a /\ 
                t' = Reftype h bt a /\ 
                PTree.get l Sigma = Some (Reftype h bt a)).
Proof.
move=> Gamma Sigma l ofs ef t t'. 
move eq : (Val (Vloc l ofs) t)=> v ht. elim: ht eq=>//=.
move=> Gamma' Sigma' l' ofs' h' bt' a' hs [] h1 h2 h3; subst. 
by exists h', bt', a'.
Qed.

Lemma type_infer_var : forall Gamma Sigma x t ef t',
type_expr Gamma Sigma (Var x t) ef t' ->
t = t' /\ PTree.get x (extend_context Gamma x t) = Some t.
Proof.
move=> Gamma Sigma x t ef t'. 
move eq: (Var x t)=> v ht. elim: ht eq=> //=.
by move=> Gamma' Sigma' x' t'' hxt [] h1 h2; subst.
Qed.

Lemma type_infer_consti: forall Gamma Sigma i ef t t', 
type_expr Gamma Sigma (Const (ConsInt i) t) ef t' ->
(exists sz s a, t = Ptype (Tint sz s a) /\ t' = Ptype (Tint sz s a)).
Proof.
move=> Gamma Sigma i ef t t'. 
move eq : (Const (ConsInt i) t)=> v ht. 
elim: ht eq=>//=. move=> Gamma' Sigma' sz' s' a' i' [] h1 h2; subst. 
by exists sz', s', a'.
Qed.

Lemma type_infer_constl: forall Gamma Sigma i ef t t', 
type_expr Gamma Sigma (Const (ConsLong i) t) ef t' ->
(exists s a, t = Ptype (Tlong s a) /\ t' = Ptype (Tlong s a)).
Proof.
move=> Gamma Sigma i ef t t'. 
move eq : (Const (ConsLong i) t)=> v ht. 
elim: ht eq=>//=. move=> Gamma' Sigma' s' a' i' [] h1 h2; subst. 
by exists s', a'.
Qed.

Lemma type_infer_constu: forall Gamma Sigma ef t t', 
type_expr Gamma Sigma (Const ConsUnit t) ef t' ->
t = Ptype Tunit /\ t' = Ptype Tunit.
Proof.
move=> Gamma Sigma ef t t'. 
move eq : (Const ConsUnit t)=> v ht. elim: ht eq=>//=.
by move=> Gamma' Sigma' [] h1; subst.
Qed.

Lemma type_infer_app: forall Gamma Sigma e es rt ef t,
type_expr Gamma Sigma (App e es rt) ef t ->
(t = rt /\
exists ts ef' efs, type_expr Gamma Sigma e ef' (Ftype ts efs rt) /\ 
exists efs', type_exprs Gamma Sigma es efs' ts).
Proof.
move=> Gamma Sigma e es rt ef t.
move eq: (App e es rt)=> ve ht. elim: ht eq=> //=.
move=> Gamma' Sigma' e' es' rt' efs ts ef' efs' ht1 hin ht2 [] h1 h2 h3; subst; split=> //=.
exists ts, ef', efs; split=> //=. by exists efs'.
Qed.

Lemma type_infer_ref: forall Gamma Sigma e ef t t',
type_expr Gamma Sigma (Prim Ref [:: e] t) ef t' ->
(exists h bt a, t = (Reftype h (Bprim bt) a) /\ t' = Reftype h (Bprim bt) a).
Proof.
move=> Gamma Sigma e ef t t'.
move eq: (Prim Ref [:: e] t)=> rv ht.
elim: ht eq=> //=.
move=> Gamma' Sigma' e' ef' h' bt' a' ht hin [] h1 h2; subst.
by exists h', bt', a'.
Qed.

Lemma type_infer_deref: forall Gamma Sigma e ef t t',
type_expr Gamma Sigma (Prim Deref [:: e] t) ef t' ->
(exists h bt a ef', t = Ptype bt /\ 
                    t' = Ptype bt /\
                    type_expr Gamma Sigma e ef' (Reftype h (Bprim bt) a)).
Proof.
move=> Gamma Sigma e ef t t'.
move eq: (Prim Deref [:: e] t)=> rv ht.
elim: ht eq=> //=.
move=> Gamma' Sigma' e' ef' h' bt' a' ht1 hin1 [] h1 h2; subst.
by exists h', bt', a', ef'. 
Qed.

Lemma type_infer_massgn: forall Gamma Sigma e e' ef t t',
type_expr Gamma Sigma (Prim Massgn [:: e; e'] t) ef t' ->
(t = Ptype Tunit /\ t' = Ptype Tunit /\
 (exists h bt a ef1 ef2, type_expr Gamma Sigma e ef1 (Reftype h (Bprim bt) a) /\
                        type_expr Gamma Sigma e' ef2 (Ptype bt))). 
Proof.
move=> Gamma Sigma e e' ef t t'.
move eq: (Prim Massgn [:: e; e'] t)=> rv ht.
elim: ht eq=> //=.
move=> Gamma' Sigma' e1 e2 h bt ef1 a ef2 ht hin ht' hin2 [] h1 h2 h3; subst; split=> //=.
split=> //=. by exists h, bt, a, ef1, ef2.
Qed.

Lemma type_infer_uop: forall Gamma Sigma e uop t ef t',
type_expr Gamma Sigma (Prim (Uop uop) [:: e] t) ef t' ->
t' = t /\ 
is_reftype t = false /\
is_unittype t = false /\
exists ef', type_expr Gamma Sigma e ef' t.
Proof.
move=> Gamma Sigma e uop t ef t'.
move eq: (Prim (Uop uop) [:: e] t)=> rv ht.
elim: ht eq=> //=.
move=> Gamma' Sigma' op e' ef' t'' hrt hut hte' hin [] h1 h2 h3; subst; split=> //=.
split=> //=; split=> //=. by exists ef'. 
Qed.

Lemma type_infer_bop: forall Gamma Sigma e e' t bop ef t',
type_expr Gamma Sigma (Prim (Bop bop) [:: e; e'] t) ef t' ->
t' = t /\
is_reftype t = false /\
is_unittype t = false /\
(exists ef', type_expr Gamma Sigma e ef' t /\
             type_expr Gamma Sigma e' ef' t).
Proof.
move=> Gamma Sigma e e' t bop ef t'.
move eq: (Prim (Bop bop) [:: e; e'] t)=> rv ht.
elim: ht eq=> //=.
move=> Gamma' Sigma' op e1 ef1 t1 e2 hrt hut ht1 hin1 ht2 hin2
       [] h1 h2 h3 h4; subst; split=> //=; split=> //=; split=> //=.
by exists ef1.
Qed.

Lemma type_infer_bind: forall Gamma Sigma e x t e' t' ef t'',
type_expr Gamma Sigma (Bind x t e e' t') ef t'' ->
(t'' = t' /\
exists ef' ef'', type_expr Gamma Sigma e ef'' t /\
                 type_expr (extend_context Gamma x t) Sigma e' ef' t').
Proof.
move=> Gamma Sigma e x t e' t' ef t''.
move eq:(Bind x t e e' t')=> rv ht. elim: ht eq=> //=.
move=> Gamma' Sigma' x' t1 e1 e2 t2 ef1 ef' ht1 hin ht2 hin'
       [] h1 h2 h3 h4 h5; subst; split=> //=. by exists ef', ef1.
Qed.

Lemma type_infer_cond: forall Gamma Sigma e1 e2 e3 t ef' t',
type_expr Gamma Sigma (Cond e1 e2 e3 t) ef' t' ->
t' = t /\
exists tb ef1 ef2, type_expr Gamma Sigma e1 ef1 tb /\
                   type_bool tb /\
                   type_expr Gamma Sigma e2 ef2 t /\
                   type_expr Gamma Sigma e3 ef2 t.
Proof.
move=> Gamma Sigma e1 e2 e3 t ef' t'.
move eq: (Cond e1 e2 e3 t)=> rv ht.
elim: ht eq=> //=.
move=> Gamma' Sigma' e1' e2' e3' tb t1 ef1 ef2 ht1 hin1 htb
       ht2 hin2 ht3 hin3 [] h1 h2 h3 h4; subst; split=> //=.
by exists tb, ef1, ef2.
Qed.

Lemma type_infer_unit: forall Gamma Sigma ef t t',
type_expr Gamma Sigma (Unit t) ef t' ->
t = Ptype Tunit /\ t' = Ptype Tunit.
Proof.
move=> Gamma Sigma ef t t'. move eq: (Unit t)=> rv ht.
elim: ht eq=> //=. by move=> Gamma' Sigma' [] h; subst.
Qed.

Lemma type_infer_addr: forall Gamma Sigma l ofs ef t t',
type_expr Gamma Sigma (Addr l ofs t) ef t' ->
(exists h bt a, t = Reftype h bt a /\ 
                t'= Reftype h bt a /\ 
                PTree.get l.(lname) Sigma = Some (Reftype h bt a)).
Proof.
move=> Gamma Sigma l ofs ef t t'.
move eq: (Addr l ofs t)=> rv ht.
elim: ht eq=> //=.
move=> Gamma' Sigma' l' ofs' h' bt' a' hs [] h1 h2; subst.
by exists h', bt', a'.
Qed.

Lemma type_infer_eapp: forall Gamma Sigma exf es ef rt t,
type_expr Gamma Sigma (Eapp exf (get_at_eapp exf) es rt) ef t ->
rt = get_rt_eapp exf /\ 
t = rt /\
rt <> Ptype Tunit /\ 
is_funtype rt = false /\ 
(exists ts ef', ts = get_at_eapp exf /\
                type_exprs Gamma Sigma es ef' ts).
Proof.
move=> Gamma Sigma exf es ef rt t. 
move eq: (Eapp exf (get_at_eapp exf) es rt)=> rv ht.
elim: ht eq=> //=.
move=> Gamma' Sigma' exf' ts es' ef' rt' hrt [] hr1 hr2 hts hes' []
       h1 h2 h3 h4; subst; split=> //=; split=> //=; split=> //=; split=> //=.
by exists (get_at_eapp exf');exists ef';split=> //=.
Qed.

Lemma type_val_reflx : forall Gamma Sigma v t ef t',
type_expr Gamma Sigma (Val v t) ef t' -> 
t = t'.
Proof.
move=> Gamma Sigma v t ef t'. move eq: (Val v t)=> rv ht. 
elim: ht eq=> //=.  
+ by move=> Gamma' Sigma' [] h; subst.
+ by move=> Gamma' Sigma' i sz s a [] h h'; subst.
+ by move=> Gamma' Sigma' i s a [] h h'; subst.
by move=> Gamma' Sigma' l ofs h t'' a hs [] h1 h2; subst.
Qed.

Lemma type_expr_exprs_deterministic: 
(forall Gamma Sigma es efs ts efs' ts', type_exprs Gamma Sigma es efs ts ->
                                        type_exprs Gamma Sigma es efs' ts' ->
                                        ts = ts') /\
(forall Gamma Sigma e ef t ef' t', type_expr Gamma Sigma e ef t ->
                                   type_expr Gamma Sigma e ef' t' ->
                                   t = t').
Proof.
suff : (forall Gamma Sigma es efs ts, type_exprs Gamma Sigma es efs ts ->
                                      forall efs' ts', type_exprs Gamma Sigma es efs' ts' ->
                                                       ts = ts') /\
       (forall Gamma Sigma e ef t, type_expr Gamma Sigma e ef t ->
                                   forall ef' t', type_expr Gamma Sigma e ef' t' ->
                                                  t = t').
+ move=> [] ih ih'. split=> //=.
  + move=> Gamma Sigma es efs ts efs' ts' hes hes'. 
    by move: (ih Gamma Sigma es efs ts hes efs' ts' hes').
  move=> Gamma Sigma e ef t ef' t' he he'.
  by move: (ih' Gamma Sigma e ef t he ef' t' he').
apply type_exprs_type_expr_ind_mut => //=.
+ move=> Gamma Sigma ef' t' ht; inversion ht; subst; auto.
  by have [h1 h2] := type_infer_vunit Gamma Sigma ef' (Ptype Tunit) t' ht.
+ move=> Gamma Sigma i sz s a ef' t' ht; inversion ht; subst; auto.
  have := type_infer_int Gamma Sigma i ef' (Ptype (Tint sz s a)) t' ht. 
  by move=> [] sz' [] s' [] a' [] h1 h2; subst.
+ move=> Gamma Sigma i s a ef' t' ht; inversion ht; subst; auto.
  have := type_infer_long Gamma Sigma i ef' (Ptype (Tlong s a)) t' ht.
  by move=> [] s' [] a' [] h1 h2; subst.
+ move=> Gamma Sigma l ofs h t a hs ef' t' ht; inversion ht; subst; auto.
  have := type_infer_loc Gamma Sigma l ofs ef' (Reftype h t a) t' ht.
  by move=> [] h' [] bt [] a' [] h1 [] h2 h3; subst.
+ move=> Gamma Sigma x t ht ef' t' ht'; subst; inversion ht'; subst; auto.
  by have [h1 h2]:= type_infer_var Gamma Sigma x t ef' t' ht'.
+ move=> Gamma Sigma sz s a i ef' t' ht; subst; inversion ht; subst; auto.
  have := type_infer_consti Gamma Sigma i ef' (Ptype (Tint sz s a)) t' ht.
  by move=> [] sz' [] s' [] a' [] h1 h2; subst.
+ move=> Gamma Sigma s a i ef' t' ht; subst; inversion ht; subst; auto.
  have := type_infer_constl Gamma Sigma i ef' (Ptype (Tlong s a)) t' ht.
  by move=> [] s' [] a' [] h1 h2; subst.
+ move=> Gamma Sigma ef' t' ht; inversion ht; subst; auto.
  have := type_infer_constu Gamma Sigma ef' (Ptype Tunit) t' ht.
  by move=> [] h h'.
+ move=> Gamma Sigma e es rt efs ts ef efs' hte hin htes hin' ef' t ht; 
  inversion ht; subst; auto.
  by have [h [ts'] [ef1 [efs1] [] ht' [efs'' hts]]]:= type_infer_app Gamma Sigma e es rt ef' t ht.
+ move=> Gamma Sigma e ef h bt a hte hin ef' t' ht; inversion ht; subst; auto.
  have := type_infer_ref Gamma Sigma e ef' (Reftype h (Bprim bt) a) t' ht.
  by move=> [] h' [] bt' [] a' [] h1 h2; subst.
+ move=> Gamma Sigma e ef h bt a hte ef' ef'' t' ht; inversion ht; subst; auto.
  have := type_infer_deref Gamma Sigma e ef'' (Ptype bt) t' ht.
  by move=> [] h' [] bt' [] a' [] ef1 [] h1 [] h2 h3; subst. 
+ move=> Gamma Sigma e e' h bt ef a ef' hte hin hte' hin' ef'' t' ht; subst; auto.
  have := type_infer_massgn Gamma Sigma e e' ef'' (Ptype Tunit) t' ht.
  by move=> [] hu [] hu' [] h' [] bt' [] a' [] ef1 [] ef2 [] h1 h2.
+ move=> Gamma Sigma op e ef t hrt hut hte hin ef' t' ht; inversion ht; subst; auto.
  by have [h1 [h2 [h3 [ef1 h4]]]] := type_infer_uop Gamma Sigma e op t ef' t' ht.
+ move=> Gamma Sigma op e ef t e' hrt hut hte hin hte' hin' 
  ef' t' ht; inversion ht; subst; auto.
  by have [h1 [h2 [h3 [ef1 [h4 h5]]]]]:= type_infer_bop Gamma Sigma e e' t op ef' t' ht.
+ move=> Gamma Sigma x t e e' t' ef ef' hte hin hte' hin' ef'' t'' ht; 
  inversion ht; subst; auto.
  by have [h1 [ef1 [ef2 [h11 h12]]]] := type_infer_bind Gamma Sigma e x t e' t' ef'' t'' ht.
+ move=> Gamma Sigma e1 e2 e3 tb t ef1 ef2 hte1 hin1 htb hte2 hin2 hte3 hin3 ef' t'
         ht; inversion ht; subst; auto.
  by have [h1 [tb' [ef1' [ef2' [ht1 [htb' [h11 h12]]]]]]]:= type_infer_cond Gamma Sigma 
  e1 e2 e3 t ef' t' ht.
+ move=> Gamma Sigma ef' t' ht; inversion ht; subst; auto.
  have := type_infer_unit Gamma Sigma ef' (Ptype Tunit) t' ht.
  by move=> [] hut hut'.
+ move=> Gamma Sigma l ofs h t a hs ef' t' ht; inversion ht; subst; auto.
  have := type_infer_addr Gamma Sigma l ofs ef' (Reftype h t a) t' ht.
  by move=> [] h' [] bt' [] a' [] h1 [] h2 h3; subst.
+ move=> Gamma Sigma exf ts es ef rt hrt [] h1 h2 h3 ht1 hin ef' t' ht; subst;
         inversion ht; subst; auto.
  by have [h11 [h12 [h13 [h14 [ts [ef'' h15]]]]]] := type_infer_eapp Gamma Sigma exf
    es ef' (get_rt_eapp exf) t' ht.
+ by move=> Gamma Sigma efs' ts' ht; inversion ht; subst; auto.
move=> Gamma Sigma e es ef efs t ts hte hin htes hin' efs' ts' ht;
       inversion ht; subst; auto.
move: (hin ef0 t0 H3)=> ->. by move: (hin' efs0 ts0 H6)=> ->.
Qed.

Lemma type_rel_typeof : forall Gamma Sigma e ef t,
type_expr Gamma Sigma e ef t ->
typeof_expr e = t.
Proof.
by move=> Gamma Sigma e ef t ht; elim: ht=> //=.
Qed.

Lemma eq_type_rel : forall v t t',
eq_type t t' ->
wtypeof_value v (wtype_of_type t') ->
wtypeof_value v (wtype_of_type t).
Proof.
move=> v t t'. case: t=> //=.
+ move=> p. case: t'=> //= p'.
  case:p=> //=.
  + by case: p'=> //=.
  + by case: p'=> //=.
  by case: p'=> //=.
+ by case: t'=> //=. 
by case: t'=> //=.
Qed.

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


(* Complete Me: Easy *)
(* There always exists a C type for BeePL type which is 
   inferred from the typing rules. *)
Lemma well_typed_success: 
(forall Gamma Sigma es efs ts, type_exprs Gamma Sigma es efs ts ->
                               exists cts g i, transBeePL_types transBeePL_type ts g = Res cts g i) /\
(forall Gamma Sigma e ef t, type_expr Gamma Sigma e ef t ->
                            exists ct g i, transBeePL_type t g = Res ct g i).
Proof.
apply type_exprs_type_expr_ind_mut=> //=.
Admitted.
