Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Globalenvs Coqlib Memory. 
Require Import Csyntax Csem SimplExpr Ctypes Memtype.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL BeePL_auxlemmas Errors.
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

| ty_prim_ref : forall Gamma Sigma e ef h bt a, 
                type_expr Gamma Sigma e ef (Ptype bt) ->
                type_expr Gamma Sigma (Prim Ref (e::nil) (Reftype h (Bprim bt) a)) (ef ++ (Alloc h :: nil)) (Reftype h (Bprim bt) a) 
| ty_prim_deref : forall Gamma Sigma e ef h bt a, (* inner expression should be unrestricted as it will be used later *)
                  type_expr Gamma Sigma e ef (Reftype h (Bprim bt) a) -> 
                  type_expr Gamma Sigma (Prim Deref (e::nil) (Ptype bt)) (ef ++ (Read h :: nil)) (Ptype bt)
| ty_prim_massgn : forall Gamma Sigma e e' h bt ef a ef', 
                   type_expr Gamma Sigma e ef (Reftype h (Bprim bt) a) ->
                   type_expr Gamma Sigma e' ef' (Ptype bt) ->
                   type_expr Gamma Sigma (Prim Massgn (e::e'::nil) (Ptype Tunit)) (ef ++ ef' ++ (Write h :: nil)) (Ptype Tunit)
| ty_prim_uop : forall Gamma Sigma op e ef t,
                is_reftype t = false ->
                is_unittype t = false ->
                type_expr Gamma Sigma e ef t ->
                (*type_expr Gamma Sigma e (ef ++ ef') t ->*)
                type_expr Gamma Sigma (Prim (Uop op) (e::nil) t) ef t
                (*type_expr Gamma Sigma (Prim (Uop op) (e::nil) t) (ef ++ ef') t*)
| ty_prim_bop : forall Gamma Sigma op e ef t e',
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


(*Inductive type_expr : ty_context -> store_context -> expr -> effect -> type -> Prop :=
(*For all value expression, we can assume any effect type, including the empty effect *)
| ty_valu : forall Gamma Sigma ef,
            type_expr Gamma Sigma (Val Vunit (Ptype Tunit)) ef (Ptype Tunit)
| ty_vali : forall Gamma Sigma ef i sz s a,
            type_expr Gamma Sigma (Val (Vint i) (Ptype (Tint sz s a))) ef (Ptype (Tint sz s a))
| ty_vall : forall Gamma Sigma ef i s a,
            type_expr Gamma Sigma (Val (Vint64 i) (Ptype (Tlong s a))) ef (Ptype (Tlong s a))
| ty_valloc : forall Gamma Sigma ef l ofs h t a,
              PTree.get l Sigma = Some (Reftype h t a) ->
              type_expr Gamma Sigma (Val (Vloc l ofs) (Reftype h t a)) ef (Reftype h t a)
| ty_var : forall Gamma Sigma x t ef, 
           PTree.get x (extend_context Gamma x t) = Some t ->
           sub_effect nil ef ->
           type_expr Gamma Sigma (Var x t) ef t
| ty_consti : forall Gamma Sigma sz s a i ef,
              sub_effect nil ef ->
              type_expr Gamma Sigma (Const (ConsInt i) (Ptype (Tint sz s a))) ef (Ptype (Tint sz s a))
| ty_constl : forall Gamma Sigma s a i ef,
              sub_effect nil ef ->
              type_expr Gamma Sigma (Const (ConsLong i) (Ptype (Tlong s a))) ef (Ptype (Tlong s a))
| ty_constu : forall Gamma Sigma ef,
              sub_effect nil ef ->
              type_expr Gamma Sigma (Const (ConsUnit) (Ptype Tunit)) ef (Ptype Tunit)
(* Fix me *)
| ty_app : forall Gamma Sigma e es rt efs ts ef efb ef' efs' efb' ef1, 
           type_expr Gamma Sigma e ef (Ftype ts efs rt) -> 
           sub_effect ef ef' ->
           sub_effect efs efs' ->
           type_exprs Gamma Sigma es efb ts ->
           sub_effect efb efb' ->
           sub_effect (ef' ++ efs' ++ efb') ef1 ->
           type_expr Gamma Sigma (App e es rt) ef1 rt
| ty_ref : forall Gamma Sigma e ef h bt a ef' ef'', 
           type_expr Gamma Sigma e ef (Ptype bt) ->
           sub_effect ef ef' ->
           sub_effect (ef' ++ (Alloc h :: nil)) ef'' ->
           type_expr Gamma Sigma (Prim Ref (e::nil) (Reftype h (Bprim bt) a)) ef'' (Reftype h (Bprim bt) a)
| ty_deref : forall Gamma Sigma e ef h bt a ef' ef'', (* inner expression should be unrestricted as it will be used later *)
             type_expr Gamma Sigma e ef (Reftype h (Bprim bt) a) -> 
             sub_effect ef ef' ->
             sub_effect (ef' ++ (Read h :: nil)) ef'' ->
             type_expr Gamma Sigma (Prim Deref (e::nil) (Ptype bt)) ef'' (Ptype bt)
| ty_massgn : forall Gamma Sigma e1 e2 h bt ef1 a ef2 ef1' ef2' ef, 
              type_expr Gamma Sigma e1 ef1 (Reftype h (Bprim bt) a) ->
              sub_effect ef1 ef1' ->
              type_expr Gamma Sigma e2 ef2 (Ptype bt) ->
              sub_effect ef2 ef2' ->
              sub_effect (ef1' ++ ef2' ++ (Write h :: nil)) ef ->
              type_expr Gamma Sigma (Prim Massgn (e1::e2::nil) (Ptype Tunit)) ef (Ptype Tunit)
| ty_uop : forall Gamma Sigma op e ef t ef',
           is_reftype t = false ->
           is_unittype t = false ->
           type_expr Gamma Sigma e ef t ->
           sub_effect ef ef' ->
           type_expr Gamma Sigma (Prim (Uop op) (e::nil) t) ef' t
| ty_bop : forall Gamma Sigma op e ef t e' ef',
           is_reftype t = false ->
           is_unittype t = false ->
           type_expr Gamma Sigma e ef t ->
           type_expr Gamma Sigma e' ef t ->
           sub_effect ef ef' ->
           type_expr Gamma Sigma (Prim (Bop op) (e::e'::nil) t) ef' t 
| ty_bind : forall Gamma Sigma x t e e' t' ef1 ef2 ef,
            type_expr Gamma Sigma e ef1 t ->
            type_expr (extend_context Gamma x t) Sigma e' ef2 t' ->
            sub_effect (ef1 ++ ef2) ef ->
            type_expr Gamma Sigma (Bind x t e e' t') ef t'
| ty_cond : forall Gamma Sigma e1 e2 e3 tb t ef1 ef2 ef3 ef1' ef, 
            type_expr Gamma Sigma e1 ef1 tb ->
            sub_effect ef1 ef1' ->
            type_bool tb ->
            type_expr Gamma Sigma e2 ef2 t ->
            sub_effect ef2 ef = true ->
            type_expr Gamma Sigma e3 ef3 t ->
            sub_effect ef3 ef = true ->
            (*sub_effect (ef1' ++ ef) ef' ->*)
            type_expr Gamma Sigma (Cond e1 e2 e3 t) (ef1' ++ ef) t
| ty_unit : forall Gamma Sigma ef,
            type_expr Gamma Sigma (Unit (Ptype Tunit)) nil (Ptype Tunit) ->
            sub_effect nil ef ->
            type_expr Gamma Sigma (Unit (Ptype Tunit)) ef (Ptype Tunit)
| ty_addr : forall Gamma Sigma l ofs h t a ef,
            PTree.get l.(lname) Sigma = Some (Reftype h t a) ->
            type_expr Gamma Sigma (Addr l ofs (Reftype h t a)) nil (Reftype h t a) ->
            sub_effect nil ef -> 
            type_expr Gamma Sigma (Addr l ofs (Reftype h t a)) ef (Reftype h t a)
(* return type, arg types, and effect must agree with the signature
   eBPF helper functions never return a void type  *)
| ty_ext : forall Gamma Sigma exf ts es ef rt ef' ef'',
           rt = get_rt_eapp exf ->
           rt <> Ptype Tunit /\ is_funtype rt = false -> 
           ts = get_at_eapp exf ->
           type_exprs Gamma Sigma es ef ts ->
           sub_effect ef ef' ->
           sub_effect ((get_ef_eapp exf) ++ ef') ef'' ->
           type_expr Gamma Sigma (Eapp exf ts es rt) ef'' rt
(* fix me : Run *)
(* fix me : Hexpr *)
(*| ty_hexpr : forall Gamma Sigma m e h ef t a, 
             type_expr Gamma Sigma e ef (Reftype h (Bprim t) a) ->
             type_expr Gamma Sigma (Hexpr m e (Reftype h (Bprim t) a)) ef (Reftype h (Bprim t) a)*)
(* fix me : Add typing rule for external function *)
with type_exprs : ty_context -> store_context -> list expr -> effect -> list type -> Prop :=
| ty_nil : forall Gamma Sigma ef,
           type_exprs Gamma Sigma nil nil nil ->
           sub_effect nil ef ->
           type_exprs Gamma Sigma nil ef nil
| ty_cons : forall Gamma Sigma e es ef efs t ts ef' efs' ef'',
            type_expr Gamma Sigma e ef t ->
            sub_effect ef ef' ->
            type_exprs Gamma Sigma es efs ts ->
            sub_effect efs efs' ->
            sub_effect (ef' ++ efs') ef'' ->
            type_exprs Gamma Sigma (e :: es) ef'' (t :: ts).
           
Scheme type_expr_ind_mut := Induction for type_expr Sort Prop
  with type_exprs_ind_mut := Induction for type_exprs Sort Prop.
Combined Scheme type_exprs_type_expr_ind_mut from type_exprs_ind_mut, type_expr_ind_mut.*)

(* The (EXTEND) rule states that we can always assume a worse effect; 
   this rule is not part of the inference rules but
   we need it to show subject reduction of stateful computations. : Leijen's koka paper *)
(* This hypothesis makes the type system non-deterministic *)
(*Hypothesis ty_extend : forall Gamma Sigma e t ef, 
                        type_expr Gamma Sigma e empty_effect t ->
                        type_expr Gamma Sigma e (ef ++ empty_effect) t.*)

(* Complete Me: Easy *)
Lemma sub_effect_refl : forall ef, 
sub_effect ef ef = true.
Proof.
Admitted.

(* Complete Me: Easy *)
Lemma sub_effect_nil : forall ef, 
sub_effect nil ef = true.
Proof.
Admitted.

(* Complete Me: Easy *)
Lemma sub_effect_trans : forall ef1 ef2 ef3, 
sub_effect ef1 ef2 = true ->
sub_effect ef2 ef3 = true ->
sub_effect ef1 ef3 = true.
Proof.
Admitted.

(*Lemma extend_effect : 
(forall Gamma Sigma es efs ts efs', type_exprs Gamma Sigma es efs ts ->
                                    sub_effect efs efs' ->
                                    type_exprs Gamma Sigma es efs' ts) /\
(forall Gamma Sigma e ef t ef', type_expr Gamma Sigma e ef t ->
                                sub_effect ef ef' ->
                                type_expr Gamma Sigma e ef' t).
Proof.
suff : (forall Gamma Sigma es efs ts, type_exprs Gamma Sigma es efs ts ->
                                      forall efs', sub_effect efs efs' -> 
                                                   type_exprs Gamma Sigma es efs' ts) /\
       (forall Gamma Sigma e ef t, type_expr Gamma Sigma e ef t ->
                                   forall ef', sub_effect ef ef' ->
                                               type_expr Gamma Sigma e ef' t).
+ move=> [] hin hin'. split=> //=.
  + move=> Gamma Sigma es efs ts efs' hts hs.
    by move: (hin Gamma Sigma es efs ts hts efs' hs).
  move=> Gamma Sigma e ef t ef' ht hs.
  by move: (hin' Gamma Sigma e ef t ht ef' hs).
apply type_exprs_type_expr_ind_mut=> //=.
(* val unit *)
+ move=> Gamma Sigma ef ef' hs. by apply ty_valu.
(* val int *)
+ move=> Gamma Sigma ef ef' i sz s a hs. by apply ty_vali.
(* val long *)
+ move=> Gamma Sigma ef ef' i s a hs. by apply ty_vall.
(* val loc *)
+ move=> Gamma Sigma ef l ofs h t a hsi ef' hs. by apply ty_valloc.
(* var *)
+ move=> Gamma Sigma x t ef hte _ ef' hs. by apply ty_var.
(* const int *)
+ move=> Gamma Sigma sz s a i ef _ ef' hs. by apply ty_consti.
(* const long *)
+ move=> Gamma Sigma s a i ef _ ef' hs. by apply ty_constl.
(* const unit *)
+ move=> Gamma Sigma ef _ ef' hs. by apply ty_constu.
(* app *)
+ move=> Gamma Sigma e es rt efs ts ef efb ef' efs' efb' ef1 
  hte hin hs1 hs2 htes hin' hs3 hs4 ef2 hs5.
  apply ty_app with efs ts ef efb ef' efs' efb'.
  + by apply hte. + by apply hs1. + by apply hs2. + by apply htes.
  + by apply hs3. 
  by have := sub_effect_trans (ef' ++ efs' ++ efb') ef1 ef2 hs4 hs5.
(* ref *)
+ move=> Gamma Sigma e ef h bt a ef' ef'' hte hin hs hs' ef''' hs''.
  apply ty_ref with ef ef'.
  + by apply hte.
  + by apply hs.
  by have := sub_effect_trans (ef' ++ [:: Alloc h]) ef'' ef''' hs' hs''.
(* deref *)
+ move=> Gamma Sigma e ef h bt a ef' ef'' ht hin hs1 hs2 ef1 hs3. 
  apply ty_deref with ef h a ef'. + by apply ht. by apply hs1.
  by have := sub_effect_trans (ef' ++ [:: Read h]) ef'' ef1 hs2 hs3.
(* massgn *)
+ move=> Gamma Sigma e1 e2 h bt ef1 a ef2 ef1' ef2' ef ht1 hin hs1 ht2 hin' hs2 hs3 ef' hs'.
  apply ty_massgn with h bt ef1 a ef2 ef1' ef2'. + by apply ht1. + by apply hs1.
  + by apply ht2. + by apply hs2. 
  by have := sub_effect_trans (ef1' ++ ef2' ++ [:: Write h]) ef ef' hs3 hs'.
(* uop *)
+ move=> Gamma Sigma op e ef t ef' hrt hut ht hin hs1 ef'' hs2.
  apply ty_uop with ef. + by apply hrt. + by apply hut. + by apply ht. 
  by have := sub_effect_trans ef ef' ef'' hs1 hs2.
(* bop *)
+ move=> Gamma Sigma op e ef t e' ef' hrt hut ht hin ht' hin' hs1 ef'' hs2.
  apply ty_bop with ef. + by apply hrt. + by apply hut. + by apply ht. + by apply ht'.
  by have := sub_effect_trans ef ef' ef'' hs1 hs2.
(* bind *)
+ move=> Gamma Sigma x t e e' t' ef1 ef2 ef ht hin ht' hin' hs2 ef' hs3.
  apply ty_bind with ef1 ef2. + by apply ht. + by apply ht'.
  by have := sub_effect_trans (ef1 ++ ef2) ef ef' hs2 hs3.
(* cond *)
+ move=> Gamma Sigma e1 e2 e3 tb t ef1 ef2 ef3 ef1' ef ht1 hin1 
         hs1 htb ht2 hin2 hs2 hs3 ht3 hin3 eff hs.
  apply ty_cond with tb ef1 ef2 ef3 ef1' ef. + by apply ht1.
  + by apply hs1. + by apply htb. + by apply ht2. + by apply hs2.
  + by apply ht3. + by apply hs3.
  by have := sub_effect_trans (ef1' ++ ef) ef' ef'' hs4 hs5.
(* unit *)
+ move=> Gamma Sigma ef ht hin _ ef' hs. by apply ty_unit.
(* addr *)
+ move=> Gamma Sigma l ofs h t a ef hsig ht hin _ ef' hs. by apply ty_addr.
(* eapp *)
+ move=> Gamma Sigma exf ts es ef rt ef' ef'' hrt [] h1 h2 hts htes hin hs1 hs2 ef1 hs3.
  apply ty_ext with ef ef'; auto. 
  by have := sub_effect_trans (get_ef_eapp exf ++ ef') ef'' ef1 hs2 hs3.
(* nil *)
+ move=> Gamma Sigma ef ht hin _ efs' hs. by apply ty_nil.
(* cons *)
move=> Gamma Sigma e es ef efs t ts ef' efs' ef'' ht hin hs hts hin' hs1 hs2 efs'' hs3.
apply ty_cons with ef efs ef' efs'; auto. 
by have := sub_effect_trans (ef' ++ efs') ef'' efs'' hs2 hs3.
Qed.*)

(*Section type_expr_ind.
Context (Pts : ty_context -> store_context -> list expr -> effect -> list type -> Prop).
Context (Pt : ty_context -> store_context -> expr -> effect -> type -> Prop).
Context (Htvalu : forall Gamma Sigma ef,
                  Pt Gamma Sigma (Val Vunit (Ptype Tunit)) ef (Ptype Tunit)).
Context (Htvali : forall Gamma Sigma ef i sz s a,
                  Pt Gamma Sigma (Val (Vint i) (Ptype (Tint sz s a))) ef (Ptype (Tint sz s a))).
Context (Htvall : forall Gamma Sigma ef i s a,
                  Pt Gamma Sigma (Val (Vint64 i) (Ptype (Tlong s a))) ef (Ptype (Tlong s a))).
Context (Htvalloc : forall Gamma Sigma ef l ofs h t a,
                    PTree.get l Sigma = Some (Reftype h t a) ->
                    Pt Gamma Sigma (Val (Vloc l ofs) (Reftype h t a)) ef (Reftype h t a)).
Context (Htval : forall Gamma Sigma v ef t,
                 Pt Gamma Sigma (Val v t) ef t).
Context (Htvar : forall Gamma Sigma x t,
                 PTree.get x (extend_context Gamma x t) = Some t ->
                 Pt Gamma Sigma (Var x t) empty_effect t).
Context (Htconti : forall Gamma Sigma t sz s i a,
                   t = (Ptype (Tint sz s a)) ->
                   Pt Gamma Sigma (Const (ConsInt i) t) empty_effect t).
Context (Htcontl : forall Gamma Sigma t s i a,
                   t = (Ptype (Tlong s a)) ->
                   Pt Gamma Sigma (Const (ConsLong i) t) empty_effect t).
Context (Htcontu : forall Gamma Sigma t,
                   t = (Ptype Tunit) ->
                   Pt Gamma Sigma (Const (ConsUnit) t) empty_effect t).
Context (Htapp : forall Gamma Sigma e es rt ef efs ts efs', 
                  Pt Gamma Sigma e ef (Ftype ts efs rt) ->
                  Pts Gamma Sigma es efs' ts ->
                  Pt Gamma Sigma (App e es rt) (ef ++ efs ++ efs') rt).   
Context (Htref : forall Gamma Sigma e ef h bt a, 
                 Pt Gamma Sigma e ef (Ptype bt) ->
                 Pt Gamma Sigma (Prim Ref (e::nil) (Reftype h (Bprim bt) a)) (ef ++ (Alloc h :: nil)) (Reftype h (Bprim bt) a)).
Context (Htderef : forall Gamma Sigma e ef h bt a, 
                   Pt Gamma Sigma e ef (Reftype h (Bprim bt) a) ->
                   Pt Gamma Sigma (Prim Deref (e::nil) (Ptype bt)) (ef ++ (Read h :: nil)) (Ptype bt)).
Context (Htmassgn : forall Gamma Sigma e1 e2 ef1 ef2 h bt a, 
                    Pt Gamma Sigma e1 ef1 (Reftype h (Bprim bt) a) ->
                    Pt Gamma Sigma e2 ef2 (Ptype bt) ->
                    Pt Gamma Sigma (Prim Massgn (e1::e2::nil) (Ptype Tunit)) (ef1 ++ ef2 ++ (Write h :: nil)) (Ptype Tunit)).
Context (Htop : forall Gamma Sigma op e ef t, 
                is_reftype t = false ->
                is_unittype t = false ->
                Pt Gamma Sigma e ef t ->
                Pt Gamma Sigma (Prim (Uop op) (e :: nil) t) ef t).
Context (Htbop : forall Gamma Sigma op e1 e2 ef t, 
                 is_reftype t = false ->
                 is_unittype t = false ->
                 Pt Gamma Sigma e1 ef t ->
                 Pt Gamma Sigma e2 ef t ->
                 Pt Gamma Sigma (Prim (Bop op) (e1 :: e2 :: nil) t) ef t).
Context (Htbind : forall Gamma Sigma x t e e' t' ef ef', 
                  Pt Gamma Sigma e ef t ->
                  Pt (extend_context Gamma x t) Sigma e' ef' t' ->
                  Pt Gamma Sigma (Bind x t e e' t') (ef ++ ef') t').
Context (Htcond : forall Gamma Sigma e1 e2 e3 ef1 ef2 ef3 tb t ef1' ef, 
                  Pt Gamma Sigma e1 ef1 tb ->
                  sub_effect ef1 ef1' ->
                  type_bool tb ->
                  Pt Gamma Sigma e2 ef2 t ->
                  sub_effect ef2 ef = true ->
                  Pt Gamma Sigma e3 ef3 t ->
                  sub_effect ef3 ef = true ->
                  Pt Gamma Sigma (Cond e1 e2 e3 t) (ef1' ++ ef) t).
Context (Htunit : forall Gamma Sigma, 
                  Pt Gamma Sigma (Unit (Ptype Tunit)) empty_effect (Ptype Tunit)).
Context (Htloc : forall Gamma Sigma l ofs h t a, 
                 PTree.get l.(lname) Sigma = Some (Reftype h t a)  ->
                 (*t' = (Reftype h t a) ->*)
                 Pt Gamma Sigma (Addr l ofs (Reftype h t a)) empty_effect (Reftype h t a)). 
Context (Htext :  forall Gamma Sigma exf ts es ef rt,
                  rt = get_rt_eapp exf ->
                  rt <> Ptype Tunit /\ is_funtype rt = false -> 
                  ts = get_at_eapp exf ->
                  Pts Gamma Sigma es ef ts ->
                  Pt Gamma Sigma (Eapp exf ts es rt) ((get_ef_eapp exf) ++ ef) rt).
(*Context (Htheap : forall Gamma Sigma m e h ef t a, 
                  Pt Gamma Sigma e ef (Reftype h (Bprim t) a) ->
                  Pt Gamma Sigma (Hexpr m e (Reftype h (Bprim t) a)) ef (Reftype h (Bprim t) a)).*)
Context (Htnil : forall Gamma Sigma,
                 Pts Gamma Sigma nil nil nil).
Context (Htcons : forall Gamma Sigma e es t ef ts efs,
                  Pt Gamma Sigma e ef t ->
                  Pts Gamma Sigma es efs ts ->
                  Pts Gamma Sigma (e :: es) (ef ++ efs) (t :: ts)).

Lemma type_expr_indP : 
(forall Gamma Sigma es efs ts, type_exprs Gamma Sigma es efs ts -> Pts Gamma Sigma es efs ts) /\
(forall Gamma Sigma e ef t, type_expr Gamma Sigma e ef t -> Pt Gamma Sigma e ef t).
Proof.
apply type_exprs_type_expr_ind_mut=> //=.
(* ConsInt *)
+ move=> Gamma Sigma t sz s a i. by apply Htconti.
(* ConsLong *)
+ move=> Gamma Sigma t s a i ht; subst. by apply Htcontl with s a.
(* App *)
+ move=> Gamma Sigma e es rt efs ts ef efs' ht hi ht' hi'.  
  by apply Htapp with ts.
(* Ref *)
+ move=> Gamma Sigma e ef h bt hte ht hp.
  by apply Htref.
(* Deref *)
+ move=> Gamma Sigma e ef h bt hte ht.
  by apply Htderef.
(* Massgn *)
+ move=> Gamma Sigma e e' h bt ef a ef' hte ht hte' ht'.
  by apply Htmassgn with bt a. 
(* Mop *)
+ move=> Gamma Sigma op e ef t hte hte' ht.
  by apply Htop.
(* Mbop *)
+ move=> Gamma Sigma bop e ef e' hte ht hte' hte'' ht' heq.
  by apply Htbop.
(* Bind *)
+ move=> Gamma Sigma h t e e' t' ef hte ht hte' ht'.
  by apply Htbind.
(* Cond *)
+ move=> Gamma Sigma e1 e2 e3 tb t ef1 ef2 ef3 ef1' ef 
  hte1 ht1 hs1 htb hte2 ht2 hs2 hte3 ht3 hs3. 
  apply Htcond with ef1 ef2 ef3 tb; auto. 
(* Ext *)
+ move=> Gamma Sigma exf ts es ef rt hrt hts tes hts'.
  by apply Htext.
(* Addr *)
(*+ move=> Gamma Sigma l ofs ef. hteq; subst. by apply Htloc.*)
(* Hexpr 
+ move=> Gamma Sigma m e h ef t a hte ht. by apply Htheap.*)
move=> Gamma Sigma e es ef efs t ts hte ht htes hts.
by apply Htcons.
Qed.

End type_expr_ind.*)


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

Lemma type_infer_vunit: forall Gamma Sigma ef t, 
type_expr Gamma Sigma (Val Vunit (Ptype Tunit)) ef t ->
Ptype Tunit = t.
Proof.
move=> Gamma Sigma ef t. 
move eq : (Val Vunit (Ptype Tunit))=> v ht. elim: ht eq=>//=.
Qed.

Lemma type_infer_int: forall Gamma Sigma ef t i sz s a, 
type_expr Gamma Sigma (Val (Vint i) (Ptype (Tint sz s a))) ef t ->
Ptype (Tint sz s a) = t.
Proof.
move=> Gamma Sigma ef t i sz s a. 
move eq : (Val (Vint i) (Ptype (Tint sz s a)))=> v ht. 
elim: ht eq=>//=. by move=> Gamma' Sigma' i' sz' s' a' [] h1 h2 h3 h4; subst.
Qed.

Lemma type_infer_long: forall Gamma Sigma ef t i s a, 
type_expr Gamma Sigma (Val (Vint64 i) (Ptype (Tlong s a))) ef t ->
Ptype (Tlong s a) = t.
Proof.
move=> Gamma Sigma ef t i s a. 
move eq : (Val (Vint64 i) (Ptype (Tlong s a)))=> v ht. 
elim: ht eq=>//=. by move=> Gamma' Sigma' i' s' a' [] h2 h3 h4; subst.
Qed.

Lemma type_infer_loc: forall Gamma Sigma ef t h bt a l ofs, 
type_expr Gamma Sigma (Val (Vloc l ofs) (Reftype h bt a)) ef t ->
(Reftype h bt a) = t.
Proof.
move=> Gamma Sigma ef t h bt a l ofs. 
move eq : (Val (Vloc l ofs) (Reftype h bt a))=> v ht. elim: ht eq=>//=.
by move=> Gamma' Sigma' l' ofs' h' bt' a' hs [] h1 h2 h3 h4 h5; subst. 
Qed.

Lemma type_infer_var : forall Gamma Sigma x t ef t',
type_expr Gamma Sigma (Var x t) ef t' ->
t = t'.
Proof.
move=> Gamma Sigma x t ef t'. 
move eq: (Var x t)=> v ht. elim: ht eq=> //=.
by move=> Gamma' Sigma' x' t'' hxt [] h1 h2; subst.
Qed.

Lemma type_infer_consti: forall Gamma Sigma ef t i sz s a, 
type_expr Gamma Sigma (Const (ConsInt i) (Ptype (Tint sz s a))) ef t ->
Ptype (Tint sz s a) = t.
Proof.
move=> Gamma Sigma ef t i sz s a. 
move eq : (Const (ConsInt i) (Ptype (Tint sz s a)))=> v ht. 
elim: ht eq=>//=. by move=> Gamma' Sigma' i' sz' s' a' [] h1 h2 h3 h4; subst.
Qed.

Lemma type_infer_constl: forall Gamma Sigma ef t i s a, 
type_expr Gamma Sigma (Const (ConsLong i) (Ptype (Tlong s a))) ef t ->
Ptype (Tlong s a) = t.
Proof.
move=> Gamma Sigma ef t i s a. 
move eq : (Const (ConsLong i) (Ptype (Tlong s a)))=> v ht. 
elim: ht eq=>//=. by move=> Gamma' Sigma' i' s' a' [] h2 h3 h4; subst.
Qed.

Lemma type_infer_constu: forall Gamma Sigma ef t, 
type_expr Gamma Sigma (Const ConsUnit (Ptype Tunit)) ef t ->
Ptype Tunit = t.
Proof.
move=> Gamma Sigma ef t. 
move eq : (Const ConsUnit (Ptype Tunit))=> v ht. elim: ht eq=>//=.
Qed.

Lemma type_infer_app: forall Gamma Sigma e es rt ef t,
type_expr Gamma Sigma (App e es rt) ef t ->
t = rt.
Proof.
move=> Gamma Sigma e es rt ef t.
move eq: (App e es rt)=> ve ht. elim: ht eq=> //=.
by move=> Gamma' Sigma' e' es' rt' efs ts ef' efs' ht1 hin ht2 [] h1 h2 h3; subst.
Qed.

Lemma type_infer_ref: forall Gamma Sigma h bt a e ef t,
type_expr Gamma Sigma (Prim Ref [:: e] (Reftype h (Bprim bt) a)) ef t ->
t = (Reftype h (Bprim bt) a).
Proof.
move=> Gamma Sigma h bt a e ef t.
move eq: (Prim Ref [:: e] (Reftype h (Bprim bt) a))=> rv ht.
elim: ht eq=> //=.
by move=> Gamma' Sigma' e' ef' h' bt' a' ht hin [] h1 h2 h3 h4; subst.
Qed.

Lemma type_infer_deref: forall Gamma Sigma bt e ef t,
type_expr Gamma Sigma (Prim Deref [:: e] (Ptype bt)) ef t ->
t = (Ptype bt).
Proof.
move=> Gamma Sigma bt e ef t.
move eq: (Prim Deref [:: e] (Ptype bt))=> rv ht.
elim: ht eq=> //=.
by move=> Gamma' Sigma' e' ef' h bt' a' ht1 hin1 [] h1 h2; subst.
Qed.

Lemma type_infer_massgn: forall Gamma Sigma e e' ef t,
type_expr Gamma Sigma (Prim Massgn [:: e; e'] (Ptype Tunit)) ef t ->
t = (Ptype Tunit). 
Proof.
move=> Gamma Sigma e e' ef t.
move eq: (Prim Massgn [:: e; e'] (Ptype Tunit))=> rv ht.
elim: ht eq=> //=.
Qed.

Lemma type_infer_uop: forall Gamma Sigma e uop t ef' t',
type_expr Gamma Sigma (Prim (Uop uop) [:: e] t) ef' t' ->
t' = t.
Proof.
move=> Gamma Sigma e uop t ef' t'.
move eq: (Prim (Uop uop) [:: e] t)=> rv ht.
elim: ht eq=> //=.
by move=> Gamma' Sigma' op e' ef t'' hrt hut hte' hin [] h1 h2 h3; subst. 
Qed.

Lemma type_infer_bop: forall Gamma Sigma e e' t bop ef t',
type_expr Gamma Sigma (Prim (Bop bop) [:: e; e'] t) ef t' ->
t' = t.
Proof.
move=> Gamma Sigma e e' t bop ef t'.
move eq: (Prim (Bop bop) [:: e; e'] t)=> rv ht.
elim: ht eq=> //=.
by move=> Gamma' Sigma' op e1 ef1 t1 e2 hrt hut ht1 hin1 ht2 hin2
       [] h1 h2 h3 h4; subst. 
Qed.

Lemma type_infer_bind: forall Gamma Sigma e x t e' t' ef t'',
type_expr Gamma Sigma (Bind x t e e' t') ef t'' ->
t'' = t'.
Proof.
move=> Gamma Sigma e x t e' t' ef t''.
move eq:(Bind x t e e' t')=> rv ht. elim: ht eq=> //=.
by move=> Gamma' Sigma' x' t1 e1 e2 t2 ef1 ef' ht1 hin ht2 hin'
       [] h1 h2 h3 h4 h5; subst.
Qed.

Lemma type_infer_cond: forall Gamma Sigma e1 e2 e3 t ef' t',
type_expr Gamma Sigma (Cond e1 e2 e3 t) ef' t' ->
t' = t.
Proof.
move=> Gamma Sigma e1 e2 e3 t ef' t'.
move eq: (Cond e1 e2 e3 t)=> rv ht.
elim: ht eq=> //=.
by move=> Gamma' Sigma' e1' e2' e3' tb t1 ef1 ef2 ht1 hin1 htb
       ht2 hin2 ht3 hin3 [] h1 h2 h3 h4; subst.
Qed.

Lemma type_infer_unit: forall Gamma Sigma ef t,
type_expr Gamma Sigma (Unit (Ptype Tunit)) ef t ->
t = Ptype Tunit.
Proof.
move=> Gamma Sigma ef t. move eq: (Unit (Ptype Tunit))=> rv ht.
by elim: ht eq=> //=.
Qed.

Lemma type_infer_addr: forall Gamma Sigma l ofs h bt a ef t,
type_expr Gamma Sigma (Addr l ofs (Reftype h bt a)) ef t ->
t = (Reftype h bt a).
Proof.
move=> Gamma Sigma l ofs h bt a ef t.
move eq: (Addr l ofs (Reftype h bt a))=> rv ht.
elim: ht eq=> //=.
by move=> Gamma' Sigma' l' ofs' h' t' a' hs [] h1 h2 h3 h4 h5; subst.
Qed.

Lemma type_infer_eapp: forall Gamma Sigma exf es ef t,
type_expr Gamma Sigma (Eapp exf (get_at_eapp exf) es (get_rt_eapp exf)) ef t ->
t = (get_rt_eapp exf).
Proof.
move=> Gamma Sigma exf es ef t. 
move eq: (Eapp exf (get_at_eapp exf) es (get_rt_eapp exf))=> rv ht.
elim: ht eq=> //=.
by move=> Gamma' Sigma' exf' ts es' ef' rt hrt [] hr1 hr2 hts hes' []
       h1 h2 h3 h4; subst.
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
  by have := type_infer_vunit Gamma Sigma ef' t' ht.
+ move=> Gamma Sigma i sz s a ef' t' ht; inversion ht; subst; auto.
  by have := type_infer_int Gamma Sigma ef' t' i sz s a ht.
+ move=> Gamma Sigma i s a ef' t' ht; inversion ht; subst; auto.
  by have := type_infer_long Gamma Sigma ef' t' i s a ht.
+ move=> Gamma Sigma l ofs h t a hs ef' t' ht; inversion ht; subst; auto.
  by have := type_infer_loc Gamma Sigma ef' t' h t a l ofs ht.
+ move=> Gamma Sigma x t ht ef' t' ht'; subst; inversion ht'; subst; auto.
  by have := type_infer_var Gamma Sigma x t ef' t' ht'.
+ move=> Gamma Sigma sz s a i ef' t' ht; subst; inversion ht; subst; auto.
  by have := type_infer_consti Gamma Sigma ef' t' i sz s a ht.
+ move=> Gamma Sigma s a i ef' t' ht; subst; inversion ht; subst; auto.
  by have := type_infer_constl Gamma Sigma ef' t' i s a ht.
+ move=> Gamma Sigma ef' t' ht; inversion ht; subst; auto.
  by have := type_infer_constu Gamma Sigma ef' t' ht.
+ move=> Gamma Sigma e es rt efs ts ef efs' hte hin htes hin' ef' t ht; 
  inversion ht; subst; auto.
  by have := type_infer_app Gamma Sigma e es rt ef' t ht.
+ move=> Gamma Sigma e ef h bt a hte hin ef' t' ht; inversion ht; subst; auto.
  by have := type_infer_ref Gamma Sigma h bt a e ef' t' ht.
+ move=> Gamma Sigma e ef h bt a hte ef' ef'' t' ht; inversion ht; subst; auto.
  by have := type_infer_deref Gamma Sigma bt e ef'' t' ht.
+ move=> Gamma Sigma e e' h bt ef a ef' hte hin hte' hin' ef'' t' ht; subst; auto.
  by have := type_infer_massgn Gamma Sigma e e' ef'' t' ht.
+ move=> Gamma Sigma op e ef t hrt hut hte hin ef' t' ht; inversion ht; subst; auto.
  by have := type_infer_uop Gamma Sigma e op t ef' t' ht.
+ move=> Gamma Sigma op e ef t e' hrt hut hte hin hte' hin' 
  ef' t' ht; inversion ht; subst; auto.
  by have := type_infer_bop Gamma Sigma e e' t op ef' t' ht.
+ move=> Gamma Sigma x t e e' t' ef ef' hte hin hte' hin' ef'' t'' ht; 
  inversion ht; subst; auto.
  by have := type_infer_bind Gamma Sigma e x t e' t' ef'' t'' ht.
+ move=> Gamma Sigma e1 e2 e3 tb t ef1 ef2 hte1 hin1 htb hte2 hin2 hte3 hin3 ef' t'
         ht; inversion ht; subst; auto.
  by have := type_infer_cond Gamma Sigma e1 e2 e3 t ef' t' ht.
+ move=> Gamma Sigma ef' t' ht; inversion ht; subst; auto.
  by have := type_infer_unit Gamma Sigma ef' t' ht.
+ move=> Gamma Sigma l ofs h t a hs ef' t' ht; inversion ht; subst; auto.
  by have := type_infer_addr Gamma Sigma l ofs h t a ef' t' ht.
+ move=> Gamma Sigma exf ts es ef rt hrt [] h1 h2 h3 ht1 hin ef' t' ht; subst;
         inversion ht; subst; auto.
  by have := type_infer_eapp Gamma Sigma exf es ef' t' ht.
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

(* Complete Me *) (* Difficult level *)
Lemma extend_ty_context_deterministic : forall Gamma Sigma x x' t1 t2 e ef t,
(x =? x')%positive = false ->
type_expr (extend_context (extend_context Gamma x t1) x' t2) Sigma e ef t ->
type_expr (extend_context Gamma x t1) Sigma e ef t. 
Proof.
Admitted.

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

(* Not provable due to C treating pointer as int in terms of 
   value stored in memory *)
Lemma wbty_chunk_rel : forall (ty: type) chunk,
access_mode ty = By_value (transl_bchunk_cchunk chunk) ->
(wtype_of_type ty) = (wtypeof_chunk chunk).
Proof.  
move=> ty chunk. case: chunk=> //=; case: ty=> //= p; case: p=> //=.
move=> i s a. case: i=> //=.
+ by case: s=> //=.
case: s=> //=.
Admitted.

(* Not provable due to C treating pointer as int in terms of 
   value stored in memory *)
Lemma cval_bval_type_chunk : forall v chunk v',
Values.Val.has_type v (type_of_chunk (transl_bchunk_cchunk chunk)) ->
transC_val_bplvalue v = Errors.OK v' ->
wtypeof_value v' (wtypeof_chunk chunk). 
Proof.
move=> v chunk v'. case: chunk=> //=; case: v=> //=; case: v'=> //=. 
Admitted.


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

