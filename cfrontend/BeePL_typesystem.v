Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Coqlib.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL BeePL_auxlemmas.
From mathcomp Require Import all_ssreflect. 

Definition empty_effect : effect := nil. 

Inductive type_expr : ty_context -> store_context -> expr -> effect -> type -> Prop :=
| Ty_var : forall Gamma Sigma x t, 
           get_ty (extend_context Gamma x.(vname) t) x.(vname) = Some t ->
           x.(vtype) = t ->
           type_expr Gamma Sigma (Var x) empty_effect t
| Ty_constint : forall Gamma Sigma t sz s i,
                t = (Ptype (Tint sz s)) ->
                type_expr Gamma Sigma (Const (ConsInt i) t) empty_effect t
| Ty_constbool : forall Gamma Sigma t b,
                 t = (Ptype Tbool) ->
                 type_expr Gamma Sigma (Const (ConsBool b) t) empty_effect t
| Ty_constunit : forall Gamma Sigma t,
                t = (Ptype Tunit) ->
                type_expr Gamma Sigma (Const (ConsUnit) t) empty_effect t
| Ty_appr : forall Gamma Sigma r e es h bt rt ef efs ts, 
            get_ty Gamma r.(vname) = Some rt ->
            type_expr Gamma Sigma (Var r) empty_effect rt -> 
            type_expr Gamma Sigma e ef (Reftype h bt) ->      (* fix me: it should be a pointer type 
                                                                         but the value it points to must be an arrow type 
                                                                         and we restrict ref to have only basic type *)
            type_exprs Gamma Sigma es efs ts -> 
            type_expr Gamma Sigma (App (Some r.(vname)) e es rt) (ef ++ efs) rt
| Ty_app : forall Gamma Sigma e es h bt rt ef ts, 
           type_expr Gamma Sigma e ef (Reftype h bt) -> 
           type_exprs Gamma Sigma es ef ts -> 
           type_expr Gamma Sigma (App None e es rt) ef rt
| Ty_prim_ref : forall Gamma Sigma e ef h bt, 
                type_expr Gamma Sigma e ef (Ptype bt) ->
                type_expr Gamma Sigma (Prim Ref (e::nil) (Reftype h (Bprim bt))) (ef ++ (Alloc h :: nil)) (Reftype h (Bprim bt))
| Ty_prim_deref : forall Gamma Sigma e ef h bt, (* inner expression should be unrestricted as it will be used later *)
                  type_expr Gamma Sigma e ef (Reftype h (Bprim bt)) -> 
                  type_expr Gamma Sigma (Prim Deref (e::nil) (Ptype bt)) (ef ++ (Read h :: nil)) (Ptype bt)
| Ty_prim_massgn : forall Gamma Sigma e e' h bt ef,
                   type_expr Gamma Sigma e ef (Reftype h (Bprim bt)) ->
                   type_expr Gamma Sigma e' ef (Ptype bt) ->
                   type_expr Gamma Sigma (Prim Massgn (e::e'::nil) (Ptype Tunit)) (ef ++ (Alloc h :: nil)) (Ptype Tunit)
| Ty_prim_uop : forall Gamma Sigma op e ef t,
                type_expr Gamma Sigma e ef t ->
                type_expr Gamma Sigma (Prim (Uop op) (e::nil) t) ef t 
| Ty_prim_bop : forall Gamma Sigma op e ef t tr e',
                type_expr Gamma Sigma e ef t ->
                type_expr Gamma Sigma e' ef t ->
                eq_type tr (if is_not_comparison op then t else (Ptype Tbool)) ->
                type_expr Gamma Sigma (Prim (Bop op) (e::e'::nil) tr) ef tr 
| Ty_bind : forall Gamma Sigma x t e e' t' ef,
            type_expr Gamma Sigma e ef t ->
            type_expr (extend_context Gamma x t) Sigma e' ef t' ->
            type_expr Gamma Sigma (Bind x t e e' t') ef t'
| Ty_cond : forall Gamma Sigma e1 e2 e3 t ef,
            type_expr Gamma Sigma e1 ef (Ptype Tbool) ->
            type_expr Gamma Sigma e2 ef t ->
            type_expr Gamma Sigma e3 ef t ->
            type_expr Gamma Sigma (Cond e1 e2 e3 t) ef t
| Ty_loc : forall Gamma Sigma l h bt,
           get_sty Sigma l.(lname) = Some (Reftype h bt)  ->
           l.(ltype) = (Reftype h bt) ->
           type_expr Gamma Sigma (Addr l) empty_effect (Reftype h bt) 
with type_exprs : ty_context -> store_context -> list expr -> effect -> list type -> Prop :=
| Ty_nil : forall Gamma Sigma,
           type_exprs Gamma Sigma nil nil nil
| Ty_cons : forall Gamma Sigma e es ef efs t ts,
            type_expr Gamma Sigma e ef t ->
            type_exprs Gamma Sigma es efs ts ->
            type_exprs Gamma Sigma (e :: es) (ef ++ efs) (t :: ts).
           
Scheme type_expr_ind_mut := Induction for type_expr Sort Prop
  with type_exprs_ind_mut := Induction for type_exprs Sort Prop.
Combined Scheme type_exprs_type_expr_ind_mut from type_exprs_ind_mut, type_expr_ind_mut.

Lemma type_exprsE : forall Gamma Sigma es efs ts,
type_exprs Gamma Sigma es efs ts ->
match es with 
| [::] => efs = [::] /\ ts = [::]
| e1 :: es1 => exists ef1 t1 efs1 ts1,
               type_expr Gamma Sigma e1 ef1 t1 /\  
               type_exprs Gamma Sigma es1 efs1 ts1 /\
               es = e1 :: es1 /\ efs = ef1 ++ efs1 /\ ts = t1 :: ts1
end.
Proof.
move=> Gamma Sigma es efs ts hs. elim: es hs=> //=.
+ by move=> hs; inversion hs.
move=> e es ih hs; inversion hs; subst.
by exists ef, t, efs0, ts0; split=> //=.
Qed.      

Section type_expr_ind.
Context (Pts : ty_context -> store_context -> list expr -> effect -> list type -> Prop).
Context (Pt : ty_context -> store_context -> expr -> effect -> type -> Prop).
Context (Htvar : forall Gamma Sigma x t,
                 get_ty (extend_context Gamma x.(vname) t) x.(vname) = Some t ->
                 x.(vtype) = t ->
                 Pt Gamma Sigma (Var x) empty_effect t).
Context (Htconti : forall Gamma Sigma t sz s i,
                   t = (Ptype (Tint sz s)) ->
                   Pt Gamma Sigma (Const (ConsInt i) t) empty_effect t).
Context (Htcontb : forall Gamma Sigma t b,
                   t = (Ptype Tbool) ->
                   Pt Gamma Sigma (Const (ConsBool b) t) empty_effect t).
Context (Htcontu : forall Gamma Sigma t,
                   t = (Ptype Tunit) ->
                   Pt Gamma Sigma (Const (ConsUnit) t) empty_effect t).
Context (Htappr : forall Gamma Sigma r e es h bt rt ef efs ts, 
                  get_ty Gamma r.(vname) = Some rt ->
                  Pt Gamma Sigma (Var r) empty_effect rt ->
                  Pt Gamma Sigma e ef (Reftype h bt) ->
                  Pts Gamma Sigma es efs ts ->
                  Pt Gamma Sigma (App (Some r.(vname)) e es rt) (ef ++ efs) rt).
Context (Htapp : forall Gamma Sigma e es ef h bt rt ts,
                 Pt Gamma Sigma e ef (Reftype h bt) ->
                 Pts Gamma Sigma es ef ts ->
                 Pt Gamma Sigma (App None e es rt) ef rt).      
Context (Htref : forall Gamma Sigma e ef h bt, 
                 Pt Gamma Sigma e ef (Ptype bt) -> 
                 Pt Gamma Sigma (Prim Ref (e::nil) (Reftype h (Bprim bt))) (ef ++ (Alloc h :: nil)) (Reftype h (Bprim bt))).
Context (Htderef : forall Gamma Sigma e ef h bt, 
                   Pt Gamma Sigma e ef (Reftype h (Bprim bt)) ->
                   Pt Gamma Sigma (Prim Deref (e::nil) (Ptype bt)) (ef ++ (Read h :: nil)) (Ptype bt)).
Context (Htmassgn : forall Gamma Sigma e1 e2 ef h bt, 
                    Pt Gamma Sigma e1 ef (Reftype h (Bprim bt)) ->
                    Pt Gamma Sigma e2 ef (Ptype bt) ->
                    Pt Gamma Sigma (Prim Massgn (e1::e2::nil) (Ptype Tunit)) (ef ++ (Alloc h :: nil)) (Ptype Tunit)).
Context (Htop : forall Gamma Sigma op e ef t, 
                Pt Gamma Sigma e ef t ->
                Pt Gamma Sigma (Prim (Uop op) (e :: nil) t) ef t).
Context (Htbop : forall Gamma Sigma op e1 e2 ef t tr, 
                 Pt Gamma Sigma e1 ef t ->
                 Pt Gamma Sigma e2 ef t ->
                 eq_type tr (if is_not_comparison op then t else (Ptype Tbool)) ->
                 Pt Gamma Sigma (Prim (Bop op) (e1 :: e2 :: nil) tr) ef tr).
Context (Htbind : forall Gamma Sigma x t e e' t' ef, 
                  Pt Gamma Sigma e ef t ->
                  Pt (extend_context Gamma x t) Sigma e' ef t' ->
                  Pt Gamma Sigma (Bind x t e e' t') ef t').
Context (Htcond : forall Gamma Sigma e1 e2 e3 ef t, 
                  Pt Gamma Sigma e1 ef (Ptype Tbool) -> 
                  Pt Gamma Sigma e2 ef t -> 
                  Pt Gamma Sigma e3 ef t -> 
                  Pt Gamma Sigma (Cond e1 e2 e3 t) ef t).
Context (Htloc : forall Gamma Sigma l h bt, 
                 get_sty Sigma l.(lname) = Some (Reftype h bt) ->
                 l.(ltype) = (Reftype h bt) ->
                 Pt Gamma Sigma (Addr l) empty_effect (Reftype h bt)). 
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
(* Appr *)
+ move=> Gamma Sigma r e es h bt et e' efs ts hg ht hi ht' hi' hes hts.
  by apply Htappr with h bt ts.
(* App *)
+ move=> Gamma Sigma e es h bt rt ef ts hte ht htes hts.
  by apply Htapp with h bt ts.
(* Ref *)
+ move=> Gamma Sigma e ef h bt hte ht.
  by apply Htref.
(* Deref *)
+ move=> Gamma Sigma e ef h bt hte ht.
  by apply Htderef.
(* Massgn *)
+ move=> Gamma Sigma e e' h bt ef hte ht hte' ht'.
  by apply Htmassgn with bt.
(* Mop *)
+ move=> Gamma Sigma op e ef t hte ht.
  by apply Htop.
(* Mbop *)
+ move=> Gamma Sigma bop e ef t tr e' hte ht hte' ht' heq.
  by apply Htbop with t.
(* Bind *)
+ move=> Gamma Sigma h t e e' t' ef hte ht hte' ht'.
  by apply Htbind.
(* Cond *)
+ move=> Gamma Sigma e1 e2 e3 t ef hte1 ht1 hte2 ht2 hte3 ht3.
  by apply Htcond.
move=> Gamma Sigma e es ef efs t ts hte ht htes hts.
by apply Htcons.
Qed.

End type_expr_ind.

Section type_expr_eq_ind.
Context (Pts : ty_context -> store_context -> list expr -> effect -> list type -> Prop).
Context (Pt : ty_context -> store_context -> expr -> effect -> type -> Prop).
Context (Ets : list type -> list type -> Prop).
Context (Et : type -> type -> Prop).
Context (Hvar : forall Gamma Sigma x t t',
                get_ty (extend_context Gamma x.(vname) t) x.(vname) = Some t ->
                x.(vtype) = t ->
                Pt Gamma Sigma (Var x) empty_effect t ->
                get_ty (extend_context Gamma x.(vname) t') x.(vname) = Some t' ->
                x.(vtype) = t' ->
                Pt Gamma Sigma (Var x) empty_effect t' ->
                Et t t').
Context (Htconti : forall Gamma Sigma t sz s i t',
                   t = (Ptype (Tint sz s)) ->
                   Pt Gamma Sigma (Const (ConsInt i) t) empty_effect t ->
                   t' = (Ptype (Tint sz s)) ->
                   Pt Gamma Sigma (Const (ConsInt i) t) empty_effect t' ->
                   Et t t').
Context (Htcontb : forall Gamma Sigma t sz s b t',
                   t = (Ptype (Tint sz s)) ->
                   Pt Gamma Sigma (Const (ConsBool b) t) empty_effect t ->
                   t' = (Ptype (Tint sz s)) ->
                   Pt Gamma Sigma (Const (ConsBool b) t) empty_effect t' ->
                   Et t t').
Context (Htcontu : forall Gamma Sigma t sz s t',
                   t = (Ptype (Tint sz s)) ->
                   Pt Gamma Sigma (Const (ConsUnit) t) empty_effect t ->
                   t' = (Ptype (Tint sz s)) ->
                   Pt Gamma Sigma (Const (ConsUnit) t) empty_effect t' ->
                   Et t t').
Context (Htappr : forall Gamma Sigma r e es h bt rt ef efs ts rt' h' bt' ts' ef' efs', 
                  get_ty Gamma r.(vname) = Some rt ->
                  Pt Gamma Sigma (Var r) empty_effect rt ->
                  Pt Gamma Sigma e ef (Reftype h bt) ->
                  Pts Gamma Sigma es efs ts ->
                  Pt Gamma Sigma (App (Some r.(vname)) e es rt) (ef ++ efs) rt ->
                  get_ty Gamma r.(vname) = Some rt' ->
                  Pt Gamma Sigma (Var r) empty_effect rt' ->
                  Pt Gamma Sigma e ef' (Reftype h' bt') ->
                  Pts Gamma Sigma es efs' ts' ->
                  Pt Gamma Sigma (App (Some r.(vname)) e es rt') (ef' ++ efs') rt').
Context (Htapp : forall Gamma Sigma e es ef h bt rt ts ef' h' bt' ts' rt',
                 Pt Gamma Sigma e ef (Reftype h bt) ->
                 Pts Gamma Sigma es ef ts ->
                 Pt Gamma Sigma e ef' (Reftype h' bt') ->
                 Et (Reftype h bt) (Reftype h bt) ->
                 Pts Gamma Sigma es ef' ts' ->
                 Ets ts ts' ->
                 Pt Gamma Sigma (App None e es rt) ef rt ->
                 Pt Gamma Sigma (App None e es rt') ef rt' ->
                 Et rt rt').      
Context (Htref : forall Gamma Sigma e ef h bt h' bt' ef', 
                 Pt Gamma Sigma e ef (Ptype bt) ->
                 Pt Gamma Sigma e ef' (Ptype bt') -> 
                 Et (Ptype bt) (Ptype bt') ->
                 Pt Gamma Sigma (Prim Ref (e::nil) (Reftype h (Bprim bt))) (ef ++ (Alloc h :: nil)) (Reftype h (Bprim bt)) -> 
                 Pt Gamma Sigma (Prim Ref (e::nil) (Reftype h' (Bprim bt'))) (ef' ++ (Alloc h' :: nil)) (Reftype h' (Bprim bt')) ->
                 Et (Reftype h (Bprim bt)) (Reftype h' (Bprim bt'))).
Context (Htderef : forall Gamma Sigma e ef h bt ef' h' bt', 
                   Pt Gamma Sigma e ef (Reftype h (Bprim bt)) ->
                   Pt Gamma Sigma e ef' (Reftype h' (Bprim bt')) ->
                   Et (Reftype h (Bprim bt)) (Reftype h' (Bprim bt')) ->
                   Pt Gamma Sigma (Prim Deref (e::nil) (Ptype bt)) (ef ++ (Read h :: nil)) (Ptype bt) -> 
                   Pt Gamma Sigma (Prim Deref (e::nil) (Ptype bt')) (ef' ++ (Read h' :: nil)) (Ptype bt') ->
                   Et (Ptype bt) (Ptype bt')).
Context (Htmassgn : forall Gamma Sigma e1 e2 ef h bt h' bt' ef', 
                    Pt Gamma Sigma e1 ef (Reftype h (Bprim bt)) ->
                    Pt Gamma Sigma e1 ef' (Reftype h' (Bprim bt')) ->
                    Et (Reftype h (Bprim bt)) (Reftype h' (Bprim bt')) ->
                    Pt Gamma Sigma e2 ef (Ptype bt) ->
                    Pt Gamma Sigma e2 ef' (Ptype bt') ->
                    Et (Ptype bt) (Ptype bt') ->
                    Pt Gamma Sigma (Prim Massgn (e1::e2::nil) (Ptype Tunit)) (ef' ++ (Alloc h' :: nil)) (Ptype Tunit) ->
                    Pt Gamma Sigma (Prim Massgn (e1::e2::nil) (Ptype Tunit)) (ef' ++ (Alloc h' :: nil)) (Ptype Tunit) ->
                    Et (Ptype Tunit) (Ptype Tunit)).
Context (Htop : forall Gamma Sigma op e ef t ef' t', 
                Pt Gamma Sigma e ef t ->
                Pt Gamma Sigma e ef' t' ->
                Et t t' ->
                Pt Gamma Sigma (Prim (Uop op) (e :: nil) t) ef t ->
                Pt Gamma Sigma (Prim (Uop op) (e :: nil) t') ef' t' ->
                Et t t').
Context (Htbop : forall Gamma Sigma op e1 e2 ef t tr ef' t' tr', 
                 Pt Gamma Sigma e1 ef t ->
                 Pt Gamma Sigma e1 ef' t' ->
                 Pt Gamma Sigma e2 ef t ->
                 Pt Gamma Sigma e2 ef' t' ->
                 Et t t' ->
                 eq_type tr (if is_not_comparison op then t else (Ptype Tbool)) ->
                 eq_type tr (if is_not_comparison op then t' else (Ptype Tbool)) ->
                 Pt Gamma Sigma (Prim (Bop op) (e1 :: e2 :: nil) tr) ef tr ->
                 Pt Gamma Sigma (Prim (Bop op) (e1 :: e2 :: nil) tr') ef tr' ->
                 Et tr tr').
Context (Htbind : forall Gamma Sigma x t e e' t' ef ef' t'' t''', 
                  Pt Gamma Sigma e ef t ->
                  Pt Gamma Sigma e ef' t' ->
                  Et t t' ->
                  Pt (extend_context Gamma x t) Sigma e' ef t'' ->
                  Pt (extend_context Gamma x t') Sigma e' ef' t''' ->
                  Pt Gamma Sigma (Bind x t e e' t'') ef t'' ->
                  Pt Gamma Sigma (Bind x t e e' t''') ef' t''' ->
                  Et t'' t''').
Context (Htcond : forall Gamma Sigma e1 e2 e3 ef t ef' t', 
                  Pt Gamma Sigma e1 ef (Ptype Tbool) -> 
                  Pt Gamma Sigma e1 ef' (Ptype Tbool) ->
                  Pt Gamma Sigma e2 ef t ->
                  Pt Gamma Sigma e2 ef' t' ->
                  Pt Gamma Sigma e3 ef t -> 
                  Pt Gamma Sigma e3 ef' t' ->
                  Pt Gamma Sigma (Cond e1 e2 e3 t') ef' t' ->
                  Et t t').
Context (Htloc : forall Gamma Sigma l h bt h' bt', 
                 get_sty Sigma l.(lname) = Some (Reftype h bt) ->
                 get_sty Sigma l.(lname) = Some (Reftype h' bt') ->
                 l.(ltype) = (Reftype h bt) ->
                 l.(ltype) = (Reftype h' bt') ->
                 Pt Gamma Sigma (Addr l) empty_effect (Reftype h bt) ->
                 Pt Gamma Sigma (Addr l) empty_effect (Reftype h' bt') ->
                 Et (Reftype h bt) (Reftype h' bt')). 
Context (Htnil : forall Gamma Sigma,
                 Pts Gamma Sigma nil nil nil ->
                 Ets nil nil).
Context (Htcons : forall Gamma Sigma e es t ef ts efs ef' t' ts' efs',
                  Pt Gamma Sigma e ef t ->
                  Pt Gamma Sigma e ef' t' ->
                  Et t t' ->
                  Pts Gamma Sigma es efs ts ->
                  Pts Gamma Sigma es efs' ts' ->
                  Ets ts ts' ->
                  Pts Gamma Sigma (e :: es) (ef ++ efs) (t :: ts) ->
                  Pts Gamma Sigma (e :: es) (ef ++ efs) (t' :: ts') ->
                  Ets (t :: ts) (t' :: ts')).

Lemma type_expr_indP' : 
(forall Gamma Sigma es efs ts efs' ts', type_exprs Gamma Sigma es efs ts -> 
                                        Pts Gamma Sigma es efs ts ->
                                        type_exprs Gamma Sigma es efs' ts' ->
                                        Pts Gamma Sigma es efs' ts'-> 
                                        Ets ts ts') /\
(forall Gamma Sigma e ef t ef' t', type_expr Gamma Sigma e ef t -> 
                                   Pt Gamma Sigma e ef t ->
                                   type_expr Gamma Sigma e ef' t' -> 
                                   Pt Gamma Sigma e ef' t' ->
                                   Et t t').
Proof.
Admitted.

End type_expr_eq_ind.

Lemma type_expr_exprs_eq: 
(forall Gamma Sigma es efs ts efs' ts', type_exprs Gamma Sigma es efs ts ->
                                        type_exprs Gamma Sigma es efs' ts' ->
                                        ts = ts') /\
(forall Gamma Sigma e ef t ef' t', type_expr Gamma Sigma e ef t ->
                                   type_expr Gamma Sigma e ef' t' ->
                                   t = t').
Proof.
Admitted.

(**** Supoorting lemmas ****)
Lemma type_rel_typeof : forall Gamma Sigma e ef t,
type_expr Gamma Sigma e ef t ->
typeof_expr e = match e with 
                | Prim (Bop op) es t => (if (is_not_comparison op) then t else (Ptype Tbool)) 
                | _ => t
                end.
Proof.
move=> Gamma Sigma e ef t ht; inversion ht; subst; rewrite /typeof_expr /=; auto.
case: ifP=> //= ho. move: H1. rewrite ho /=. case: t ht=> //= p. by case: p=> //=.
Qed.

Lemma sem_binary_notcmp_type_val1: forall Gamma Sigma bop v1 v2 e1 e2 v ef t1, 
sem_binary_operation bop v1 v2 (typeof_expr e1) (typeof_expr e2) = some v ->
type_expr Gamma Sigma e1 ef t1 ->
is_not_comparison bop = true ->
typeof_value v t1.
Proof.
Admitted.

Lemma sem_binary_notcmp_type_val2: forall Gamma Sigma bop v1 v2 e1 e2 v ef t2, 
sem_binary_operation bop v1 v2 (typeof_expr e1) (typeof_expr e2) = some v ->
type_expr Gamma Sigma e2 ef t2 ->
is_not_comparison bop = true ->
typeof_value v t2.
Proof.
Admitted.

Lemma sem_binary_cmp_type_val: forall Gamma Sigma bop v1 v2 e1 e2 v ef t1, 
sem_binary_operation bop v1 v2 (typeof_expr e1) (typeof_expr e2) = some v ->
type_expr Gamma Sigma e1 ef t1 ->
is_not_comparison bop = false ->
typeof_value v (Ptype Tbool).
Proof.
Admitted.

Lemma type_reflex : forall v t t' v',
typeof_value v t ->
typeof_value v t' ->
typeof_value v' t ->
typeof_value v' t'.
Proof.
move=> v t t' v'. rewrite /typeof_value /=.
case: v=> //=.
+ case: t=> //= p. case: p=> //=.
  case: t'=> //= p'. by case: p'=> //=.
+ case: t=> //= p. case: p=> //=.
  case: t'=> //= p. by case: p=> //=.
+ case: t=> //= p. case: p=> //=.
  case: t'=> //= p. by case: p=> //=.
case: t=> //= i b. case: b=> //= p l hl; subst.
by case: t'=> //= i' b hl'; subst. 
Qed.

Lemma eq_type_rel : forall v t t',
eq_type t t' ->
typeof_value v t' ->
typeof_value v t.
Proof.
move=> v t t'. case: t'=> //=.
+ case: t=> //= p p'. case: p=> //=.
  + by case: p'=> //=.
  + by case: p'=> //=.
  by case: p'=> //=.
+ move=> i b. by case: t=> //= i' b' /andP [] hi ht hv. 
move=> es e t'. by case: t=> //=.
Qed.

Lemma get_val_var_ty : forall st x v,
get_val_var (vmem st) x = Some v ->
typeof_value v (vtype x).
Proof.
move=> [] /= h vm x v. elim: vm=> //=.
move=> [] xi xv xs ih /=. 
case hxeq: (eq_vinfo x xi && valid_value_var_dec x xv)=>//= [] [] hv; subst.
move: hxeq. move=> /andP [] h1 h2. by case: valid_value_var_dec h2=> //=.
Qed.

(**** Substitution preserves typing ****)
(* Substitution preserve typing says that suppose we
   have an expression [e] with a free variable [x], and suppose we've been
   able to assign a type [t'] to [e] under the assumption that [x] has
   some type [t].  Also, suppose that we have some other term [e'] and
   that we've shown that [e'] has type [t].  Then, since [e'] satisfies
   the assumption we made about [x] when typing [e], we should be
   able to substitute [e'] for each of the occurrences of [x] in [e]
   and obtain a new expression that still has type [t]. *)
Lemma subst_preservation : forall Gamma Sigma x t e' e ef t', 
type_expr (extend_context Gamma x.(vname) t) Sigma e ef t' ->
type_expr Gamma Sigma e' ef t ->
type_expr Gamma Sigma (subst x.(vname) e' e) ef t'.
Proof.
Admitted.

Lemma extend_ty_context_deterministic : forall Gamma Sigma x x' t1 t2 e ef t,
(x =? x')%positive = false ->
type_expr (extend_context (extend_context Gamma x t1) x' t2) Sigma e ef t ->
type_expr (extend_context Gamma x t1) Sigma e ef t. 
Proof.
Admitted.

Lemma subst_typing : forall Gamma Sigma genv x e e' ef t st st' v,
type_expr Gamma Sigma (subst x e e') ef t ->
sem_expr genv st (subst x e e') st' v ->
typeof_value v t.
Proof.
Admitted.


(**** Preservation ****)
Lemma preservation : forall Gamma Sigma genv e ef t st st' v, 
type_expr Gamma Sigma e ef t ->
sem_expr genv st e st' v ->
typeof_value v t.
Proof.
move=> Gamma Sigma genv e ef t st st' v ht he. move: st st' v he.
induction ht.
+ move=> st st' v he; inversion he; subst.
  by have := get_val_var_ty st' x v H4.
(* Const int *)
+ by move=> st st' v he; inversion he; subst; rewrite /typeof_value.
(* Const bool *)
+ by move=> st st' v he; inversion he; subst; rewrite /typeof_value.
(* Const unit *)
+ by move=> st st' v he; inversion he; subst; rewrite /typeof_value.
(* App with return *) 
+ admit.
(* App with no return *)
+ admit.
(* Ref *)
+ move=> st st' v he; inversion he; subst. by rewrite /typeof_value /=.
(* Deref *)
+ move=> st st' v he; inversion he; subst.
  by move: (IHht st st' (Vloc l) H1)=> hvt.
(* Massgn *)
+ move=> st st' v he; inversion he; subst. by rewrite /typeof_value.
(* Uop *)
+ move=> st st' v he. inversion he; subst.
  have [h1 h2] := sem_unary_operation_val_type op v0 (typeof_expr e) v H7.
  move: (IHht st st' v0 H6)=> hv0t.
  have := type_rel_typeof Gamma Sigma e ef t ht. case: e ht IHht he H6 H7 h1 h2=> //=.
  + by move=> v1 ht IHht he H6 H7 h1 h2 <-.
  + by move=> c t0 ht IHht he H6 H7 h1 h2 <-.
  + by move=> o e es t0 ht IHht he H6 H7 h1 h2 <-.
  move=> b es t0 ht IHht he H6 H7 h1 h2. case: b ht IHht he H6=> //=.
  + by move=> ht IHht he H6 <-.
  + by move=> ht IHht he H6 <-.
  + by move=> ht IHht he H6 <-.
  + by move=> uop ht IHht he H6 <-.
  + move=> b ht IHht he H6 heq; subst. rewrite heq /= in h2.
    move: h2. case: ifP=> //= hc hv. + by have := type_reflex v0 t0 t v h1 hv0t hv. 
    rewrite hc in heq; subst. by have := type_reflex v0 (Ptype Tbool) t v h1 hv0t hv.
  + by move=> h ht IHht he H6 <-.
  + by move=> i t0 e e' t1 ht IHht he H6 ho h1 h2 <-.
  + by move=> e e1 e2 t' ht IHht he H6 ho h1 h2 <-.
  + by move=> l ht IHht he H6 ho h1 h2 <-.
  by move=> h e t' ht IHht he H6 ho h1 h2 <-.
(* Bop *)
+ move=> st st' v he; inversion he; subst.
  move: (IHht1 st st' v1 H8)=> hvt1.
  move: (IHht2 st' st'' v2 H9)=> hvt2.
  move: H. case: ifP=> //= hc.
  + have ht :=  sem_binary_operation_val_type1 op v1 v2 (typeof_expr e) (typeof_expr e') v H10.
    move=> heq. have htv1' := eq_type_rel v1 tr t heq hvt1. rewrite hc in ht.
    have hvt := sem_binary_notcmp_type_val1 Gamma Sigma op v1 v2 e e' v ef t H10 ht1 hc. 
    by have := eq_type_rel v tr t heq hvt.
  move=> heq. have hvt := sem_binary_cmp_type_val Gamma Sigma op v1 v2 e e' v ef t H10 ht1 hc. 
  by have := eq_type_rel v tr (Ptype Tbool) heq hvt.
(* Bind *)
+ move=> st st' v he. have /= hs := subst_preservation Gamma Sigma {| vname := x; vtype := t |} t e e' ef t' ht2 ht1.
  inversion he; subst. by have := subst_typing Gamma Sigma genv x e e' ef t' st'0 st' v hs H9.
(* Cond *)
+ move=> st st' v he; inversion he; subst.
  + by move: (IHht2 st'0 st' v H8).
  by move: (IHht3 st'0 st' v H8).
(* Addr *)
move=> st st' v he; inversion he; subst.
rewrite /typeof_value /=. by case: bt H H0=> //= p.
Admitted.
 
   

    
    
