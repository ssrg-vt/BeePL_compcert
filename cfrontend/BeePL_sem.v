Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep.
Require Import Globalenvs Cop BeePL_aux BeePL_mem BeeTypes BeePL Csyntax.
Require Import Initializersproof Cstrategy BeePL_auxlemmas Coqlib Errors SimplExpr Events.

From mathcomp Require Import all_ssreflect. 

(* How to transform the heap into heap regions *)
(* heap_compcert : (l1 -> v1; l2 -> v2; .... ln -> vn)
heap_koka : ((h1, (l1 -> v1; l2 -> v2; .... ln -> vn);
        (h2, (l1 -> v1; l2 -> v2; .... ln -> vn);
        ..
!(h, e)*) 

Definition is_stateful_expr (e : BeePL.expr) : bool :=
match e with 
| Val e t => true 
| Var x t => false
| Const c t => false
| App e es t => true
| Prim b es t => match b with 
                 | Ref => true 
                 | Deref => true 
                 | Massgn => true 
                 | Uop o => true 
                 | Bop o => true
                 | Run _ => false (* fix me *)
                 end
| Bind x tx e e' t => true 
| Cond e1 e2 e3 t => true 
| Unit t => false
| Addr l ofs t => false
| Hexpr m e t => false (* fix me *)
| BeePL.Eapp ef ts es t => true 
end.

Fixpoint is_stateful_exprs (es : list BeePL.expr) : bool :=
match es with 
| nil => true
| e :: es => is_stateful_expr e && is_stateful_exprs es
end.

Section Big_Step_Semantics.

Variable (ge : genv).

(* Big step semantics without lv, rv, or context *)
Inductive bsem_expr : vmap -> Memory.mem -> BeePL.expr -> Memory.mem -> vmap -> value -> Prop := 
| bsem_value : forall vm m v t,
               well_formed_value v t ->
               bsem_expr vm m (Val v t) m vm v
| bsem_lvar : forall vm m x t l ofs v,
             vm!x = Some (l, t) -> 
             deref_addr ge t m l ofs Full v ->
             bsem_expr vm m (Var x t) m vm v
| bsem_gbvar : forall vm m x t l ofs v,
               vm!x = None ->
               Genv.find_symbol ge x = Some l -> 
               deref_addr ge t m l ofs Full v ->
               bsem_expr vm m (Var x t) m vm v
| bsem_consti : forall vm m i t,
                bsem_expr vm m (Const (ConsInt i) t) m vm (Vint i)
| bsem_constl : forall vm m i t, 
                bsem_expr vm m (Const (ConsLong i) t) m vm (Vint64 i)
| bsem_constu : forall vm m,
                bsem_expr vm m (Const (ConsUnit) (Ptype Tunit)) m vm (Vunit)
| bsem_appr :  forall vm1 vm2 m1 e es t l fd m2 m3 m4 m5 m6 vs rv vm3 vm4 vm5,
               bsem_expr vm1 m1 e m2 vm2 (Vloc l Ptrofs.zero) ->
               Genv.find_funct ge (transBeePL_value_cvalue (Vloc l Ptrofs.zero)) = Some (Internal fd) ->
               BeePL.type_of_fundef (Internal fd) = 
               Ftype (typeof_exprs es) (get_effect_fundef (Internal fd)) (get_rt_fundef (Internal fd)) ->
               list_norepet (fd.(fn_args) ++ fd.(BeePL.fn_vars)) ->
               alloc_variables vm2 m2 (fd.(fn_args) ++ fd.(BeePL.fn_vars)) vm3 m3 -> 
               bsem_exprs vm3 m3 es m4 vm4 vs ->
               typeof_values vs (unzip2 fd.(fn_args)) ->
               bind_variables ge vm4 m4 fd.(fn_args) vs m5  ->
               bsem_expr vm4 m5 fd.(BeePL.fn_body) m6 vm5 rv -> 
               typeof_value rv (get_rt_fundef (Internal fd)) ->
               t = (get_rt_fundef (Internal fd)) ->
               bsem_expr vm1 m1 (App e es t) m6 vm5 rv
| bsem_ref : forall vm m e vm' m' vm'' m'' v fid l ofs g ct g' i' h a t,
             bsem_expr vm m e m' vm' v ->
             transBeePL_type (Ptype t) g = Res ct g' i' ->
             (gensym ct) = ret fid ->
             bind_variables ge vm m ((fid, Ptype t) :: nil) (v :: nil) m' ->
             vm!fid = Some (l, Reftype h (Bprim t) a) -> 
             bsem_expr vm m (Prim Ref [:: e] (Reftype h (Bprim t) a)) m'' vm'' (Vloc l ofs)
| bsem_deref : forall vm m e m' vm' l ofs bf v,
               bsem_expr vm m e m' vm' (Vloc l ofs) ->
               deref_addr ge (typeof_expr e) m l ofs bf v ->
               bsem_expr vm m (Prim Deref (e :: nil) (typeof_expr e)) m' vm' v
| bsem_massgn : forall vm m e1 m' vm' l ofs bf e2 vm'' m'' v v' g1 ct1 ct2 g2 i g3 i',  
                bsem_expr vm m e1 m' vm' (Vloc l ofs) ->
                bsem_expr vm' m' e2 vm'' m'' v ->
                transBeePL_type (typeof_expr e1) g1 = Res ct1 g2 i ->
                transBeePL_type (typeof_expr e2) g2 = Res ct2 g3 i' ->
                sem_cast (transBeePL_value_cvalue v) ct2 ct1 m = Some (transBeePL_value_cvalue v') ->
                assign_addr ge (typeof_expr e1) m l ofs bf v' m' v' -> 
                bsem_expr vm m (Prim Massgn (e1 :: e2 :: nil) (Ptype Tunit)) vm'' m'' Vunit
| bsem_uop : forall vm m e v uop m' vm' v' ct v'' g g' i,
             bsem_expr vm m e m' vm' v ->
             transBeePL_type (typeof_expr e) g = Res ct g' i ->
             sem_unary_operation uop (transBeePL_value_cvalue v) ct m' = Some v' ->
             transC_val_bplvalue v' = OK v'' ->
             bsem_expr vm m (Prim (Uop uop) (e :: nil) (typeof_expr e)) m' vm' v''
| bsem_bop : forall cenv vm m e1 e2 v1 v2 bop vm' m' m'' vm'' v ct1 ct2 v' g g' i g'' i',
             bsem_expr vm m e1 m' vm' v1 ->
             bsem_expr vm' m' e2 m'' vm'' v2 ->
             transBeePL_type (typeof_expr e1) g = Res ct1 g' i ->
             transBeePL_type (typeof_expr e2) g' = Res ct2 g'' i'->
             sem_binary_operation cenv bop (transBeePL_value_cvalue v1) ct1 
                                           (transBeePL_value_cvalue v2) ct2 m'' = Some v ->
             transC_val_bplvalue v = OK v' ->
             bsem_expr vm m (Prim (Bop bop) (e1 :: e2 :: nil) (typeof_expr e1)) m'' vm'' v'
(* fix me : add semantics for run primitive *)
| bsem_bind : forall vm m x e1 vm' m' v e2 e2' v' tx,
              bsem_expr vm m e1 m' vm' v -> 
              subst x (Val v (typeof_expr e1)) e2 = e2' ->
              bsem_expr vm m e2' m' vm' v' ->
              bsem_expr vm m (Bind x tx e1 e2 (typeof_expr e2)) m' vm' v'
| bsem_ctrue : forall vm m e1 e2 e3 t vm' m' vb g ct1 g' i v vm'' m'', 
               bsem_expr vm m e1 m' vm' vb -> 
               transBeePL_type (typeof_expr e1) g = Res ct1 g' i ->
               bool_val (transBeePL_value_cvalue vb) ct1 m' = Some true ->
               bsem_expr vm' m' e2 m'' vm'' v ->
               bsem_expr vm m (Cond e1 e2 e3 t) m'' vm'' v
| bsem_cfalse : forall vm m e1 e2 e3 t vm' m' vb g ct1 g' i v vm'' m'', 
                bsem_expr vm m e1 m' vm' vb -> 
                transBeePL_type (typeof_expr e1) g = Res ct1 g' i ->
                bool_val (transBeePL_value_cvalue vb) ct1 m' = Some false ->
                bsem_expr vm' m' e3 m'' vm'' v ->
                bsem_expr vm m (Cond e1 e2 e3 t) m'' vm'' v
| bsem_ut : forall vm m, 
            bsem_expr vm m (Unit (Ptype Tunit)) m vm Vunit
| bsem_adr : forall vm m l ofs t,
              bsem_expr vm m (Addr l ofs t) m vm (Vloc l.(lname) ofs)
| bsem_eapp : forall vm m es vm' m' m'' vs ef g cef g' i' vres bv ts ty t,
              bsem_exprs vm m es m' vm' vs ->
              befunction_to_cefunction ef g = Res cef g' i' ->
              external_call cef ge (transBeePL_values_cvalues vs) m' t vres m'' ->
              transC_val_bplvalue vres = OK bv ->
              bsem_expr vm m (BeePL.Eapp ef ts es ty) m'' vm' bv
(* fix me : add semantics for hexpr *)
with bsem_exprs : vmap -> Memory.mem -> list BeePL.expr -> Memory.mem -> vmap -> list value -> Prop :=
| bsem_nil : forall vm m,
             bsem_exprs vm m nil m vm nil
| bsem_cons : forall vm m m' m'' v vs e es vm' vm'',
              bsem_expr vm m e m' vm' v ->
              bsem_exprs vm' m' es m'' vm'' vs ->
              bsem_exprs vm m (e :: es) m'' vm'' (v :: vs). 

Scheme bsem_expr_ind_mut := Induction for bsem_expr Sort Prop
  with bsem_exprs_ind_mut := Induction for bsem_exprs Sort Prop.
Combined Scheme bsem_exprs_bsem_expr_ind_mut from bsem_exprs_ind_mut, bsem_expr_ind_mut.

Section bsem_expr_ind.
Context (Pbs : vmap -> Memory.mem -> list BeePL.expr -> Memory.mem -> vmap -> list value -> Prop).
Context (Pb : vmap -> Memory.mem -> BeePL.expr -> Memory.mem -> vmap -> value -> Prop).
Context (Hbvalue : forall vm m v t, 
                 well_formed_value v t -> 
                 Pb vm m (Val v t) m vm v).
Context (Hblvar : forall vm m x t l ofs v,
                 vm!x = Some (l, t) -> 
                 deref_addr ge t m l ofs Full v ->
                 Pb vm m (Var x t) m vm v).
Context (Hbgbvar : forall vm m x t l ofs v,
                 vm!x = None ->
                 Genv.find_symbol ge x = Some l -> 
                 deref_addr ge t m l ofs Full v ->
                 Pb vm m (Var x t) m vm v).
Context (Hbconsti : forall vm m i t,
                  Pb vm m (Const (ConsInt i) t) m vm (Vint i)).
Context (Hbconstl : forall vm m i t, 
                  Pb vm m (Const (ConsLong i) t) m vm (Vint64 i)).
Context (Hbconstu : forall vm m,
                  Pb vm m (Const (ConsUnit) (Ptype Tunit)) m vm (Vunit)).
Context (Hbappr : forall vm1 vm2 m1 e es t l fd m2 m3 m4 m5 m6 vs rv vm3 vm4 vm5,
                  Pb vm1 m1 e m2 vm2 (Vloc l Ptrofs.zero) ->
                  Genv.find_funct ge (transBeePL_value_cvalue (Vloc l Ptrofs.zero)) = Some (Internal fd) ->
                  BeePL.type_of_fundef (Internal fd) = 
                  Ftype (typeof_exprs es) (get_effect_fundef (Internal fd)) (get_rt_fundef (Internal fd)) ->
                  list_norepet (fd.(fn_args) ++ fd.(BeePL.fn_vars)) ->
                  alloc_variables vm2 m2 (fd.(fn_args) ++ fd.(BeePL.fn_vars)) vm3 m3 -> 
                  Pbs vm3 m3 es m4 vm4 vs ->
                  typeof_values vs (unzip2 fd.(fn_args)) ->
                  bind_variables ge vm4 m4 fd.(fn_args) vs m5  ->
                  Pb vm4 m5 fd.(BeePL.fn_body) m6 vm5 rv -> 
                  typeof_value rv (get_rt_fundef (Internal fd)) ->
                  t = (get_rt_fundef (Internal fd)) ->
                  Pb vm1 m1 (App e es t) m6 vm5 rv).
Context (Hbref : forall vm m e vm' m' vm'' m'' v fid l ofs g ct g' i' h a t,
                 Pb vm m e m' vm' v ->
                 transBeePL_type (Ptype t) g = Res ct g' i' ->
                 (gensym ct) = ret fid ->
                 bind_variables ge vm m ((fid, Ptype t) :: nil) (v :: nil) m' ->
                 vm!fid = Some (l, Reftype h (Bprim t) a) ->
                 Pb vm m (Prim Ref [:: e] (Reftype h (Bprim t) a)) m'' vm'' (Vloc l ofs)).
Context (Hbderef : forall vm m e m' vm' l ofs bf v,
                   Pb vm m e m' vm' (Vloc l ofs) ->
                   deref_addr ge (typeof_expr e) m l ofs bf v ->
                   Pb vm m (Prim Deref (e :: nil) (typeof_expr e)) m' vm' v).
Context (Hbmassgn : forall vm m e1 m' vm' l ofs bf e2 vm'' m'' v v' g1 ct1 ct2 g2 i g3 i',  
                   Pb vm m e1 m' vm' (Vloc l ofs) ->
                   Pb vm' m' e2 vm'' m'' v ->
                   transBeePL_type (typeof_expr e1) g1 = Res ct1 g2 i ->
                   transBeePL_type (typeof_expr e2) g2 = Res ct2 g3 i' ->
                   sem_cast (transBeePL_value_cvalue v) ct2 ct1 m = Some (transBeePL_value_cvalue v') ->
                   assign_addr ge (typeof_expr e1) m l ofs bf v' m' v' ->
                   Pb vm m (Prim Massgn (e1 :: e2 :: nil) (Ptype Tunit)) vm'' m'' Vunit).
Context (Hbuop : forall vm m e v uop m' vm' v' ct v'' g g' i,
                Pb vm m e m' vm' v ->
                transBeePL_type (typeof_expr e) g = Res ct g' i ->
                sem_unary_operation uop (transBeePL_value_cvalue v) ct m' = Some v' ->
                transC_val_bplvalue v' = OK v'' ->
                Pb vm m (Prim (Uop uop) (e :: nil) (typeof_expr e)) m' vm' v'').
Context (Hbbop : forall cenv vm m e1 e2 v1 v2 bop vm' m' m'' vm'' v ct1 ct2 v' g g' i g'' i',
                Pb vm m e1 m' vm' v1 ->
                Pb vm' m' e2 m'' vm'' v2 ->
                transBeePL_type (typeof_expr e1) g = Res ct1 g' i ->
                transBeePL_type (typeof_expr e2) g' = Res ct2 g'' i'->
                sem_binary_operation cenv bop (transBeePL_value_cvalue v1) ct1 
                                              (transBeePL_value_cvalue v2) ct2 m'' = Some v ->
                transC_val_bplvalue v = OK v' ->
                Pb vm m (Prim (Bop bop) (e1 :: e2 :: nil) (typeof_expr e1)) m'' vm'' v').
Context (Hbbind : forall vm m x e1 vm' m' v  e2 e2' v' tx,
                 Pb vm m e1 m' vm' v -> 
                 subst x (Val v (typeof_expr e1)) e2 = e2' ->
                 Pb vm m e2' m' vm' v' ->
                 Pb vm m (Bind x tx e1 e2 (typeof_expr e2)) m' vm' v').
Context (Hbctrue : forall vm m e1 e2 e3 t vm' m' vb g ct1 g' i v vm'' m'', 
                  Pb vm m e1 m' vm' vb -> 
                  transBeePL_type (typeof_expr e1) g = Res ct1 g' i ->
                  bool_val (transBeePL_value_cvalue vb) ct1 m' = Some true ->
                  Pb vm' m' e2 m'' vm'' v ->
                  Pb vm m (Cond e1 e2 e3 t) m'' vm'' v).
Context (Hbcfalse : forall vm m e1 e2 e3 t vm' m' vb g ct1 g' i v vm'' m'', 
                   Pb vm m e1 m' vm' vb -> 
                   transBeePL_type (typeof_expr e1) g = Res ct1 g' i ->
                   bool_val (transBeePL_value_cvalue vb) ct1 m' = Some false ->
                   Pb vm' m' e3 m'' vm'' v ->
                   Pb vm m (Cond e1 e2 e3 t) m'' vm'' v).
Context (Hbut : forall vm m, 
                Pb vm m (Unit (Ptype Tunit)) m vm Vunit).
Context (Hbadr : forall vm m l ofs t,
                 Pb vm m (Addr l ofs t) m vm (Vloc l.(lname) ofs)).
Context (Hbeapp : forall vm m es vm' m' m'' vs ef g cef g' i' vres bv ts ty t,
                   Pbs vm m es m' vm' vs ->
                   befuntion_to_cefunction ef g = Res cef g' i' ->
                   external_call cef ge (transBeePL_values_cvalues vs) m' t vres m'' ->
                   transC_val_bplvalue vres = OK bv ->
                   Pb vm m (BeePL.Eapp ef ts es ty) m'' vm' bv).
Context (Hbnil : forall vm m,
                 Pbs vm m nil m vm nil).
Context (Hbcons : forall vm m m' m'' v vs e es vm' vm'',
                  Pb vm m e m' vm' v ->
                  Pbs vm' m' es m'' vm'' vs ->
                  Pbs vm m (e :: es) m'' vm'' (v :: vs)).

Lemma bsem_expr_indP :
  (forall vm m es m' vm' vs, bsem_exprs vm m es m' vm' vs -> Pbs vm m es m' vm' vs) /\
  (forall vm m e m' vm' v, bsem_expr vm m e m' vm' v -> Pb vm m e m' vm' v).
Proof.
  apply bsem_exprs_bsem_expr_ind_mut; eauto.
Qed.

End bsem_expr_ind.

End Big_Step_Semantics.

Definition extract_value_expr (e : BeePL.expr) : list value :=
match e with 
| Val v t => [:: v]
| _ => nil
end.

Fixpoint extract_values_exprs (es : list BeePL.expr) : list value := 
match es with 
| nil => nil
| e :: es => extract_value_expr e ++ extract_values_exprs es 
end.

Section Small_Step_Semantics.

Variable (ge : genv).

Inductive ssem_expr : vmap -> Memory.mem -> BeePL.expr -> Memory.mem -> vmap -> BeePL.expr -> Prop :=
| ssem_value : forall vm m v t,
               well_formed_value v t ->
               ssem_expr vm m (Val v t) m vm (Val v t)
| ssem_lvar : forall vm m x t l ofs v,
              vm!x = Some (l, t) -> 
              deref_addr ge t m l ofs Full v ->
              is_vloc v = false ->
              ssem_expr vm m (Var x t) m vm (Val v t)
| ssem_gbvar : forall vm m x t l ofs v,
               vm!x = None ->
               Genv.find_symbol ge x = Some l -> 
               deref_addr ge t m l ofs Full v ->
               is_vloc v = false ->
               ssem_expr vm m (Var x t) m vm (Val v t)
| ssem_consti : forall vm m i t,
                ssem_expr vm m (Const (ConsInt i) t) m vm (Val (Vint i) t)
| ssem_constl : forall vm m i t, 
                ssem_expr vm m (Const (ConsLong i) t) m vm (Val (Vint64 i) t)
| ssem_constu : forall vm m,
                ssem_expr vm m (Const (ConsUnit) (Ptype Tunit)) m vm (Val (Vunit) (Ptype Tunit))
| ssem_app1 : forall vm1 m1 e es t e' m2 vm2,
              ssem_expr vm1 m1 e m2 vm2 e' ->
              ssem_expr vm1 m1 (App e es t) m2 vm2 (App e' es t)
| ssem_app2 : forall vm1 vm2 m1 es t l fd m2 m3 m4 vs vm3,
              Genv.find_funct ge (transBeePL_value_cvalue (Vloc l Ptrofs.zero)) = Some (Internal fd) ->
              BeePL.type_of_fundef (Internal fd) = 
              Ftype (typeof_exprs es) (get_effect_fundef (Internal fd)) (get_rt_fundef (Internal fd)) ->
              t = get_rt_fundef (Internal fd) ->
              list_norepet (fd.(fn_args) ++ fd.(BeePL.fn_vars)) ->
              alloc_variables vm1 m1 (fd.(fn_args) ++ fd.(BeePL.fn_vars)) vm2 m2 -> 
              ssem_exprs vm2 m2 es m3 vm3 vs ->
              typeof_exprs vs = (unzip2 fd.(fn_args)) ->
              bind_variables ge vm3 m3 fd.(fn_args) (extract_values_exprs vs) m4  ->
              ssem_expr vm1 m1 (App (Val (Vloc l Ptrofs.zero) (Ftype (typeof_exprs es) 
                                                                     (get_effect_fundef (Internal fd)) 
                                                                     (get_rt_fundef (Internal fd)))) es t) m2 vm2
                               fd.(BeePL.fn_body)
| ssem_ref1 : forall vm m e m' vm' e' h t a,
              ssem_expr vm m e m' vm' e' ->
              ssem_expr vm m (Prim Ref [:: e] (Reftype h (Bprim t) a)) m' vm' 
                             (Prim Ref [:: e'] (Reftype h (Bprim t) a))
| ssem_ref2 : forall vm m vm' m' vm'' m'' v fid l ofs t g ct g' i' h a,
              transBeePL_type (Ptype t) g = Res ct g' i' ->
              (gensym ct) = ret fid ->
              bind_variables ge vm m ((fid, Ptype t) :: nil) (v :: nil) m' ->
              ssem_expr vm' m' (Var fid (Ptype t)) m'' vm'' (Val (Vloc l ofs) (Reftype h (Bprim t) a)) -> 
              ssem_expr vm m (Prim Ref [:: (Val v (Ptype t))] (Reftype h (Bprim t) a)) m'' vm'' 
              (*(Hexpr m'' (Val (Vloc l ofs) (Reftype h (Bprim t) a)) (Reftype h (Bprim t) a))*)
                             (Val (Vloc l ofs) (Reftype h (Bprim t) a))
| ssem_deref1 : forall vm m e t m' vm' e',
                ssem_expr vm m e m' vm' e' ->
                ssem_expr vm m (Prim Deref (e :: nil) (Ptype t)) m' vm' 
                               (Prim Deref (e' :: nil) (Ptype t))
| ssem_deref2 : forall vm m l ofs bf v h a t,
                deref_addr ge (Ptype t) m l ofs bf v ->
                is_vloc v = false ->
                ssem_expr vm m (Prim Deref [:: (Val (Vloc l ofs) (Reftype h (Bprim t) a))] (Ptype t)) m vm 
                               (Val v (Ptype t))
| ssem_massgn1 : forall vm m e1 e2 m' vm' e1',  
                 ssem_expr vm m e1 m' vm' e1' ->
                 ssem_expr vm m (Prim Massgn (e1 :: e2 :: nil) (Ptype Tunit)) m' vm' 
                                (Prim Massgn (e1' :: e2 :: nil) (Ptype Tunit))
| ssem_massgn2 : forall vm m e2 e2' m' vm' l ofs h a t,  
                 ssem_expr vm m e2  m' vm' e2' ->
                 ssem_expr vm m (Prim Massgn ((Val (Vloc l ofs) (Reftype h (Bprim t) a)) :: e2 :: nil) (Ptype Tunit)) m' vm' 
                                (Prim Massgn ((Val (Vloc l ofs) (Reftype h (Bprim t) a)) :: e2' :: nil) (Ptype Tunit))
| ssem_massgn3 : forall vm m t m' l ofs bf v h a,  
                 assign_addr ge (Ptype t) m l ofs bf v m' v -> 
                 is_vloc v = false ->
                 ssem_expr vm m (Prim Massgn ((Val (Vloc l ofs) (Reftype h (Bprim t) a)) ::  Val v (Ptype t):: nil) (Ptype Tunit)) 
                                m' vm (Val Vunit (Ptype Tunit))
| ssem_uop1 : forall vm m e e' uop m' vm',
              ssem_expr vm m e m' vm' e' ->
              ssem_expr vm m (Prim (Uop uop) (e :: nil) (typeof_expr e)) m' vm' 
                             (Prim (Uop uop) (e' :: nil) (typeof_expr e))
| ssem_uop2 : forall vm m t v uop v' ct v'' g g' i,
             transBeePL_type t g = Res ct g' i ->
             sem_unary_operation uop (transBeePL_value_cvalue v) ct m = Some v' ->
             transC_val_bplvalue v' = OK v'' ->
             ssem_expr vm m (Prim (Uop uop) [:: (Val v t)] t) m vm (Val v'' t)
| ssem_bop1 : forall vm m vm' m' bop e1 e2 e1',
              ssem_expr vm m e1 m' vm' e1' ->
              ssem_expr vm m (Prim (Bop bop) (e1 :: e2 :: nil) (typeof_expr e1)) m' vm' 
                             (Prim (Bop bop) (e1' :: e2 :: nil) (typeof_expr e1))
| ssem_bop2 : forall vm m vm' m' bop v1 t1 e2 e2',
              ssem_expr vm m e2 m' vm' e2' ->
              ssem_expr vm m (Prim (Bop bop) (Val v1 t1 :: e2 :: nil) t1) m' vm' 
                             (Prim (Bop bop) (Val v1 t1 :: e2' :: nil) t1)
| ssem_bop3 : forall cenv vm m v1 v2 bop t v ct v' g g' i,
              transBeePL_type t g = Res ct g' i ->
              sem_binary_operation cenv bop (transBeePL_value_cvalue v1) ct 
                                            (transBeePL_value_cvalue v2) ct m = Some v ->
              transC_val_bplvalue v = OK v' ->
              ssem_expr vm m (Prim (Bop bop) (Val v1 t :: Val v2 t :: nil) t) m vm (Val v' t)
(* fix me : add semantics for run primitive *)
| ssem_bind1 : forall vm m x e1 e1' e2 vm' m' tx,
               ssem_expr vm m e1 m' vm' e1' -> 
               ssem_expr vm m (Bind x tx e1 e2 (typeof_expr e2)) m' vm' 
                              (Bind x tx e1' e2 (typeof_expr e2)) 
| ssem_bind2 : forall vm m x v1 e2 tx,
               ssem_expr vm m (Bind x tx (Val v1 tx) e2 (typeof_expr e2)) m vm (subst x (Val v1 tx) e2)  
| ssem_cond : forall vm m e1 e2 e3 vm' m' e1', 
              ssem_expr vm m e1 m' vm' e1' -> 
              ssem_expr vm m (Cond e1 e2 e3 (typeof_expr e2)) m' vm' (Cond e1' e2 e3 (typeof_expr e2))
| ssem_ctrue : forall vm m v1 e2 e3 t1 g ct1 g' i, 
               transBeePL_type t1 g = Res ct1 g' i ->
               bool_val (transBeePL_value_cvalue v1) ct1 m = Some true ->
               ssem_expr vm m (Cond (Val v1 t1) e2 e3 (typeof_expr e2)) m vm e2
| ssem_cfalse : forall vm m v1 e2 e3 t1 g ct1 g' i, 
                transBeePL_type t1 g = Res ct1 g' i ->
                bool_val (transBeePL_value_cvalue v1) ct1 m = Some false ->
                ssem_expr vm m (Cond (Val v1 t1) e2 e3 (typeof_expr e2)) m vm e3
| ssem_ut : forall vm m, 
            ssem_expr vm m (Unit (Ptype Tunit)) m vm (Val Vunit (Ptype Tunit))
| ssem_adr : forall vm m l ofs h t a,
             ssem_expr vm m (Addr l ofs (Reftype h t a)) m vm (Val (Vloc l.(lname) ofs) (Reftype h t a))
| ssem_hexpr1 : forall vm m e m' vm' e' t,
                ssem_expr vm m e m' vm' e' ->
                ssem_expr vm m (Hexpr m e t) m' vm' (Hexpr m e' t)
(* fix me : hexpr m, l should take step to ?? *)
| ssem_hexpr2 : forall vm m h bt a l ofs t,
                ssem_expr vm m (Hexpr m (Val (Vloc l ofs) (Reftype h (Bprim bt) a)) t) m vm (Val (Vloc l ofs) (Reftype h (Bprim bt) a))
| ssem_eapp : forall vm m es vm' m' m'' vs ef g cef g' i' vres bv ts ty t,
              ssem_exprs vm m es m' vm' vs ->
              befunction_to_cefunction ef g = Res cef g' i' ->
              external_call cef ge (transBeePL_values_cvalues (extract_values_exprs vs)) m' t vres m'' ->
              transC_val_bplvalue vres = OK bv ->
              ssem_expr vm m (BeePL.Eapp ef ts es ty) m'' vm' (Val bv ty)
with ssem_exprs : vmap -> Memory.mem -> list BeePL.expr -> Memory.mem -> vmap -> list BeePL.expr -> Prop :=
| ssem_nil : forall vm m,
             ssem_exprs vm m nil m vm nil
| ssem_cons1 : forall vm m m' e e' es vm',
              ssem_expr vm m e m' vm' e' ->
              ssem_exprs vm m (e :: es) m' vm' (e' :: es)
| ssem_cons2 : forall vm m es m' vm' v t vs,
               ssem_exprs vm m es m' vm' vs ->
               ssem_exprs vm m (Val v t :: es) m' vm' (Val v t :: vs). 

Scheme ssem_expr_ind_mut := Induction for ssem_expr Sort Prop
  with ssem_exprs_ind_mut := Induction for ssem_exprs Sort Prop.
Combined Scheme ssem_exprs_ssem_expr_ind_mut from ssem_exprs_ind_mut, ssem_expr_ind_mut.

Section ssem_expr_ind.
Context (Pss : vmap -> Memory.mem -> list BeePL.expr -> Memory.mem -> vmap -> list BeePL.expr -> Prop).
Context (Ps : vmap -> Memory.mem -> BeePL.expr -> Memory.mem -> vmap -> BeePL.expr -> Prop).
Context (Hsvalue : forall vm m v t, 
                 well_formed_value v t -> 
                 Ps vm m (Val v t) m vm (Val v t)).
Context (Hslvar : forall vm m x t l ofs v,
                 vm!x = Some (l, t) -> 
                 deref_addr ge t m l ofs Full v ->
                 Ps vm m (Var x t) m vm (Val v t)).
Context (Hsgbvar : forall vm m x t l ofs v,
                 vm!x = None ->
                 Genv.find_symbol ge x = Some l -> 
                 deref_addr ge t m l ofs Full v ->
                 Ps vm m (Var x t) m vm (Val v t)).
Context (Hsconsti : forall vm m i t,
                  Ps vm m (Const (ConsInt i) t) m vm (Val (Vint i) t)).
Context (Hsconstl : forall vm m i t, 
                  Ps vm m (Const (ConsLong i) t) m vm (Val (Vint64 i) t)).
Context (Hsconstu : forall vm m,
                  Ps vm m (Const (ConsUnit) (Ptype Tunit)) m vm (Val Vunit (Ptype Tunit))).
Context (Hsapp1 : forall vm1 m1 e es t e' m2 vm2,
                  Ps vm1 m1 e m2 vm2 e' ->
                  Ps vm1 m1 (App e es t) m2 vm2 (App e' es t)).
Context (Hsapp2 : forall vm1 vm2 m1 es t l fd m2 m3 m4 vs vm3,
                  Genv.find_funct ge (transBeePL_value_cvalue (Vloc l Ptrofs.zero)) = Some (Internal fd) ->
                  BeePL.type_of_fundef (Internal fd) = 
                  Ftype (typeof_exprs es) (get_effect_fundef (Internal fd)) (get_rt_fundef (Internal fd)) ->
                  t = get_rt_fundef (Internal fd) ->
                  list_norepet (fd.(fn_args) ++ fd.(BeePL.fn_vars)) ->
                  alloc_variables vm1 m1 (fd.(fn_args) ++ fd.(BeePL.fn_vars)) vm2 m2 -> 
                  Pss vm2 m2 es m3 vm3 vs ->
                  typeof_exprs vs = (unzip2 fd.(fn_args)) ->
                  bind_variables ge vm3 m3 fd.(fn_args) (extract_values_exprs vs) m4  ->
                  Ps vm1 m1 (App (Val (Vloc l Ptrofs.zero) (Ftype (typeof_exprs es) 
                                                                     (get_effect_fundef (Internal fd)) 
                                                                     (get_rt_fundef (Internal fd)))) es t) m2 vm2
                               fd.(BeePL.fn_body)).
Context (Hsref1 : forall vm m e m' vm' e' h t a,
                 Ps vm m e m' vm' e' ->
                 Ps vm m (Prim Ref [:: e] (Reftype h (Bprim t) a)) m' vm' 
                                (Prim Ref [:: e'] (Reftype h (Bprim t) a))).
Context (Hsref2 : forall vm m vm' m' vm'' m'' v fid l ofs t g ct g' i' h a,
                 transBeePL_type (Ptype t) g = Res ct g' i' ->
                 (gensym ct) = ret fid ->
                 bind_variables ge vm m ((fid, Ptype t) :: nil) (v :: nil) m' ->
                 Ps vm' m' (Var fid (Ptype t)) m'' vm'' (Val (Vloc l ofs) (Reftype h (Bprim t) a)) ->
                 Ps vm m (Prim Ref [:: (Val v (Ptype t))] (Reftype h (Bprim t) a)) m'' vm'' 
                               (Val (Vloc l ofs) (Reftype h (Bprim t) a))).
Context (Hsderef1 : forall vm m e t m' vm' e',
                   Ps vm m e m' vm' e' ->
                   Ps vm m (Prim Deref (e :: nil) (Ptype t)) m' vm' 
                                  (Prim Deref (e' :: nil) (Ptype t))).
Context (Hsderef2 : forall vm m m' vm' l ofs bf v h a t,
                   deref_addr ge (Ptype t) m l ofs bf v ->
                   Ps vm m (Prim Deref [:: (Val (Vloc l ofs) (Reftype h (Bprim t) a))] (Ptype t)) m' vm' 
                                  (Val v (Ptype t))).
Context (Hsmassgn1 : forall vm m e1 e2 m' vm' e1',  
                    Ps vm m e1 m' vm' e1' ->
                    Ps vm m (Prim Massgn (e1 :: e2 :: nil) (Ptype Tunit)) m' vm' 
                                   (Prim Massgn (e1' :: e2 :: nil) (Ptype Tunit))).
Context (Hsmassgn2 : forall vm m e2 e2' m' vm' l ofs h a t,  
                    Ps vm m e2  m' vm' e2' ->
                    Ps vm m (Prim Massgn ((Val (Vloc l ofs) (Reftype h (Bprim t) a)) :: e2 :: nil) (Ptype Tunit)) m' vm' 
                                   (Prim Massgn ((Val (Vloc l ofs) (Reftype h (Bprim t) a)) :: e2' :: nil) (Ptype Tunit))).
Context (Hsmassgn3 : forall vm m t m' l ofs bf v h a,  
                    assign_addr ge (Ptype t) m l ofs bf v m' v -> 
                    Ps vm m (Prim Massgn ((Val (Vloc l ofs) (Reftype h (Bprim t) a)) ::  Val v (Ptype t):: nil) (Ptype Tunit)) 
                                    m' vm (Val Vunit (Ptype Tunit))).
Context (Hsuop1 : forall vm m e e' uop m' vm',
                 Ps vm m e m' vm' e' ->
                 Ps vm m (Prim (Uop uop) (e :: nil) (typeof_expr e)) m' vm' 
                                (Prim (Uop uop) (e' :: nil) (typeof_expr e))).
Context (Hsuop2 : forall vm m t v uop m' vm' v' ct v'' g g' i,
                 transBeePL_type t g = Res ct g' i ->
                 sem_unary_operation uop (transBeePL_value_cvalue v) ct m' = Some v' ->
                 transC_val_bplvalue v' = OK v'' ->
                 Ps vm m (Prim (Uop uop) [:: (Val v t)] t) m' vm' (Val v'' t)).
Context (Hsbop1 : forall vm m vm' m' bop e1 e2 e1',
                 Ps vm m e1 m' vm' e1' ->
                 Ps vm m (Prim (Bop bop) (e1 :: e2 :: nil) (typeof_expr e1)) m' vm' 
                                (Prim (Bop bop) (e1' :: e2 :: nil) (typeof_expr e1))).
Context (Hsbop2 : forall vm m vm' m' bop v1 t1 e2 e2',
                 Ps vm m e2 m' vm' e2' ->
                 Ps vm m (Prim (Bop bop) (Val v1 t1 :: e2 :: nil) t1) m' vm' 
                                (Prim (Bop bop) (Val v1 t1 :: e2' :: nil) t1)).
Context (Hsbop3 : forall cenv vm m v1 v2 bop t v ct v' g g' i,
              transBeePL_type t g = Res ct g' i ->
              sem_binary_operation cenv bop (transBeePL_value_cvalue v1) ct 
                                            (transBeePL_value_cvalue v2) ct m = Some v ->
              transC_val_bplvalue v = OK v' ->
              Ps vm m (Prim (Bop bop) (Val v1 t :: Val v2 t :: nil) t) m vm (Val v' t)).
Context (Hsbind1 : forall vm m x e1 e1' e2 vm' m' tx,
                 Ps vm m e1 m' vm' e1' -> 
                 Ps vm m (Bind x tx e1 e2 (typeof_expr e2)) m' vm' 
                         (Bind x tx e1' e2 (typeof_expr e2))).
Context (Hsbind2 : forall vm m x v1 e2 tx,
                   Ps vm m (Bind x tx (Val v1 tx) e2 (typeof_expr e2)) m vm (subst x (Val v1 tx) e2)).
Context (Hscond : forall vm m e1 e2 e3 vm' m' e1',
                  Ps vm m e1 m' vm' e1' -> 
                  Ps vm m (Cond e1 e2 e3 (typeof_expr e2)) m' vm' (Cond e1' e2 e3 (typeof_expr e2))).
Context (Hsctrue : forall vm m v1 e2 e3 t1 g ct1 g' i, 
                  transBeePL_type t1 g = Res ct1 g' i ->
                  bool_val (transBeePL_value_cvalue v1) ct1 m = Some true ->
                  Ps vm m (Cond (Val v1 t1) e2 e3 (typeof_expr e2)) m vm e2).
Context (Hscfalse : forall vm m v1 e2 e3 t1 g ct1 g' i, 
                   transBeePL_type t1 g = Res ct1 g' i ->
                   bool_val (transBeePL_value_cvalue v1) ct1 m = Some false ->
                   Ps vm m (Cond (Val v1 t1) e2 e3 (typeof_expr e2)) m vm e3).
Context (Hsut : forall vm m, 
               Ps vm m (Unit (Ptype Tunit)) m vm (Val Vunit (Ptype Tunit))).
Context (Hsadr : forall vm m l ofs t,
                Ps vm m (Addr l ofs t) m vm (Val (Vloc l.(lname) ofs) t)).
Context (Hshexpr1 : forall vm m e m' vm' e' t,
                 Ps vm m e m' vm' e' ->
                 Ps vm m (Hexpr m e t) m' vm' (Hexpr m e' t)).
Context (Hshexpr2 : forall vm m h bt a l ofs t,
                 Ps vm m (Hexpr m (Val (Vloc l ofs) (Reftype h (Bprim bt) a)) t) m vm (Val (Vloc l ofs) (Reftype h (Bprim bt) a))).
Context (Hseapp : forall vm m es vm' m' m'' vs ef g cef g' i' vres bv ts ty t,
                  Pss vm m es m' vm' vs ->
                  befuntion_to_cefunction ef g = Res cef g' i' ->
                  external_call cef ge (transBeePL_values_cvalues (extract_values_exprs vs)) m' t vres m'' ->
                  transC_val_bplvalue vres = OK bv ->
                  Ps vm m (BeePL.Eapp ef ts es ty) m'' vm' (Val bv ty)).
Context (Hsnil : forall vm m,
                 Pss vm m nil m vm nil).
Context (Hscons1 : forall vm m m' e e' es vm',
                   Ps vm m e m' vm' e' ->
                   Pss vm m (e :: es) m' vm' (e' :: es)).
Context (Hscons2 : forall vm m es m' vm' v t vs,
                   Pss vm m es m' vm' vs ->
                   Pss vm m (Val v t :: es) m' vm' (Val v t :: vs)).

Lemma ssem_expr_indP :
  (forall vm m es m' vm' vs, ssem_exprs vm m es m' vm' vs -> Pss vm m es m' vm' vs) /\
  (forall vm m e m' vm' v, ssem_expr vm m e m' vm' v -> Ps vm m e m' vm' v).
Proof.
  apply ssem_exprs_ssem_expr_ind_mut; eauto.
Qed.
End ssem_expr_ind.

End Small_Step_Semantics.

Definition is_value (e : BeePL.expr) : bool :=
match e with 
| Val _ _ => true 
| _ => false
end.

Fixpoint is_values (es : list BeePL.expr) : bool :=
match es with 
| nil => true
| e :: es => is_value e && is_values es
end.

(** An expr is safe if it cannot get stuck by doing any transition - 
    Either it reaches a value or it takes step **)
Definition bsafe_expr (bge : genv) (e : BeePL.expr) : Prop :=
forall v vm m vm' m', bsem_expr bge vm m e vm' m' v.

Definition ssafe_expr (bge : genv) (vm : vmap) (m : Memory.mem) (e : BeePL.expr) : Prop :=
is_value e \/ exists m' vm' e', ssem_expr bge vm m e m' vm' e'.


Inductive ssem_closure : genv -> vmap -> Memory.mem -> BeePL.expr -> nat -> 
                         Memory.mem -> vmap -> BeePL.expr -> Prop :=
| ssem_one : forall bge vm m e m' vm' e',
             ssem_expr bge vm m e m' vm' e' ->
             ssem_closure bge vm m e 1%nat m' vm' e'
| ssem_multi : forall bge vm m e m' vm' e' n vm'' m'' e'',
               ssem_expr bge vm m e m' vm' e' ->
               ssem_closure bge vm' m' e' n m'' vm'' e'' ->
               ssem_closure bge vm m e (n + 1) %nat m'' vm'' e''
with ssem_closures : genv -> vmap -> Memory.mem -> list BeePL.expr -> nat ->
                     Memory.mem -> vmap -> list BeePL.expr -> Prop :=
| ssems_one : forall bge vm m e m' vm' e',
              ssem_exprs bge vm m e m' vm' e' ->
              ssem_closures bge vm m e 1%nat m' vm' e'
| ssems_multi : forall bge vm m e m' vm' e' n vm'' m'' e'',
                ssem_exprs bge vm m e m' vm' e' ->
                ssem_closures bge vm' m' e' n m'' vm'' e'' ->
                ssem_closures bge vm m e (n + 1)%nat m'' vm'' e''.

          
