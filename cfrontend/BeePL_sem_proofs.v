Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep.
Require Import Globalenvs Cop BeePL_aux BeePL_mem BeeTypes BeePL Csyntax.
Require Import Initializersproof Cstrategy BeePL_auxlemmas Coqlib Errors SimplExpr Events.

From mathcomp Require Import all_ssreflect. 

Section Big_Step_Semantics.

Variable (ge : genv).

(* Big step semantics without lv, rv, or context *)
Inductive bsem_expr : vmap -> Memory.mem -> BeePL.expr -> Memory.mem -> vmap -> value -> Prop := 
| bsem_value : forall vm m v t,
               bsem_expr vm m (Val v t) m vm v
| bsem_lvar : forall vm m x t l ofs h a v,
             vm!(x.(vname)) = Some (l, Reftype h (Bprim t) a) -> 
             deref_addr ge x.(vtype) m l ofs Full v ->
             bsem_expr vm m (Var x) m vm v
| bsem_gbvar : forall vm m x l ofs v,
               vm!(x.(vname)) = None ->
               Genv.find_symbol ge x.(vname) = Some l -> 
               deref_addr ge x.(vtype) m l ofs Full v ->
               bsem_expr vm m (Var x) m vm v
| bsem_consti : forall vm m i t,
                bsem_expr vm m (Const (ConsInt i) t) m vm (Vint i)
| bsem_constl : forall vm m i t, 
                bsem_expr vm m (Const (ConsLong i) t) m vm (Vint64 i)
| bsem_constu : forall vm m,
                bsem_expr vm m (Const (ConsUnit) (Ptype Tunit)) m vm (Vunit)
| bsem_appr : forall vm1 vm2 m1 e es t l fd m2 m3 m4 m5 m6 vs rv vm3 vm4 vm5,
              bsem_expr vm1 m1 e m2 vm2 (Vloc l Ptrofs.zero) ->
              Genv.find_funct ge (transBeePL_value_cvalue (Vloc l Ptrofs.zero)) = Some (Internal fd) ->
              BeePL.type_of_fundef (Internal fd) = 
              Ftype (typeof_exprs es) (get_effect_fundef (Internal fd)) (get_rt_fundef (Internal fd)) ->
              list_norepet (fd.(fn_args) ++ fd.(BeePL.fn_vars)) ->
              alloc_variables vm2 m2 (fd.(fn_args) ++ fd.(BeePL.fn_vars)) vm3 m3 -> 
              bsem_exprs vm3 m3 es m4 vm4 vs ->
              typeof_values vs (wtypes_of_types (extract_types_vinfos fd.(fn_args))) ->
              bind_variables ge vm4 m4 fd.(fn_args) vs m5  ->
              bsem_expr vm4 m5 fd.(BeePL.fn_body) m6 vm5 rv -> 
              bsem_expr vm1 m1 (App e es t) m6 vm5 rv
| bsem_ref : forall vm m e vm' m' vm'' m'' v fid l ofs t g ct g' i',
             bsem_expr vm m e m' vm' v ->
             transBeePL_type t g = Res ct g' i' ->
             (gensym ct) = ret fid ->
             bind_variables ge vm m ({| vname := fid; vtype := t|} :: nil) (v :: nil) m' ->
             bsem_expr vm' m' (Var {| vname := fid; vtype := t |}) m'' vm'' (Vloc l ofs) -> 
             bsem_expr vm m (Prim Ref [:: e] t) m'' vm'' (Vloc l ofs)
| bsem_deref : forall vm m e t m' vm' l ofs bf v,
               bsem_expr vm m e m' vm' (Vloc l ofs) ->
               deref_addr ge (typeof_expr e) m l ofs bf v ->
               typeof_expr e = t ->
               BeeTypes.type_is_volatile t = false ->
               bsem_expr vm m (Prim Deref (e :: nil) t) m' vm' v
| bsem_massgn : forall vm m e1 m' vm' l ofs bf e2 vm'' m'' v v' t g1 ct1 ct2 g2 i g3 i',  
                bsem_expr vm m e1 m' vm' (Vloc l ofs) ->
                bsem_expr vm' m' e2 vm'' m'' v ->
                transBeePL_type (typeof_expr e1) g1 = Res ct1 g2 i ->
                transBeePL_type (typeof_expr e2) g2 = Res ct2 g3 i' ->
                sem_cast (transBeePL_value_cvalue v) ct2 ct1 m = Some (transBeePL_value_cvalue v') ->
                assign_addr ge (typeof_expr e1) m l ofs bf v' m' v' -> 
                typeof_expr e1 = t ->
                bsem_expr vm m (Prim Massgn (e1 :: e2 :: nil) t) vm'' m'' v'
| bsem_uop : forall vm m e v uop m' vm' v' t ct v'' g g' i,
             bsem_expr vm m e m' vm' v ->
             transBeePL_type (typeof_expr e) g = Res ct g' i ->
             sem_unary_operation uop (transBeePL_value_cvalue v) ct m' = Some v' ->
             transC_val_bplvalue v' = OK v'' ->
             bsem_expr vm m (Prim (Uop uop) (e :: nil) t) m' vm' v''
| bsem_bop : forall cenv vm m e1 e2 t v1 v2 bop vm' m' m'' vm'' v ct1 ct2 v' g g' i g'' i',
             bsem_expr vm m e1 m' vm' v1 ->
             bsem_expr vm' m' e2 m'' vm'' v2 ->
             transBeePL_type (typeof_expr e1) g = Res ct1 g' i ->
             transBeePL_type (typeof_expr e2) g' = Res ct2 g'' i'->
             sem_binary_operation cenv bop (transBeePL_value_cvalue v1) ct1 
                                           (transBeePL_value_cvalue v2) ct2 m'' = Some v ->
             transC_val_bplvalue v = OK v' ->
             bsem_expr vm m (Prim (Bop bop) (e1 :: e2 :: nil) t) m'' vm'' v'
(* fix me : add semantics for run primitive *)
| bsem_bind : forall vm m x e1 vm' m' v m'' vm'' e2 e2' m''' v' tx t,
              bsem_expr vm m e1 m' vm' v -> 
              subst ge vm' m' x v e2 m'' e2' ->
              bsem_expr vm' m'' e2' m''' vm'' v' ->
              bsem_expr vm m (Bind x tx e1 e2 t) m''' vm'' v'
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
| bsem_adr : forall vm m l ofs,
              bsem_expr vm m (Addr l ofs) m vm (Vloc l.(lname) ofs)
| bsem_eapp : forall vm m es vm' m' m'' vs ef g cef g' i' vres bv ts ty t,
              bsem_exprs vm m es m' vm' vs ->
              befuntion_to_cefunction ef g = Res cef g' i' ->
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

End Big_Step_Semantics.

Definition is_value (e : BeePL.expr) : bool :=
match e with 
| Val _ _ => true 
| _ => false
end.

(** An expr is safe if it cannot get stuck by doing any transition - 
    Either it reaches a value or it takes step **)
Definition safe_expr (bge : genv) (e : BeePL.expr) : Prop :=
forall v vm m vm' m', bsem_expr bge vm m e vm' m' v.
