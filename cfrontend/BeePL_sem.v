Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep.
Require Import Globalenvs Cop Csyntax Csem BeeTypes BeePL_aux BeePL_mem BeePL Csyntaxdefs Memory.
Require Import Initializersproof Cstrategy BeePL_auxlemmas Coqlib Errors SimplExpr Events BeePL_values.

From mathcomp Require Import all_ssreflect. 

(* How to transform the heap into heap regions *)
(* heap_compcert : (l1 -> v1; l2 -> v2; .... ln -> vn)
heap_koka : ((h1, (l1 -> v1; l2 -> v2; .... ln -> vn);
        (h2, (l1 -> v1; l2 -> v2; .... ln -> vn);
        ..
!(h, e)*) 

Fixpoint is_stateful_expr (e : BeePL.expr) : bool :=
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
                 | Cast t => true
                 end
| Bind x tx e e' t => is_stateful_expr e || is_stateful_expr e' 
| Cond e1 e2 e3 t => is_stateful_expr e1 || is_stateful_expr e2 || is_stateful_expr e3   
| Unit t => false
| Addr l ofs t => false
| Sinit _ _ _ _ => true
| Sfield _ _ _ => true
| For e1 e2 d e t => is_stateful_expr e 
| Enone t => false
| Esome e t => is_stateful_expr e
| Match e ps es t => is_stateful_expr e || has is_stateful_expr es
| Ebytes es t => has is_stateful_expr es
| Ainit a t es t' => has is_stateful_expr es
| Aaccess a t n t' => true
end.

Fixpoint is_stateful_exprs (es : list BeePL.expr) : bool :=
match es with 
| nil => true
| e :: es => is_stateful_expr e && is_stateful_exprs es
end.

Definition wrange d (n1 n2 : Z) : seq int :=
  let n := Z.to_nat (n2 - n1) in
  match d with
  | Up   => (map Int.repr [seq (Z.add n1 (Z.of_nat i)) | i <- iota 0 n])
  | Down => (map Int.repr [seq (Z.sub n2 (Z.of_nat i)) | i <- iota 0 n])
  end.

Definition check_unsafe_op (op : binary_operation) (s : signedness) (v1 v2 : value) : bool :=
match op with 
| Odiv => match s with 
         | Signed => if is_zero_val v2
                        || is_overflow_vals v1 v2
                     then true 
                     else false
         | Unsigned => is_zero_val v2
         end
| Omod => match s with 
         | Signed => if is_zero_val v2
                        || is_overflow_vals v1 v2
                     then true 
                     else false
         | Unsigned => is_zero_val v2
         end
| Oshl => is_val_shift v1
| Oshr => is_val_shift v1 
| _ => false
end.


Definition extract_variables_globdef (gd : (globdef fundef type)) : list (ident * type) :=
match gd with 
| Gfun fd => match fd with 
             | Internal fn => fn.(fn_args) ++ fn.(fn_vars)
             | External ef ts t cc => nil
             end
| Gvar gv => nil
end.

Fixpoint extract_variables_globdefs (gds : list (globdef fundef type)) : list (ident * type) :=
match gds with 
| nil => nil
| gd :: gds => extract_variables_globdef gd ++ extract_variables_globdefs gds
end.

Fixpoint string_of_nat (n : nat) : string :=
match n with
| O => "0"%string
| S n' => append (string_of_nat n') "1"%string (* or a real digit encoder *)
end.

Fixpoint ident_in_list (x : ident) (l : list ident) {struct l} : bool :=
  match l with
  | nil => false
  | y :: ys => if (x =? y)%positive then true else ident_in_list x ys
  end.

Fixpoint create_fresh_ident_aux (used : list ident) (next : positive) (fuel : nat) : option ident :=
  match fuel with
  | O => None (* exhausted fuel *)
  | S fuel' =>
      if ident_in_list next used then
        create_fresh_ident_aux used (Pos.succ next) fuel'
      else
        Some next
  end.

Definition create_fresh_ident (used : list ident) : ident :=
  match create_fresh_ident_aux used 100%positive 10000 with
  | Some id => id
  | None => 1%positive (* fallback if we somehow exhaust fuel *)
  end.

Inductive sem_allocate_fields : positive -> ptrofs -> ident -> list ident -> list value -> list type -> Memory.mem -> Memory.mem -> Prop :=
| sem_allocate_nil : forall b ofs sid m,
                          sem_allocate_fields b ofs sid nil nil nil m m
| sem_allocate_struct : forall loc ofs ge sid co f delta bf fs v vs t ts m1 m2 m3, 
                        ge.(genv_cenv)!sid = Some co ->
                        field_offset (bcomposite_composite_env ge.(genv_cenv)) f (bmembers_cmembers (co_members co)) = OK (delta, bf) ->
                        assign_addr ge t m1 loc (Ptrofs.add ofs (Ptrofs.repr delta)) bf v m2 v ->
                        sem_allocate_fields loc ofs sid fs vs ts m2 m3 ->
                        sem_allocate_fields loc ofs sid (f :: fs) (v :: vs) (t :: ts) m1 m3.

Inductive sem_array_init_helper : Memory.mem -> Values.block -> ptrofs -> list value -> type -> Memory.mem -> Prop :=
| sem_allocate_array_elm_nil : forall m loc ofs t,
                               sem_array_init_helper m loc ofs nil t m
| sem_allocate_array_elm : forall ge m loc ofs v vs t m' m'',
                           assign_addr ge t m loc ofs Full v m' v ->
                           sem_array_init_helper m' loc (Ptrofs.add ofs (Ptrofs.repr 1)) vs t m'' ->
                           sem_array_init_helper m loc ofs vs t m''.

Inductive sem_array_init : store_context -> ident -> type -> list value -> vmap -> Memory.mem -> 
                           vmap -> Memory.mem -> store_context -> Prop :=
| sem_allocate_array : forall Sigma ge vm arr t aty vs loc m vm' m' m'' Sigma',
                       alloc_variables ge Sigma vm m ((arr, t) :: nil) vm' m' Sigma' ->
                       vm ! arr = Some (loc, t) ->
                       get_array_elm_ty t = OK aty ->
                       sem_array_init_helper m' loc (Ptrofs.repr 0) vs aty m'' ->
                       sem_array_init Sigma arr t vs vm m vm' m'' Sigma'.
          
Section Big_Step_Semantics.

Variable (ge : genv).

(* Big step semantics without lv, rv, or context *) 
Inductive bsem_expr : program -> vmap -> Memory.mem -> BeePL.expr -> Memory.mem -> vmap -> value -> Prop := 
| bsem_value : forall p vm m v t,
               well_formed_value v t ->
               bsem_expr p vm m (Val v t) m vm v
| bsem_lvar : forall p vm m x t l v,
              vm!x = Some (l, t) -> 
              deref_addr t m l Ptrofs.zero Full v ->
              bsem_expr p vm m (Var x t) m vm v
| bsem_gbvar : forall p vm m x t l v,
               vm!x = None ->
               Genv.find_symbol ge x = Some l -> 
               deref_addr t m l Ptrofs.zero Full v ->
               bsem_expr p vm m (Var x t) m vm v
| bsem_consti : forall p vm m i t,
                bsem_expr p vm m (Const (ConsInt i) t) m vm (Vint i)
| bsem_constl : forall p vm m i t, 
                bsem_expr p vm m (Const (ConsLong i) t) m vm (Vint64 i)
| bsem_constu : forall p vm m,
                bsem_expr p vm m (Const (ConsUnit) Utype) m vm (Vunit)
| bsem_appr : forall p vm1 vm_callee m1 e es t l fd m2 m3 m4 m5 m6 vs rv Sigma ,
              (* head: evaluate the function expression to a pointer/location *)
              bsem_expr p vm1 m1 e m2 vm1 (Vloc l Ptrofs.zero) ->
              Genv.find_funct ge (trans_bvalue_cvalue (Vloc l Ptrofs.zero))  = Some (Internal fd) ->
              BeePL.type_of_fundef (Internal fd) =
                Ftype (typeof_exprs es) (get_effect_fundef (Internal fd)) (get_rt_fundef (Internal fd)) (get_v_fundef (Internal fd)) ->
              list_norepet (fd.(fn_args) ++ fd.(BeePL.fn_vars)) ->
              (* allocate callee locals/args: produce vm_callee *)
              alloc_variables ge empty_context empty_vmap m2 (fd.(fn_args) ++ fd.(BeePL.fn_vars)) vm_callee m3 Sigma ->
              (* evaluate arguments in the CALLER env *)
              bsem_exprs p vm1 m3 es m4 vm1 vs ->
              typeof_values vs (unzip2 fd.(fn_args)) ->
              (* bind parameters in the CALLEE env *)
              bind_variables ge vm_callee m4 fd.(fn_args) vs m5 ->
              (* execute the callee body under CALLEE env *)
              bsem_expr p vm_callee m5 fd.(BeePL.fn_body) m6 vm_callee rv ->
              typeof_value rv (get_rt_fundef (Internal fd)) ->
              t = (get_rt_fundef (Internal fd)) ->
              (* return to the caller: env is vm1 again *)
              bsem_expr p vm1 m1 (App e es t) m6 vm1 rv
| bsem_ref : forall bge p vm m e m' ml m'' v l a t,
             bsem_expr p vm m e m' vm v ->
             Mem.alloc m 0 (sizeof_type p.(prog_comp_env) (Vtype t)) = ml ->
             assign_addr bge (Vtype t) ml.1 ml.2 Ptrofs.zero Full v m'' v -> 
             bsem_expr p vm m (Prim Ref [:: e] (Ptrtype (Reftype (Bprim t) a))) m'' vm (Vloc l Ptrofs.zero)
| bsem_deref : forall p vm m e m' l ofs v,
               bsem_expr p vm m e m' vm (Vloc l ofs) ->
               deref_addr (typeof_expr e) m' l ofs Full v ->
               bsem_expr p vm m (Prim Deref (e :: nil) (typeof_expr e)) m' vm v
| bsem_massgn : forall p vm m e1 m' l ofs bf e2 m'' v v' pt ct1 ct2,  
                bsem_expr p vm m e1 m' vm (Vloc l ofs) ->
                bsem_expr p vm m' e2 m'' vm v ->
                transBeePL_type (typeof_expr e1) = ct1  ->
                transBeePL_type (typeof_expr e2) = ct2  ->
                typeof_expr e1 = Ptrtype pt ->
                typeof_expr e2 = get_data_type pt ->
                sem_cast (trans_bvalue_cvalue v) ct2 ct1 m = Some (trans_bvalue_cvalue v') ->
                assign_addr ge (typeof_expr e1) m l ofs bf v' m' v' -> 
                bsem_expr p vm m (Prim Massgn (e1 :: e2 :: nil) Utype) m'' vm Vunit
| bsem_uop : forall p vm m e v uop m' v' ct v'',
             bsem_expr p vm m e m' vm v ->
             transBeePL_type (typeof_expr e) = ct ->
             sem_unary_operation uop (trans_bvalue_cvalue v) ct m' = Some v' ->
             trans_cvalue_bvalue v' = OK v'' ->
             bsem_expr p vm m (Prim (Uop uop) (e :: nil) (typeof_expr e)) m' vm v''
| bsem_bop_unsafe : forall p vm m e1 e2 v1 v2 bop s m' m'' zv,
                    bsem_expr p vm m e1 m' vm v1 ->
                    bsem_expr p vm m' e2 m'' vm v2 ->
                    signedness_of_type (typeof_expr e1) = Some s ->
                    check_unsafe_op bop s v1 v2 = true ->
                    return_bzero (typeof_expr e1) = OK zv ->
                    bsem_expr p vm m (Prim (Bop bop) (e1 :: e2 :: nil) (typeof_expr e1)) m'' vm zv
| bsem_bop_safe : forall p cenv vm m e1 e2 v1 v2 bop s m' m'' ct1 ct2 v v',
                  bsem_expr p vm m e1 m' vm v1 ->
                  bsem_expr p vm m' e2 m'' vm v2 ->
                  signedness_of_type (typeof_expr e1) = Some s ->
                  check_unsafe_op bop s v1 v2 = false ->
                  transBeePL_type (typeof_expr e1) = ct1 ->
                  transBeePL_type (typeof_expr e2) = ct2 ->
                  sem_binary_operation cenv bop (trans_bvalue_cvalue v1) ct1 
                                           (trans_bvalue_cvalue v2) ct2 m'' = Some v ->
                  trans_cvalue_bvalue v = OK v' ->
                  bsem_expr p vm m (Prim (Bop bop) (e1 :: e2 :: nil) (typeof_expr e1)) m'' vm v'
| ssem_bcast : forall p vm m e  m' v t2 v' v'',
               bsem_expr p vm m e m' vm v ->
               sem_cast (trans_bvalue_cvalue v) (transBeePL_type (typeof_expr e)) (transBeePL_type t2) m' = Some v' ->
               trans_cvalue_bvalue v' = OK v'' ->
               bsem_expr p vm m (Prim (Cast t2) (e:: nil) t2) m' vm v''
| bsem_bind_subst : forall bge p vm m x e1 m' m'' m''' v e2 l v' tx,
                    bsem_expr p vm m e1 m' vm v -> 
                    not (x =? Ctypesdefs.ident_of_string "_")%positive ->
                    vm!x = Some (l, tx) ->
                    chunk_for_volatile_type (transBeePL_type tx) Full = None ->
                    Cop.sem_cast (trans_bvalue_cvalue v) (transBeePL_type (typeof_expr e1))
                      (transBeePL_type tx) m' = Some (trans_bvalue_cvalue v) ->
                    assign_addr bge tx m' l Ptrofs.zero Full v m'' v -> 
                    (* vm <- (x, v) ==> vm'; [e2]vm'--> v'*)
                    (*SubstE x (Val v (typeof_expr e1)) e2 e2' ->*)
                    bsem_expr p vm m'' e2 m''' vm v' ->
                    bsem_expr p vm m (Bind x tx e1 e2 (typeof_expr e2)) m''' vm v'
| bsem_bind_no_subst : forall p vm m x e1 m' m'' v e2 v' tx,
                       bsem_expr p vm m e1 m' vm v -> 
                       (x =? Ctypesdefs.ident_of_string "_")%positive ->
                       bsem_expr p vm m' e2 m'' vm v' ->
                       bsem_expr p vm m (Bind x tx e1 e2 (typeof_expr e2)) m'' vm v'
| bsem_ctrue : forall p vm m e1 e2 e3 t  m' vb ct1 v' v v'' m'', 
               bsem_expr p vm m e1 m' vm vb -> 
               transBeePL_type (typeof_expr e1) = ct1 ->
               bool_val (trans_bvalue_cvalue vb) ct1 m' = Some true ->
               bsem_expr p vm m' e2 m'' vm v' ->
               Cop.sem_cast (trans_bvalue_cvalue v') (transBeePL_type (typeof_expr e2)) (transBeePL_type t) m'' = Some v'' ->
               trans_cvalue_bvalue v'' = OK v ->
               bsem_expr p vm m (Cond e1 e2 e3 t) m'' vm v
| bsem_cfalse : forall p vm m e1 e2 e3 t m' vb ct1 v' v v'' m'', 
                bsem_expr p vm m e1 m' vm vb -> 
                transBeePL_type (typeof_expr e1) = ct1 ->
                bool_val (trans_bvalue_cvalue vb) ct1 m' = Some false ->
                bsem_expr p vm m' e3 m'' vm v' ->
                Cop.sem_cast (trans_bvalue_cvalue v') (transBeePL_type (typeof_expr e3)) (transBeePL_type t) m'' = Some v'' ->
                trans_cvalue_bvalue v'' = OK v ->
                bsem_expr p vm m (Cond e1 e2 e3 t) m'' vm v
| bsem_ut : forall p vm m, 
            bsem_expr p vm m (Unit Utype) m vm Vunit
| bsem_adr : forall p vm m l ofs t,
             bsem_expr p vm m (Addr l ofs t) m vm (Vloc l.(lname) ofs)
(*| bsem_eapp : forall p vm m es vm' m' m'' vs ef cef vres bv ts ty t,
              bsem_exprs p vm m es m' vm' vs ->
              befunction_to_cefunction ef = cef ->
              external_call cef ge (trans_bvalues_cvalues vs) m' t vres m'' ->
              trans_cvalue_bvalue vres = OK bv ->
              bsem_expr p vm m (BeePL.Eapp ef ts es ty) m'' vm' bv*)
| bsem_screate : forall Sigma p x ids t vm1 m1 es vm2 m2 vm3 m3 m4 vs fid loc ofs st sa Sigma',
                 bsem_exprs p vm1 m1 es m2 vm2 vs ->
                 create_fresh_ident (unzip1 (extract_variables_globdefs (map (fun '(_, gd, _) => gd) p.(prog_defs)))) = fid ->
                 alloc_variables ge Sigma vm2 m2 ((fid, t) :: nil) vm3 m3 Sigma' ->
                 vm3!fid = Some (loc, t) ->
                 t = Stype st sa ->
                 (*bsem_expr vm3 m3 (Var fid (Ptype t)) m'' vm'' (Val (Vloc loc ofs) (Reftype h t a)) -> *)
                 sem_allocate_fields loc ofs x ids vs (map typeof_expr es) m3 m4 ->
                 bsem_expr p vm1 m1 (Sinit x ids es t) m2 vm2 (Vloc loc ofs) 
| bsem_sfield : forall p b ofs id co delta bf f vm m vm' m' e t sid sa, (* bitfield is lost *)
                bsem_expr p vm m e m' vm' (Vloc b ofs) ->
                typeof_expr e = (Ptrtype (Reftype (Bstruct sid sa) noattr)) ->
                ge.(genv_cenv)!id = Some co ->
                field_offset (bcomposite_composite_env ge.(genv_cenv)) f (bmembers_cmembers (co_members co)) = OK (delta, bf) ->
                bsem_expr p vm m (Sfield e f t)  
                               m vm (Vloc b (Ptrofs.add ofs (Ptrofs.repr delta))) 
| bsem_for : forall p e1 e2 d e3 lo hi n vm m vm' m' vm'' m'' vm''' m''' t v',
             bsem_expr p vm m e1 m' vm' lo ->
             bsem_expr p vm' m' e2 m'' vm'' hi ->
             compute_range lo hi = OK n ->
             bsem_bfor p n vm'' m'' (For e1 e2 d e3 t) m''' vm''' v' -> 
             bsem_expr p vm m (For e1 e2 d e3 t) m''' vm''' v'
| bsem_none : forall p m vm t,
              bsem_expr p vm m (Enone t) m vm (Voption None)
| bsem_some : forall p m vm t e vm' m' v,
              bsem_expr p vm m e m' vm' v ->
              bsem_expr p vm m (Esome e t) m vm (Voption (Some v))
| bsem_match_none : forall p m vm t e p1 p2 e1 e2 vm' m' vm'' m'' v1 v2 vm''' m''',
                    bsem_expr p vm m e m' vm' (Voption None) ->
                    bsem_expr p vm' m' e1 m'' vm'' v1 ->
                    bsem_expr p vm'' m'' e2 m''' vm''' v2 ->
                    bsem_expr p vm m (Match e (p1 :: p2 :: nil) (e1 :: e2 :: nil) t) m'' vm'' 
                      (if eq_pattern p1 Pnone then v1 else v2) 
| bsem_match_some : forall p m vm t e ve p1 p2 e1 e2 vm' m' vm'' m'' v1 v2 vm''' m''',
                    bsem_expr p vm m e m' vm' (Voption (Some ve)) ->
                    bsem_expr p vm' m' e1 m'' vm'' v1 ->
                    bsem_expr p vm'' m'' e2 m''' vm''' v2 ->
                    bsem_expr p vm m (Match e (p1 :: p2 :: nil) (e1 :: e2 :: nil) t) m'' vm'' 
                       (if eq_pattern p1 Pnone then v2 else v1)  
| bsem_ainit : forall Sigma p vm m m' vm' vs arr t es loc vm'' m'' Sigma', 
               bsem_exprs p vm m es m' vm' vs ->
               sem_array_init Sigma arr t vs vm' m' vm'' m'' Sigma' ->
               vm'' ! arr = Some (loc, t) ->
               bsem_expr p vm m (Ainit arr t es t) m'' vm'' (Vloc loc (Ptrofs.repr 0)) 
| bsem_aaccess : forall p vm m arr t n t' loc aty v,
                 vm ! arr = Some (loc, t) ->
                 get_array_elm_ty t = OK aty ->
                 deref_addr aty m loc (Ptrofs.repr (Z.of_nat n)) Full v ->
                 bsem_expr p vm m (Aaccess arr t n t') m vm v
(* fix me : add semantics for hexpr *)
with bsem_exprs : program -> vmap -> Memory.mem -> list BeePL.expr -> Memory.mem -> vmap -> list value -> Prop :=
| bsem_nil : forall p vm m,
             bsem_exprs p vm m nil m vm nil
| bsem_cons : forall p vm m m' m'' v vs e es vm' vm'',
              bsem_expr p vm m e m' vm' v ->
              bsem_exprs p vm' m' es m'' vm'' vs ->
              bsem_exprs p vm m (e :: es) m'' vm'' (v :: vs)
with bsem_bfor : program -> Z -> vmap -> Memory.mem -> expr -> Memory.mem -> vmap -> value -> Prop :=
| bsem_for_nil : forall p vm m e,
                 bsem_bfor p (Z.of_nat O) vm m e m vm Vunit
| bsem_for_one : forall p n vm m e m' vm' vm'' m'' v v',
                 bsem_expr p vm m e m' vm' v ->
                 bsem_bfor p (Z.of_nat n) vm' m' e m'' vm'' v' ->
                 bsem_bfor p (Z.of_nat (S n)) vm m e m'' vm'' v'.

End Big_Step_Semantics.


Scheme bsem_expr_ind_mut := Induction for bsem_expr Sort Prop
  with bsem_exprs_ind_mut := Induction for bsem_exprs Sort Prop.
Combined Scheme bsem_exprs_bsem_expr_ind_mut from bsem_exprs_ind_mut, bsem_expr_ind_mut.

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

Inductive ssem_expr : program -> vmap -> Memory.mem -> BeePL.expr -> Memory.mem -> vmap -> BeePL.expr -> Prop :=
(*| ssem_value : forall p vm m v t,
               well_formed_value v t ->
               ssem_expr p vm m (Val v t) m vm (Val v t)*)
| ssem_lvar : forall p vm m x t l v,
              vm!x = Some (l, t) -> 
              deref_addr t m l Ptrofs.zero Full v ->
              ssem_expr p vm m (Var x t) m vm (Val v t)
| ssem_gbvar : forall p vm m x t l v,
               vm!x = None ->
               Genv.find_symbol ge x = Some l -> 
               deref_addr t m l Ptrofs.zero Full v ->
               ssem_expr p vm m (Var x t) m vm (Val v t)
| ssem_consti : forall p vm m i t,
                ssem_expr p vm m (Const (ConsInt i) t) m vm (Val (Vint i) t)
| ssem_constl : forall p vm m i t, 
                ssem_expr p vm m (Const (ConsLong i) t) m vm (Val (Vint64 i) t)
| ssem_constu : forall p vm m,
                ssem_expr p vm m (Const (ConsUnit) Utype) m vm (Val (Vunit) Utype)
| ssem_app1 : forall p vm1 m1 e es t e' m2 vm2,
              ssem_expr p vm1 m1 e m2 vm2 e' ->
              ssem_expr p vm1 m1 (App e es t) m2 vm2 (App e' es t)
| ssem_app2 : forall p vm1 m1 l o es vt t es' m2 vm2,
              ssem_exprs p vm1 m1 es m2 vm2 es' ->
              ssem_expr p vm1 m1 (App (Val (Vloc l o) vt) es t) m2 vm2 
                (App (Val (Vloc l o) vt) es' t)
| ssem_app3 : forall Sigma Sigma' p vm1 vm2 m1 es t l o fd m2 m3 m4 vs vm3,
              Genv.find_funct ge (trans_bvalue_cvalue (Vloc l o)) = Some (Internal fd) ->
              BeePL.type_of_fundef (Internal fd) = 
              Ftype (unzip2 fd.(fn_args)) (get_effect_fundef (Internal fd)) (get_rt_fundef (Internal fd)) (get_v_fundef (Internal fd)) ->
              t = get_rt_fundef (Internal fd) ->
              list_norepet (fd.(fn_args) ++ fd.(BeePL.fn_vars)) ->
              alloc_variables ge Sigma vm1 m1 (fd.(fn_args) ++ fd.(BeePL.fn_vars)) vm2 m2 Sigma' -> 
              ssem_exprs p vm2 m2 es m3 vm3 vs ->
              typeof_exprs vs = (unzip2 fd.(fn_args)) ->
              bind_variables ge vm3 m3 fd.(fn_args) (extract_values_exprs vs) m4  ->
              ssem_expr p vm1 m1 (App (Val (Vloc l o) (Ftype (typeof_exprs es) 
                                                                     (get_effect_fundef (Internal fd)) 
                                                                     (get_rt_fundef (Internal fd)) (get_v_fundef (Internal fd)))) es t) m2 vm2
                               fd.(BeePL.fn_body)
| ssem_ref1 : forall p vm m e m' vm' e' bt a,
              ssem_expr p vm m e m' vm' e' ->
              ssem_expr p vm m (Prim Ref [:: e] (Ptrtype (Reftype bt a))) m' vm' 
                             (Prim Ref [:: e'] (Ptrtype (Reftype bt a)))
| ssem_ref2 : forall p vm m vm' ml m' chunk v l bt a Sigma Sigma',
              Mem.alloc m 0 (sizeof_type p.(prog_comp_env) (construct_type_btype bt)) = ml ->
              chunk_of_type (construct_type_btype bt) = Some chunk ->
              Mem.storev (transl_bchunk_cchunk chunk) ml.1 (trans_bvalue_cvalue (Vloc ml.2 Ptrofs.zero)) (trans_bvalue_cvalue v) = Some m' ->
              (*assign_addr bge (construct_type_btype bt) ml.1 ml.2 Ptrofs.zero Full v m'' v -> *)
              PTree.set l (Ptrtype (Reftype bt a)) Sigma = Sigma' ->
              ssem_expr p vm m (Prim Ref [:: (Val v (construct_type_btype bt))] (Ptrtype (Reftype bt a))) m' vm' 
                             (Val (Vloc ml.2 Ptrofs.zero) (Ptrtype (Reftype bt a)))
| ssem_deref1 : forall p vm m e t m' vm' e',
                ssem_expr p vm m e m' vm' e' ->
                ssem_expr p vm m (Prim Deref (e :: nil) t) m' vm' 
                                 (Prim Deref (e' :: nil) t)
| ssem_deref2 : forall p vm m l ofs v t,
                deref_addr (get_data_type t) m l ofs Full v ->
                ssem_expr p vm m (Prim Deref [:: Val (Vloc l ofs) (Ptrtype t)] (get_data_type t)) m vm 
                               (Val v (get_data_type t))
| ssem_massgn1 : forall p vm m e1 e2 m' vm' e1',  
                 ssem_expr p vm m e1 m' vm' e1' ->
                 ssem_expr p vm m (Prim Massgn (e1 :: e2 :: nil) Utype) m' vm' 
                                (Prim Massgn (e1' :: e2 :: nil) Utype)
| ssem_massgn2 : forall p vm m e2 e2' m' vm' l ofs t,  
                 ssem_expr p vm m e2  m' vm' e2' ->
                 ssem_expr p vm m (Prim Massgn ((Val (Vloc l ofs) (Ptrtype t)) :: e2 :: nil) Utype) m' vm' 
                                (Prim Massgn ((Val (Vloc l ofs) (Ptrtype t)) :: e2' :: nil) Utype)
| ssem_massgn3 : forall p vm m t m' l ofs bf v,  
                 assign_addr ge (get_data_type t) m l ofs bf v m' v -> 
                 ssem_expr p vm m (Prim Massgn (Val (Vloc l ofs) (Ptrtype t) ::  Val v (get_data_type t):: nil) Utype )
                                m' vm (Val Vunit Utype)
| ssem_uop1 : forall p vm m e e' uop vm' m',
              ssem_expr p vm m e m' vm' e' ->
              ssem_expr p vm m (Prim (Uop uop) (e :: nil) (typeof_expr e)) m' vm'
                             (Prim (Uop uop) (e' :: nil) (typeof_expr e))
| ssem_uop2 : forall p vm m t v uop v' ct v'',
             transBeePL_type t = ct ->
             sem_unary_operation uop (trans_bvalue_cvalue v) ct m = Some v' ->
             trans_cvalue_bvalue v' = OK v'' ->
             ssem_expr p vm m (Prim (Uop uop) [:: (Val v t)] t) m vm (Val v'' t)
| ssem_bop1 : forall p vm m vm' m' bop e1 e2 e1',
              ssem_expr p vm m e1 m' vm' e1' ->
              ssem_expr p vm m (Prim (Bop bop) (e1 :: e2 :: nil) (typeof_expr e1)) m' vm'
                             (Prim (Bop bop) (e1' :: e2 :: nil) (typeof_expr e1))
| ssem_bop2 : forall p vm m vm' m' bop v1 t1 e2 e2',
              ssem_expr p vm m e2 m' vm' e2' ->
              ssem_expr p vm m (Prim (Bop bop) (Val v1 t1 :: e2 :: nil) t1) m' vm' 
                             (Prim (Bop bop) (Val v1 t1 :: e2' :: nil) t1)
| ssem_bop3_unsafe  : forall p vm m v1 v2 bop t ct s zv,
               transBeePL_type t = ct ->
               signedness_of_type t = Some s ->
               check_unsafe_op bop s v1 v2 = true ->
               return_bzero t = OK zv ->
               ssem_expr p vm m (Prim (Bop bop) (Val v1 t :: Val v2 t :: nil) t) m vm (Val zv t) 
| ssem_bop3_safe  : forall p cenv vm m v1 v2 bop t v ct v' s,
                    transBeePL_type t = ct ->
                    signedness_of_type t = Some s ->
                    check_unsafe_op bop s v1 v2 = false ->
                    sem_binary_operation cenv bop (trans_bvalue_cvalue v1) ct 
                                            (trans_bvalue_cvalue v2) ct m = Some v ->
                    trans_cvalue_bvalue v = OK v' ->
                    ssem_expr p vm m (Prim (Bop bop) (Val v1 t :: Val v2 t :: nil) t) m vm (Val v' t)
| ssem_cast1 : forall p vm m e e' m' t,
               ssem_expr p vm m e m' vm e' ->
               ssem_expr p vm m (Prim (Cast t) (e :: nil) t) m' vm
                                (Prim (Cast t) (e' :: nil) t)
| ssem_cast2 : forall p vm m v t1 t2 v' v'',
               sem_cast (trans_bvalue_cvalue v) (transBeePL_type t1) (transBeePL_type t2) m = Some v' ->
               trans_cvalue_bvalue v' = OK v'' ->
               ssem_expr p vm m (Prim (Cast t2) (Val v t1:: nil) t2) m vm (Val v'' t2)
(* fix me : add semantics for run primitive *)
| ssem_bind1 : forall p vm m x e1 e1' e2 vm' m' tx,
               ssem_expr p vm m e1 m' vm' e1' -> 
               ssem_expr p vm m (Bind x tx e1 e2 (typeof_expr e2)) m' vm' 
                              (Bind x tx e1' e2 (typeof_expr e2)) 
| ssem_bind2 : forall p vm m x v1 e2 tx e2',
               SubstE x (Val v1 tx) e2 e2' ->
               ssem_expr p vm m (Bind x tx (Val v1 tx) e2 (typeof_expr e2)) m vm e2' 
| ssem_cond : forall p vm m e1 e2 e3 vm' m' e1', 
              ssem_expr p vm m e1 m' vm' e1' -> 
              ssem_expr p vm m (Cond e1 e2 e3 (typeof_expr e2)) m' vm' (Cond e1' e2 e3 (typeof_expr e2))
| ssem_ctrue : forall p vm m e2 e3, 
               ssem_expr p vm m (Cond (Val (Vbool true) (Vtype Tbool)) e2 e3 (typeof_expr e2)) m vm e2
| ssem_cfalse : forall p vm m e2 e3,
                ssem_expr p vm m (Cond (Val (Vbool false) (Vtype Tbool)) e2 e3 (typeof_expr e3)) m vm e3
| ssem_ut : forall p vm m, 
            ssem_expr p vm m (Unit Utype) m vm (Val Vunit Utype)
| ssem_adr : forall p vm m l ofs t a,
             ssem_expr p vm m (Addr l ofs (Ptrtype (Reftype t a))) m vm (Val (Vloc l.(lname) ofs) (Ptrtype (Reftype t a)))
| ssem_sinit1 : forall p x ids t vm1 m1 es vm2 m2 es',
                  ssem_exprs p vm1 m1 es m2 vm2 es' ->
                  ssem_expr p vm1 m1 (Sinit x ids es t) m2 vm2 (Sinit x ids es' t)
| ssem_sinit2 : forall Sigma Sigma' p x ids t vm1 m1 vm2 m2 m3 vs fid loc ofs ts a st sa,
                  create_fresh_ident (unzip1 (extract_variables_globdefs (map (fun '(_, gd, _) => gd) p.(prog_defs)))) = fid ->
                  alloc_variables ge Sigma vm1 m1 ((fid, t) :: nil) vm2 m2 Sigma' ->
                  vm2!fid = Some (loc, t) ->
                  t = Stype st sa ->
                  typeof_values (extract_values_exprs vs) ts ->
                  (*bsem_expr vm3 m3 (Var fid (Ptype t)) m'' vm'' (Val (Vloc loc ofs) (Reftype h t a)) -> *)
                  sem_allocate_fields loc ofs x ids (extract_values_exprs vs) ts m2 m3 ->
                  ssem_expr p vm1 m1 (Sinit x ids vs t) m3 vm2 (Val (Vloc loc ofs) (Ptrtype (Reftype (Bstruct st sa) a))) 
| ssem_sfield1 : forall p vm m e m' vm' e' f t, 
                 ssem_expr p vm m e m' vm' e' ->
                 ssem_expr p vm m (Sfield e f t) m' vm' (Sfield e' f t) 
| ssem_sfield2 : forall p b ofs co delta bf f vm m t sid sa, (* bitfield is lost *)
                 ge.(genv_cenv)!sid = Some co ->
                 field_offset (bcomposite_composite_env ge.(genv_cenv)) f (bmembers_cmembers (co_members co)) = OK (delta, bf) ->
                 ssem_expr p vm m (Sfield (Val (Vloc b ofs) (Ptrtype (Reftype (Bstruct sid sa) noattr))) f t)  
                               m vm (Val (Vloc b (Ptrofs.add ofs (Ptrofs.repr delta))) t) 
| ssem_for1 : forall p vm m e1 e1' e2 vm' m' d e3 t,
              ssem_expr p vm m e1 m' vm' e1' ->
              ssem_expr p vm m (For e1 e2 d e3 t) m' vm' (For e1' e2 d e3 t) 
| ssem_for2 : forall p vm m v1 t1 e2 e2' vm' m' d e3 t,
              ssem_expr p vm m e2 m' vm' e2' ->
              ssem_expr p vm m (For (Val v1 t1) e2 d e3 t) m' vm' (For (Val v1 t1) e2' d e3 t)
| ssem_for3 : forall p vm m v1 t1 v2 t2 n d e3 t m' vm' v,
              compute_range v1 v2 = OK n ->
              ssem_bfor p n vm m (For (Val v1 t1) (Val v2 t2) d e3 t) m' vm' v -> 
              ssem_expr p vm m (For (Val v1 t1) (Val v2 t2) d e3 t) m' vm' v
| ssem_none : forall p m vm t,
                ssem_expr p vm m (Enone t) m vm (Val (Voption None) t)
| ssem_some1 : forall p m vm t e vm' m' e',
               ssem_expr p vm m e m' vm' e' ->
               ssem_expr p vm m (Esome e t) m' vm' (Esome e' t)
| ssem_some2 : forall p m vm t v t',
               ssem_expr p vm m (Esome (Val v t) t') m vm (Val (Voption (Some v)) t')
| ssem_match_none1 : forall p m vm p1 p2 e1 e2 t' vm' m' e e',
                     ssem_expr p vm m e m' vm' e' ->
                     ssem_expr p vm m (Match e (p1 :: p2 :: nil) (e1 :: e2 :: nil) t') m vm 
                      (Match e' (p1 :: p2 :: nil) (e1 :: e2 :: nil) t')
| ssem_match_none2 : forall p m vm t p1 p2 e1 e2 t',
                     ssem_expr p vm m (Match (Val (Voption None) t) (p1 :: p2 :: nil) (e1 :: e2 :: nil) t') m vm 
                      (if eq_pattern p1 Pnone then e1 else e2) 
| ssem_match_some : forall p m vm t ve p1 p2 e1 e2 t',
                    ssem_expr p vm m (Match (Val (Voption (Some ve)) t) (p1 :: p2 :: nil) (e1 :: e2 :: nil) t') m vm 
                       (if eq_pattern p1 Pnone then e2 else e1)
| ssem_match_bytes : forall p vm m e p1 e1 t, (* fix me *)
                     ssem_expr p vm m (Match e (p1 :: nil) (e1 :: nil) t) m vm e1
| ssem_array_init1 : forall p vm m e es vm' m' e' arr t,
                     ssem_expr p vm m e m' vm' e' ->
                     ssem_expr p vm m (Ainit arr t (e :: es) t) m' vm' (Ainit arr t (e' :: es) t)
| ssem_array_init2 : forall p vm m v es vm' m' es' arr t aty,
                     get_array_elm_ty t = OK aty ->
                     ssem_exprs p vm m es m' vm' es' ->
                     ssem_expr p vm m (Ainit arr t (Val v aty :: es) t) m' vm' (Ainit arr t (Val v aty :: es') t)
| ssem_array_init3 : forall Sigma Sigma' p vm m vs vm' m' arr t,
                     sem_array_init Sigma arr t (extract_values_exprs vs) vm m vm' m' Sigma' ->
                     ssem_expr p vm m (Ainit arr t vs t) m' vm' (Ainit arr t vs t)
| ssem_array_access : forall p vm m arr t n t' loc aty v,
                      vm ! arr = Some (loc, t) ->
                      get_array_elm_ty t = OK aty ->
                      deref_addr aty m loc (Ptrofs.repr (Z.of_nat n)) Full v ->
                      ssem_expr p vm m (Aaccess arr t n t') m vm (Val v aty)
with ssem_exprs : program -> vmap -> Memory.mem -> list BeePL.expr -> Memory.mem -> vmap -> list BeePL.expr -> Prop :=
| ssem_nil : forall p vm m,
             ssem_exprs p vm m nil m vm nil
| ssem_cons1 : forall p vm m m' e e' es vm',
              ssem_expr p vm m e m' vm' e' ->
              ssem_exprs p vm m (e :: es) m' vm' (e' :: es)
| ssem_cons2 : forall p vm m es m' vm' v t vs,
               ssem_exprs p vm m es m' vm' vs ->
               ssem_exprs p vm m (Val v t :: es) m' vm' (Val v t :: vs)
with ssem_bfor : program -> Z -> vmap -> Memory.mem -> expr -> Memory.mem -> vmap -> expr -> Prop :=
| ssem_for_nil : forall p vm m e,
                 ssem_bfor p (Z.of_nat O) vm m e m vm (Val Vunit Utype)
| ssem_for_one : forall p n vm m e m' vm' vm'' m'' v v',
                 ssem_expr p vm m e m' vm' v ->
                 ssem_bfor p (Z.of_nat n) vm' m' e m'' vm'' v' ->
                 ssem_bfor p (Z.of_nat (S n)) vm m e m'' vm'' v'.

Scheme ssem_expr_ind_mut := Induction for ssem_expr Sort Prop
  with ssem_exprs_ind_mut := Induction for ssem_exprs Sort Prop.
Combined Scheme ssem_exprs_ssem_expr_ind_mut from ssem_exprs_ind_mut, ssem_expr_ind_mut.

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
Definition bsafe_expr (bge : genv) (p : program) (e : BeePL.expr) : Prop :=
forall v vm m vm' m', bsem_expr bge p vm m e vm' m' v.

Definition ssafe_expr (bge : genv) (p : program) (vm : vmap) (m : Memory.mem) (e : BeePL.expr) : Prop :=
is_value e \/ exists m' vm' e', ssem_expr bge p vm m e m' vm' e'.


Inductive ssem_closure : genv -> program -> vmap -> Memory.mem -> BeePL.expr -> nat -> 
                         Memory.mem -> vmap -> BeePL.expr -> Prop :=
| ssem_val : forall bge p vm m v t,
             ssem_closure bge p vm m (Val v t) 0%nat m vm (Val v t)
| ssem_one : forall bge p vm m e m' vm' e',
             ssem_expr bge p vm m e m' vm' e' ->
             ssem_closure bge p vm m e 1%nat m' vm' e'
| ssem_multi : forall bge p vm m e m' vm' e' n vm'' m'' e'',
               ssem_expr bge p vm m e m' vm' e' ->
               ssem_closure bge p vm' m' e' n m'' vm'' e'' ->
               ssem_closure bge p vm m e (n + 1) %nat m'' vm'' e''
with ssem_closures : genv -> program -> vmap -> Memory.mem -> list BeePL.expr -> nat ->
                     Memory.mem -> vmap -> list BeePL.expr -> Prop :=
| ssems_one : forall bge p vm m e m' vm' e',
              ssem_exprs bge p vm m e m' vm' e' ->
              ssem_closures bge p vm m e 1%nat m' vm' e'
| ssems_multi : forall bge p vm m e m' vm' e' n vm'' m'' e'',
                ssem_exprs bge p vm m e m' vm' e' ->
                ssem_closures bge p vm' m' e' n m'' vm'' e'' ->
                ssem_closures bge p vm m e (n + 1)%nat m'' vm'' e''.

          
(**
Reuse value domain 
What we want to do with respect to function calls? **)

(** int x = 3; 
    for (i = 0; i < x + 2) {
         body;  (** we should not decrement i **)
    } **)
(** verify at runtime if range is less than BPF_MAX_LOOPS **)

(** Types for integer variables : (int, range-interval)
    x + y 

             Gamma |- x : (t, rx)    Gamma |- y : (t, ry)
    -----------------------------------------------------------------
      Gamma |- x + y : (t, ((min(rx) + min(ry), max(rx) + max(ry))))


2+3 = 5

2 --> {2}
3 --> {3}
2+3 --> {5}


For var expr expr 

     Gamma |- n : int, rn  Gamma, (Gamma |- i : int, rn) |- e : (t, r), Gamma' 
                            Gamma' <= Gamma    
   ---------------------------------------------------------------------------------
   Gamma |- for (i = 0; i < n) e : (t


l := 4; 

|- l : ref, lr
|- 4 : int, {4}
{4} <= lr ***)


(*int uid; ---> *int


int x ----> int x *)


(* ref 0 ---> uid = 0; &uid where uid is fresh var *)

