Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Globalenvs Coqlib Memory. 
Require Import Csyntax Csem SimplExpr Ctypes Memtype.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL BeePL_auxlemmas Errors BeePL_values BeePL_notations BeePL_sem.
Require Import BeePL_helper_functions.
From mathcomp Require Import all_ssreflect. 

Local Open Scope error_monad_scope.
Local Open Scope csyntax_scope.

Inductive type_expr : bcomposite_env -> ty_context -> store_context -> expr -> effect -> type -> Prop :=
(*For all value expression, we can assume any effect type, including the empty effect *)
| ty_valu : forall cenv Gamma Sigma,
            type_expr cenv Gamma Sigma (Val Vunit tunit) nil tunit
| ty_valb : forall cenv Gamma Sigma b,
            type_expr cenv Gamma Sigma (Val (Vbool b) (Vtype (Tbool))) nil (Vtype (Tbool))
| ty_vali : forall cenv Gamma Sigma i sz s a,
            type_expr cenv Gamma Sigma (Val (Vint i) (Vtype (Tint sz s a))) nil (Vtype (Tint sz s a))
| ty_vall : forall cenv Gamma Sigma i s a,
            type_expr cenv Gamma Sigma (Val (Vint64 i) (Vtype (Tlong s a))) nil (Vtype (Tlong s a))
| ty_valloc : forall cenv Gamma Sigma l ofs h t a,
              PTree.get l Sigma = Some (Ptrtype (Reftype h t a)) ->
              type_expr cenv Gamma Sigma (Val (Vloc l ofs) (Ptrtype (Reftype h t a))) nil (Ptrtype (Reftype h t a))
| ty_valo : forall cenv Gamma Sigma o t,
            type_expr cenv Gamma Sigma (Val (Voption o) (Ptrtype (Otype t))) nil (Ptrtype (Otype t))
| ty_var : forall cenv Gamma Sigma x t, 
           PTree.get x Gamma = Some t ->
           type_expr cenv Gamma Sigma (Var x t) nil t
| ty_constint : forall cenv Gamma Sigma sz s a i,
                type_expr cenv Gamma Sigma (Const (ConsInt i) (Vtype (Tint sz s a))) nil (Vtype (Tint sz s a))
| ty_constlong : forall cenv Gamma Sigma s a i,
                 type_expr cenv Gamma Sigma (Const (ConsLong i) (Vtype (Tlong s a))) nil (Vtype (Tlong s a))
| ty_constunit : forall cenv Gamma Sigma,
                 type_expr cenv Gamma Sigma (Const (ConsUnit) tunit) nil tunit
| ty_app : forall cenv Gamma Sigma e te es rt efs ts ef efs',
           type_expr cenv Gamma Sigma e ef te -> 
           eq_type te (Ptrtype (Fptype ts efs rt)) || eq_type te (Ftype ts efs rt) ->
           type_exprs cenv Gamma Sigma es efs' ts -> 
           type_expr cenv Gamma Sigma (App e es rt) (ef ++ efs ++ efs') rt
| ty_ref : forall cenv Gamma Sigma e ef h bt a, 
           type_expr cenv Gamma Sigma e ef (construct_type_btype bt) ->
           (*type_is_volatile (transBeePL_type (construct_type_btype bt)) = false ->*)
           type_expr cenv Gamma Sigma (Prim Ref (e::nil) (Ptrtype (Reftype h bt a))) (ef ++ (Alloc h :: nil)) (Ptrtype (Reftype h bt a)) 
| ty_deref : forall cenv Gamma Sigma e ef pt h, (* inner expression should be unrestricted as it will be used later *)
             type_expr cenv Gamma Sigma e ef (Ptrtype pt) -> 
             is_option_ptr_type pt = false ->
             (*type_is_volatile (transBeePL_type (get_data_type pt)) = false ->*)
             type_expr cenv Gamma Sigma (Prim Deref (e::nil) (get_data_type pt)) (ef ++ (Read h :: nil)) (get_data_type pt)
| ty_massgn : forall cenv Gamma Sigma e e' h pt ef ef', 
              type_expr cenv Gamma Sigma e ef (Ptrtype pt) ->
              is_option_ptr_type pt = false ->
              (*type_is_volatile (transBeePL_type (get_data_type pt)) = false ->*)
              type_expr cenv Gamma Sigma e' ef' (get_data_type pt) ->
              type_expr cenv Gamma Sigma (Prim Massgn (e::e'::nil) tunit) (ef ++ ef' ++ (Write h :: nil)) tunit
| ty_notbool : forall cenv Gamma Sigma e ef,
               type_expr cenv Gamma Sigma e ef (Vtype Tbool) ->
               type_expr cenv Gamma Sigma (Prim (Uop Cop.Onotbool) (e::nil) (Vtype Tbool)) ef (Vtype Tbool)
| ty_notint : forall cenv Gamma Sigma e ef t,
              is_primint t || is_primlong t ->
              type_expr cenv Gamma Sigma e ef t ->
              type_expr cenv Gamma Sigma (Prim (Uop Cop.Onotint) (e::nil) t) ef t
| ty_neg : forall cenv Gamma Sigma e ef t,
           is_primint t || is_primlong t ->
           type_expr cenv Gamma Sigma e ef t ->
           type_expr cenv Gamma Sigma (Prim (Uop Cop.Oneg) (e::nil) t) ef t
| ty_add : forall cenv Gamma Sigma e ef1 ef2 t e',
           is_primint t || is_primlong t ->
           type_expr cenv Gamma Sigma e ef1 t ->
           type_expr cenv Gamma Sigma e' ef2 t ->
           type_expr cenv Gamma Sigma (Prim (Bop Cop.Oadd) (e::e'::nil) t) (ef1 ++ ef2) t 
| ty_sub : forall cenv Gamma Sigma e ef1 ef2 t e',
           is_primint t || is_primlong t ->
           type_expr cenv Gamma Sigma e ef1 t ->
           type_expr cenv Gamma Sigma e' ef2 t ->
           type_expr cenv Gamma Sigma (Prim (Bop Cop.Osub) (e::e'::nil) t) (ef1 ++ ef2) t
| ty_mul : forall cenv Gamma Sigma e ef1 ef2 t e',
           is_primint t || is_primlong t ->
           type_expr cenv Gamma Sigma e ef1 t ->
           type_expr cenv Gamma Sigma e' ef2 t ->
           type_expr cenv Gamma Sigma (Prim (Bop Cop.Omul) (e::e'::nil) t)  (ef1 ++ ef2) t 
| ty_div : forall cenv Gamma Sigma e ef1 ef2 t e',
           is_primint t || is_primlong t ->
           type_expr cenv Gamma Sigma e ef1 t ->
           type_expr cenv Gamma Sigma e' ef2 t ->
           type_expr cenv Gamma Sigma (Prim (Bop Cop.Odiv) (e::e'::nil) t) (ef1 ++ ef2) t
| ty_mod : forall cenv Gamma Sigma e ef1 ef2 t e',
           is_primint t || is_primlong t ->
           type_expr cenv Gamma Sigma e ef1 t ->
           type_expr cenv Gamma Sigma e' ef2 t ->
           type_expr cenv Gamma Sigma (Prim (Bop Cop.Omod) (e::e'::nil) t) (ef1 ++ ef2) t
| ty_and : forall cenv Gamma Sigma e ef1 ef2 t e',
           is_primint t || is_primlong t ->
           type_expr cenv Gamma Sigma e ef1 t ->
           type_expr cenv Gamma Sigma e' ef2 t ->
           type_expr cenv Gamma Sigma (Prim (Bop Cop.Oand) (e::e'::nil) t) (ef1 ++ ef2) t
| ty_or : forall cenv Gamma Sigma e ef1 ef2 t e',
           is_primint t || is_primlong t ->
           type_expr cenv Gamma Sigma e ef1 t ->
           type_expr cenv Gamma Sigma e' ef2 t ->
           type_expr cenv Gamma Sigma (Prim (Bop Cop.Oor) (e::e'::nil) t) (ef1 ++ ef2) t
| ty_xor : forall cenv Gamma Sigma e ef1 ef2 t e',
           is_primint t || is_primlong t ->
           type_expr cenv Gamma Sigma e ef1 t ->
           type_expr cenv Gamma Sigma e' ef2 t ->
           type_expr cenv Gamma Sigma (Prim (Bop Cop.Oxor) (e::e'::nil) t) (ef1 ++ ef2) t
| ty_shl : forall cenv Gamma Sigma e ef1 ef2 t e',
           is_primint t || is_primlong t ->
           type_expr cenv Gamma Sigma e ef1 t ->
           type_expr cenv Gamma Sigma e' ef2 t ->
           type_expr cenv Gamma Sigma (Prim (Bop Cop.Oshl) (e::e'::nil) t) (ef1 ++ ef2) t
| ty_shr : forall cenv Gamma Sigma e ef1 ef2 t e',
           is_primint t || is_primlong t ->
           type_expr cenv Gamma Sigma e ef1 t ->
           type_expr cenv Gamma Sigma e' ef2 t ->
           type_expr cenv Gamma Sigma (Prim (Bop Cop.Oshr) (e::e'::nil) t) (ef1 ++ ef2) t
| ty_eq : forall cenv Gamma Sigma e ef1 ef2 t e',
           is_primint t || is_primlong t || is_primbool t ->
           type_expr cenv Gamma Sigma e ef1 t ->
           type_expr cenv Gamma Sigma e' ef2 t ->
           type_expr cenv Gamma Sigma (Prim (Bop Cop.Oeq) (e::e'::nil) (Vtype Tbool))  (ef1 ++ ef2) (Vtype Tbool)
| ty_ne : forall cenv Gamma Sigma e ef1 ef2 t e',
           is_primint t || is_primlong t || is_primbool t ->
           type_expr cenv Gamma Sigma e ef1 t ->
           type_expr cenv Gamma Sigma e' ef2 t ->
           type_expr cenv Gamma Sigma (Prim (Bop Cop.One) (e::e'::nil) (Vtype Tbool))  (ef1 ++ ef2) (Vtype Tbool)
| ty_lt : forall cenv Gamma Sigma e ef1 ef2 t e',
           is_primint t || is_primlong t ->
           type_expr cenv Gamma Sigma e ef1 t ->
           type_expr cenv Gamma Sigma e' ef2 t ->
           type_expr cenv Gamma Sigma (Prim (Bop Cop.Olt) (e::e'::nil) (Vtype Tbool))  (ef1 ++ ef2) (Vtype Tbool)
| ty_gt : forall cenv Gamma Sigma e ef1 ef2 t e',
           is_primint t || is_primlong t ->
           type_expr cenv Gamma Sigma e ef1 t ->
           type_expr cenv Gamma Sigma e' ef2 t ->
           type_expr cenv Gamma Sigma (Prim (Bop Cop.Ogt) (e::e'::nil) (Vtype Tbool)) (ef1 ++ ef2) (Vtype Tbool)
| ty_le : forall cenv Gamma Sigma e ef1 ef2 t e',
           is_primint t || is_primlong t  ->
           type_expr cenv Gamma Sigma e ef1 t ->
           type_expr cenv Gamma Sigma e' ef2 t ->
           type_expr cenv Gamma Sigma (Prim (Bop Cop.Ole) (e::e'::nil) (Vtype Tbool))  (ef1 ++ ef2) (Vtype Tbool)
| ty_ge : forall cenv Gamma Sigma e ef1 ef2 t e',
           is_primint t || is_primlong t ->
           type_expr cenv Gamma Sigma e ef1 t ->
           type_expr cenv Gamma Sigma e' ef2 t ->
           type_expr cenv Gamma Sigma (Prim (Bop Cop.Oge) (e::e'::nil) (Vtype Tbool))  (ef1 ++ ef2) (Vtype Tbool)
| ty_bind : forall cenv Gamma Sigma x t e e' t' ef ef',
            type_expr cenv Gamma Sigma e ef t ->
            type_expr cenv (extend_context Gamma x t) Sigma e' ef' t' ->
            type_expr cenv Gamma Sigma (Bind x t e e' t') (ef ++ ef') t'
| ty_cond : forall cenv Gamma Sigma e1 e2 e3 t ef1 ef2, 
            type_expr cenv Gamma Sigma e1 ef1 (Vtype Tbool) ->
            type_expr cenv Gamma Sigma e2 ef2 t ->
            type_expr cenv Gamma Sigma e3 ef2 t ->
            type_expr cenv Gamma Sigma (Cond e1 e2 e3 t) (ef1 ++ ef2) t
| ty_unit : forall cenv Gamma Sigma,
            type_expr cenv Gamma Sigma (Unit tunit) nil tunit
| ty_addr : forall cenv Gamma Sigma l ofs h t a,
            PTree.get l.(lname) Sigma = Some (Ptrtype (Reftype h t a)) ->
            (*t' = (Reftype h t a) ->*)
            type_expr cenv Gamma Sigma (Addr l ofs (Ptrtype (Reftype h t a))) nil (Ptrtype (Reftype h t a)) 
(* return type, arg types, and effect must agree with the signature
   eBPF helper functions never return a void type and a function  *)
(*| ty_ext : forall Gamma Sigma exf ts es ef rt,
           rt = get_rt_eapp exf ->
           rt <> Ptype Tunit /\ is_funtype rt = false -> 
           ts = get_at_eapp exf ->
           type_exprs Gamma Sigma es ef ts ->
           type_expr Gamma Sigma (Eapp exf ts es rt) ((get_ef_eapp exf) ++ ef) rt *)
| ty_sinit : forall cenv Gamma Sigma x es efs h id a a' co ids cts bts, 
             type_exprs cenv Gamma Sigma es efs bts ->
             PTree.get id cenv = Some co ->
             type_of_members (combine (map Ctypes.attr_of_type (transBeePL_types transBeePL_type bts)) ids) 
                             (bmembers_cmembers co.(co_members)) = OK cts ->
             trans_ctypes_btypes trans_ctype_btype cts = OK bts ->
             type_expr cenv Gamma Sigma (Sinit x ids es (Ptrtype (Reftype h (Bstruct id a) a'))) efs (Ptrtype (Reftype h (Bstruct id a) a'))
| ty_sfield : forall cenv Gamma Sigma e x id a te ef co ct bt,
              type_expr cenv Gamma Sigma e ef te ->
              (eq_type te (Stype id a)) \/ (eq_type te (Ptrtype (Reftype mem_ident (Bstruct id a) noattr))) 
              \/ (eq_type te (Ptrtype (Otype (Reftype mem_ident (Bstruct id a) noattr)))) ->
              PTree.get id cenv = Some co ->
              Ctyping.type_of_member a x (bmembers_cmembers co.(co_members)) = OK ct ->
              trans_ctype_btype ct = OK bt ->
              type_expr cenv Gamma Sigma (Sfield e x bt) ef bt
| ty_for : forall cenv Gamma Sigma e1 e2 d e ef1 t1 ef2 t2 fv1 fv2 fv ef t,
           type_expr cenv Gamma Sigma e1 ef1 t1 ->
           type_expr cenv Gamma Sigma e2 ef2 t2 ->
           type_expr cenv Gamma Sigma e ef t -> 
           eq_type t1 t2 ->
           is_primint t || is_primlong t ->
           free_variables e1 = fv1 ->
           free_variables e2 = fv2 ->
           free_variables e = fv ->
           disjoint_vars fv fv1 ->
           disjoint_vars fv fv2 ->
           type_expr cenv Gamma Sigma (For e1 e2 d e t) (ef1 ++ ef2 ++ ef) t
| ty_none : forall cenv Gamma Sigma t,
            is_option_ptr_type t ->
            type_expr cenv Gamma Sigma (Enone (Ptrtype t)) nil (Ptrtype t)
| ty_some : forall cenv Gamma Sigma t e te ef,
            type_expr cenv Gamma Sigma e ef te ->
            is_option_ptr_type t ->
            te = get_data_type t ->
            type_expr cenv Gamma Sigma (Esome e (Ptrtype t)) ef (Ptrtype t)
| ty_matcho : forall cenv Gamma Sigma e ef te ps es efs ts fvs,
              get_patterns_var ps = fvs ->
              type_expr cenv Gamma Sigma e ef te ->
              type_exprs cenv (extends_context Gamma fvs (construct_list_type (hd tunit ts) (length fvs))) Sigma es efs ts ->
              is_option_type te \/ is_bytes te ->
              all_eq_types ts ->
              type_expr cenv Gamma Sigma (Match e ps es (hd tunit ts)) (ef ++ efs) (hd tunit ts)
| ty_ainit : forall cenv Gamma Sigma a t es t' aty efs ts,
             type_exprs cenv Gamma Sigma es efs ts -> 
             get_array_elm_ty t = OK aty -> 
             is_atype t && is_atype t' ->
             all_eq_type aty ts ->
             type_expr cenv Gamma Sigma (Ainit a t es t') efs t' (* Should we also include write effects for array initialization? *)
| ty_aaccess : forall cenv Gamma Sigma a t n t' aty, 
               get_array_elm_ty t = OK aty ->
               is_atype t ->
               eq_type aty t' ->
               type_expr cenv Gamma Sigma (Aaccess a t n t') nil t'
(*| ty_subt : forall cenv Gamma Sigma e ef t ef', 
            type_expr cenv Gamma Sigma e ef t ->
            sub_effect ef ef' ->
            type_expr cenv Gamma Sigma e ef' t*)
(* fix me : Run *)
(* fix me : Hexpr *)
(*| ty_hexpr : forall Gamma Sigma m e h ef t a, 
             type_expr Gamma Sigma e ef (Reftype h (Bprim t) a) ->
             type_expr Gamma Sigma (Hexpr m e (Reftype h (Bprim t) a)) ef (Reftype h (Bprim t) a)*)
(* fix me : Add typing rule for external function *)
with type_exprs : bcomposite_env -> ty_context -> store_context -> list expr -> effect -> list type -> Prop :=
| ty_nil : forall cenv Gamma Sigma,
           type_exprs cenv Gamma Sigma nil nil nil
| ty_cons : forall cenv Gamma Sigma e es ef efs t ts,
            type_expr cenv Gamma Sigma e ef t ->
            type_exprs cenv Gamma Sigma es efs ts ->
            type_exprs cenv Gamma Sigma (e :: es) (ef ++ efs) (t :: ts).
           
Scheme type_expr_ind_mut := Induction for type_expr Sort Prop
  with type_exprs_ind_mut := Induction for type_exprs Sort Prop.
Combined Scheme type_exprs_type_expr_ind_mut from type_exprs_ind_mut, type_expr_ind_mut.

(**** Type system for whole program ***)
Inductive type_function : bcomposite_env -> ty_context -> store_context -> BeePL.function -> Prop :=
| ty_function : forall fn cenv Gamma Sigma ef tb Gamma',
                bind_vars (bind_vars Gamma fn.(fn_args)) fn.(fn_vars) = Gamma' -> 
                type_expr cenv Gamma' Sigma fn.(fn_body) ef tb ->
                tb = fn.(fn_return) ->
                is_ptrtype tb = false ->
                ef = fn.(fn_effect) ->
                type_function cenv Gamma Sigma fn.

Inductive type_fundef : ef_env -> bcomposite_env -> ty_context -> store_context -> BeePL.fundef -> Prop :=
| ty_ifundef : forall efenv cenv Gamma Sigma fd fn,
               fd = Internal fn ->
               type_function cenv Gamma Sigma fn ->
               type_fundef efenv cenv Gamma Sigma fd
| ty_efundef : forall efenv cenv Gamma Sigma ef ts t cc fd efs,
               fd = External ef ts t cc ->
               get_ef_type efenv (get_name_eapp ef) = OK efs ->
               t = (get_rt_eapp ef) ->
               ts = (get_at_eapp ef) ->
               ts = (fst efs) ->
               t = (fst (snd efs)) ->
               (get_ef_eapp ef) = (snd (snd efs)) ->
               type_fundef efenv cenv Gamma Sigma fd.

Inductive type_globalvar : ef_env -> bcomposite_env -> ty_context -> store_context -> BeePL.globvar type -> effect -> type -> Prop :=
| ty_globvar : forall efenv cenv Gamma Sigma ef gv, 
               construct_ef_gvars gv.(gvar_init) = OK ef ->
               type_globalvar efenv cenv Gamma Sigma gv ef gv.(gvar_info).

Inductive type_globdef : ef_env -> bcomposite_env -> ty_context -> store_context ->  BeePL.globdef BeePL.fundef BeeTypes.type -> Prop :=
| ty_fundef : forall efenv cenv Gamma Sigma gfd fd,
              gfd = AST.Gfun fd ->
              type_fundef efenv cenv Gamma Sigma fd ->
              type_globdef efenv cenv Gamma Sigma gfd
| ty_globdef : forall efenv cenv Gamma Sigma gfd g ef t,
              gfd = Gvar g ->
              type_globalvar efenv cenv Gamma Sigma g ef t ->
              type_globdef efenv cenv Gamma Sigma gfd.

Inductive type_globdefs :  ef_env -> bcomposite_env -> ty_context -> store_context -> list (BeePL.globdef BeePL.fundef BeeTypes.type) -> Prop :=
| ty_gnil : forall efenv cenv Gamma Sigma,
            type_globdefs efenv cenv Gamma Sigma nil
| ty_gcons : forall efenv cenv Gamma Sigma g gs,
             type_globdef efenv cenv Gamma Sigma g ->
             type_globdefs efenv cenv Gamma Sigma gs ->
             type_globdefs efenv cenv Gamma Sigma (g :: gs).

Inductive type_program : BeePL.program -> Prop :=
| ty_prog : forall p cenv Gamma,
            check_get_fundef_sec p.(prog_defs) = true ->
            Gamma = bind_globdef (PTree.empty _) (map (fun '(id, gd, _) => (id, gd)) p.(prog_defs)) ->
            cenv = p.(prog_comp_env) ->
            type_globdefs beepl_ef_env cenv Gamma empty_context (map (fun '(_, gd, _) => gd) p.(prog_defs)) ->
            type_program p.


(**** Well formedness ****)

(*** Well formed var ***)
Inductive well_formed_var (Gamma : ty_context) (Sigma : store_context) (bge : BeePL.genv) (vm : vmap) (m : Memory.mem) : Prop :=
| store_well_typed_lvar : (forall x t,
                           Gamma ! x = Some t ->
                           (exists l' t' v, vm ! x = Some (l', t') /\
                           t = t' /\ PTree.get l' Sigma = Some t /\ 
                                                  deref_addr t m l' Ptrofs.zero Full v)) ->
                          well_formed_var Gamma Sigma bge vm m
| store_well_typed_gvar : (forall x t,
                          Gamma ! x = Some t ->
                          (exists l' v, vm ! x = None /\ Genv.find_symbol bge x = Some l' /\ 
                                            PTree.get l' Sigma = Some t /\ 
                                            deref_addr t m l' Ptrofs.zero Full v)) ->
                         well_formed_var Gamma Sigma bge vm m.

(*** Well formed loc (coming from ref, not variables) ***)
Inductive well_formed_loc (Sigma : store_context) (bge : BeePL.genv) (vm : vmap) (m : Memory.mem) : Prop :=
| store_well_typed_loc : (forall x ofs t, PTree.get x Sigma = Some (Ptrtype t) ->
                          (exists chunk, Mem.valid_access m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) Freeable /\
                                         chunk_of_type (get_data_type t) = Some chunk)) /\
                          (forall chunk x ofs t, Mem.valid_access m (transl_bchunk_cchunk chunk) x (Ptrofs.unsigned ofs) Freeable /\
                                                 chunk_of_type (get_data_type t) = Some chunk -> 
                                                 PTree.get x Sigma = Some (Ptrtype t)) ->
                          well_formed_loc Sigma bge vm m.

(*** Well formed function ***)
Inductive well_formed_function (cenv : bcomposite_env) (Gamma : ty_context) (Sigma : store_context) (bge : BeePL.genv) (vm : vmap) (m : Memory.mem) : Prop :=
| store_well_typed_fn : (forall l o ef te ts efs rt vs efs', 
                         type_expr cenv Gamma Sigma (Val (Vloc l o) te) ef te -> 
                         eq_type te (Ptrtype (Fptype ts efs rt)) || eq_type te (Ftype ts efs rt) ->
                         type_exprs cenv Gamma Sigma vs efs' ts ->
                         exists fd, Genv.find_funct bge (trans_bvalue_cvalue (Vloc l o)) = Some (Internal fd) /\
                                    list_norepet (fd.(fn_args) ++ fd.(BeePL.fn_vars)) /\ 
                                    length fd.(fn_args) = length (extract_values_exprs vs) /\
                                    ts = (unzip2 fd.(fn_args)) /\ rt = get_rt_fundef (Internal fd)) ->
                        well_formed_function cenv Gamma Sigma bge vm m.

(** Well-Typed Store **)
(* A store st is well-typed with respect to a store typing context Sigma if the
   term at each location l in vm has the type at location l in store typing context
   and there exists a value in the memory at that location. *)
(* It is more evolved due to two maps used in CompCert for retrieving data from the memory *)
(* Since we only allow pointers through references, it is safe to say that if there exists a 
   location in memory then it is also safe to deref that location *)
(* Mem.valid_pointer ensures that the location l with ofset ofs is nonempty in memory m *)
Definition store_well_typed (cenv : bcomposite_env) (Gamma : ty_context) (Sigma : store_context) 
                            (bge : BeePL.genv) (vm : vmap) (m : Memory.mem) : Prop :=
well_formed_var Gamma Sigma bge vm m /\ well_formed_loc Sigma bge vm m /\ well_formed_function cenv Gamma Sigma bge vm m.
  

Definition accumulate_effect_function (fn : BeePL.function) : effect := fn.(fn_effect).

Definition accumulate_effect_fundef (fd : BeePL.fundef) : effect := 
match fd with 
| Internal fn => fn.(fn_effect)
| External fn ts t cc => get_ef_eapp fn
end.

Definition accumulate_effect_globalvar (gv : BeePL.globvar type) : res effect := 
do ef <- construct_ef_gvars gv.(gvar_init);
OK ef.

Definition accumulate_effect_gd (gd : BeePL.globdef BeePL.fundef BeeTypes.type) : res effect :=
match gd with 
| AST.Gfun fd => OK (accumulate_effect_fundef fd)
| AST.Gvar g => accumulate_effect_globalvar g
end.

Fixpoint accumulate_effect_gds (gds : list (BeePL.globdef BeePL.fundef BeeTypes.type)) : res effect :=
match gds with 
| nil => OK nil
| gd :: gds => do ef <- accumulate_effect_gd gd;
               do efs <- accumulate_effect_gds gds;
               OK (ef ++ efs)
end.

Definition accumulate_effect_progs (p : BeePL.program) : res effect :=
accumulate_effect_gds (map (fun '(_, gd, _) => gd) p.(prog_defs)).

(* Value typing *)
(* A value does not produce any effect *)
Lemma value_typing : forall cenv Gamma Sigma ef t v,
type_expr cenv Gamma Sigma (Val v t) ef t ->
type_expr cenv Gamma Sigma (Val v t) nil t. 
Proof.
move=> cenv Gamma Sigma ef t v. move eq : (Val v t)=> v' ht.
elim: ht eq=> //=.
+ move=> cenv' Gamma' Sigma' [] h1; subst. by apply ty_valu.
+ move=> cenv' Gamma' Sigma' b [] h1; subst. by apply ty_valb.
+ move=> cenv' Gamma' Sigma' i sz s a [] h1; subst. by apply ty_vali.
+ move=> cenv' Gamma' Sigma' i s a [] h1; subst. by apply ty_vall.
+ move=> cenv' Gamma' Sigma' l ofs h bt a hs [] h1; subst. by apply ty_valloc. 
move=> cenv' Gamma' Sigma' o t' [] h1; subst. by apply ty_valo.
Qed.

Lemma type_infer_vunit: forall cenv Gamma Sigma ef t t', 
type_expr cenv Gamma Sigma (Val Vunit t) ef t' ->
t = tunit /\ t' = tunit.
Proof.
move=> cenv Gamma Sigma ef t t'. unfold tunit.
move eq : (Val Vunit t)=> v ht. elim: ht eq=>//=.
by move=> cenv' Gamma' Sigma' [] h; subst.
Qed.

Lemma type_infer_option: forall cenv Gamma Sigma ef o t t',
type_expr cenv Gamma Sigma (Val (Voption o) t) ef t' ->
exists pt, t = (Ptrtype (Otype pt)) /\ t' = (Ptrtype (Otype pt)).
Proof.
move=> cenv Gamma Sigma ef o t t'.
move eq: (Val (Voption o) t)=> v ht. elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' o' pt' [] h1 h2; subst. by exists pt'.
Qed.

Lemma type_infer_vbool: forall cenv Gamma Sigma ef b t t', 
type_expr cenv Gamma Sigma (Val (Vbool b) t) ef t' ->
t = Vtype Tbool /\ t' = Vtype Tbool.
Proof.
move=> cenv Gamma Sigma ef b t t'. 
move eq : (Val (Vbool b) t)=> v ht. elim: ht eq=>//=.
by move=> cenv' Gamma' Sigma' b' [] h1 h2; subst.
Qed.

Lemma type_infer_int: forall cenv Gamma Sigma i ef t t', 
type_expr cenv Gamma Sigma (Val (Vint i) t) ef t' ->
(exists sz s a, t = Vtype (Tint sz s a) /\ t' = Vtype (Tint sz s a)).
Proof.
move=> cenv Gamma Sigma i ef t t'. 
move eq : (Val (Vint i) t)=> v ht. 
elim: ht eq=>//=. move=> cenv' Gamma' Sigma' i' sz' s' a' [] h1 h2; subst. 
by exists sz', s', a'.
Qed.

Lemma type_infer_long: forall cenv Gamma Sigma i ef t t', 
type_expr cenv Gamma Sigma (Val (Vint64 i) t) ef t' ->
(exists s a, t = Vtype (Tlong s a) /\ t' = Vtype (Tlong s a)).
Proof.
move=> cenv Gamma Sigma i ef t t'. 
move eq : (Val (Vint64 i) t)=> v ht. 
elim: ht eq=>//=. move=> cenv' Gamma' Sigma' i' s' a' [] h2 h3; subst.
by exists s', a'.
Qed.

Lemma type_infer_loc: forall cenv Gamma Sigma l ofs ef t t', 
type_expr cenv Gamma Sigma (Val (Vloc l ofs) t) ef t' ->
(exists h bt a, t = Ptrtype (Reftype h bt a) /\ 
                t' = Ptrtype (Reftype h bt a) /\ 
                PTree.get l Sigma = Some (Ptrtype (Reftype h bt a))).
Proof.
move=> cenv Gamma Sigma l ofs ef t t'. 
move eq : (Val (Vloc l ofs) t)=> v ht. elim: ht eq=>//=.
move=> cenv' Gamma' Sigma' l' ofs' h' bt' a' hs [] h1 h2 h3; subst. 
by exists h', bt', a'.
Qed.

Lemma type_infer_var : forall cenv Gamma Sigma x t ef t',
type_expr cenv Gamma Sigma (Var x t) ef t' ->
t = t' /\ PTree.get x Gamma = Some t.
Proof.
move=> cenv Gamma Sigma x t ef t'. 
move eq: (Var x t)=> v ht. elim: ht eq=> //=.
by move=> cenv' Gamma' Sigma' x' t'' hxt [] h1 h2; subst.
Qed.

Lemma type_infer_consti: forall cenv Gamma Sigma i ef t t', 
type_expr cenv Gamma Sigma (Const (ConsInt i) t) ef t' ->
(exists sz s a, t = Vtype (Tint sz s a) /\ t' = Vtype (Tint sz s a)).
Proof.
move=> cenv Gamma Sigma i ef t t'. 
move eq : (Const (ConsInt i) t)=> v ht. 
elim: ht eq=>//=. move=> cenv' Gamma' Sigma' sz' s' a' i' [] h1 h2; subst. 
by exists sz', s', a'.
Qed.

Lemma type_infer_constl: forall cenv Gamma Sigma i ef t t', 
type_expr cenv Gamma Sigma (Const (ConsLong i) t) ef t' ->
(exists s a, t = Vtype (Tlong s a) /\ t' = Vtype (Tlong s a)).
Proof.
move=> cenv Gamma Sigma i ef t t'. 
move eq : (Const (ConsLong i) t)=> v ht. 
elim: ht eq=>//=. move=> cenv' Gamma' Sigma' s' a' i' [] h1 h2; subst. 
by exists s', a'.
Qed.

Lemma type_infer_constu: forall cenv Gamma Sigma ef t t', 
type_expr cenv Gamma Sigma (Const ConsUnit t) ef t' ->
t = tunit /\ t' = tunit.
Proof.
move=> cenv Gamma Sigma ef t t'. 
move eq : (Const ConsUnit t)=> v ht. elim: ht eq=>//=.
by move=> cenv' Gamma' Sigma' [] h1; subst.
Qed.

Lemma type_infer_app: forall cenv Gamma Sigma e es rt ef t,
type_expr cenv Gamma Sigma (App e es rt) ef t ->
(t = rt /\
exists te ts ef' efs efs', type_expr cenv Gamma Sigma e ef' te /\ 
(eq_type te (Ptrtype (Fptype ts efs rt)) || eq_type te (Ftype ts efs rt)) /\
type_exprs cenv Gamma Sigma es efs' ts).
Proof.
move=> cenv Gamma Sigma e es rt ef t.
move eq: (App e es rt)=> ve ht. elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e' te es' rt' efs ts ef' efs' ht1 hin ht2 heq [] h1 h2 h3; subst; split=> //=.
exists te, ts, ef', efs, efs'; split=> //=.
Qed.

Lemma type_infer_ref: forall cenv Gamma Sigma e ef t t',
type_expr cenv Gamma Sigma (Prim Ref [:: e] t) ef t' ->
(exists h bt a, t = Ptrtype (Reftype h bt a) /\ t' = Ptrtype (Reftype h bt a)).
Proof.
move=> cenv Gamma Sigma e ef t t'.
move eq: (Prim Ref [:: e] t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e' ef' h' bt' a' ht hin [] h1 h2; subst.
by exists h', bt', a'; split=> //=.
Qed.

Lemma type_infer_deref: forall cenv Gamma Sigma e ef t t',
type_expr cenv Gamma Sigma (Prim Deref [:: e] t) ef t' ->
(exists pt ef', t = (get_data_type pt) /\ 
                t' = (get_data_type pt) /\
                type_expr cenv Gamma Sigma e ef' (Ptrtype pt)).
Proof.
move=> cenv Gamma Sigma e ef t t'.
move eq: (Prim Deref [:: e] t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e' ef' pt h ht1 hin1 h1 [] h2 h3; subst.
by exists pt, ef'; split=>//=. 
Qed.

Lemma type_infer_massgn: forall cenv Gamma Sigma e e' ef t t',
type_expr cenv Gamma Sigma (Prim Massgn [:: e; e'] t) ef t' ->
(t = tunit /\ t' = tunit /\
 (exists pt ef1 ef2, type_expr cenv Gamma Sigma e ef1 (Ptrtype pt) /\ 
                     is_option_ptr_type pt = false /\ 
                     type_expr cenv Gamma Sigma e' ef2 (get_data_type pt))). 
Proof.
move=> cenv Gamma Sigma e e' ef t t'.
move eq: (Prim Massgn [:: e; e'] t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e1 e2 h pt ef1 ef2 ht hin ho ht' hin' [] h1 h2 h3; subst; split=> //=.
split=> //=. by exists pt, ef1, ef2.
Qed.

Lemma type_infer_notbool : forall cenv Gamma Sigma e ef t t',
type_expr cenv Gamma Sigma (Prim (Uop Cop.Onotbool) (e::nil) t) ef t' ->
t = (Vtype Tbool) /\ t' = (Vtype Tbool) /\
exists ef', type_expr cenv Gamma Sigma e ef' (Vtype Tbool).
Proof.
move=> cenv Gamma Sigma e ef t t'.
move eq: (Prim (Uop Cop.Onotbool) (e::nil) t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e1 ef1 ht hin [] h1 h2; split=> //=; subst.
split=> //=. by exists ef1.
Qed.

Lemma type_infer_notint : forall cenv Gamma Sigma e ef t t',
type_expr cenv Gamma Sigma (Prim (Uop Cop.Onotint) (e::nil) t) ef t' ->
((is_primint t || is_primlong t)  \/ (is_primint t' || is_primlong t')) /\
exists ef', type_expr cenv Gamma Sigma e ef' t.
Proof.
move=> cenv Gamma Sigma e ef t t'.
move eq: (Prim (Uop Cop.Onotint) (e::nil) t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e1 ef1 t1 heq ht hin [] h1 h2; split=> //=; subst.
+ by left. by exists ef1.
Qed.

Lemma type_infer_neg : forall cenv Gamma Sigma e ef t t',
type_expr cenv Gamma Sigma (Prim (Uop Cop.Oneg) (e::nil) t) ef t' ->
((is_primint t || is_primlong t)  \/ (is_primint t' || is_primlong t')) /\
exists ef', type_expr cenv Gamma Sigma e ef' t.
Proof.
move=> cenv Gamma Sigma e ef t t'.
move eq: (Prim (Uop Cop.Oneg) (e::nil) t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e1 ef1 t1 heq ht hin [] h1 h2; split=> //=; subst.
+ by left. by exists ef1.
Qed.

Lemma type_infer_add : forall cenv Gamma Sigma e e' ef t t',
type_expr cenv Gamma Sigma (Prim (Bop Cop.Oadd) (e::e'::nil) t) ef t' ->
((is_primint t || is_primlong t)  \/ (is_primint t' || is_primlong t')) /\
exists ef1 ef2, type_expr cenv Gamma Sigma e ef1 t /\ type_expr cenv Gamma Sigma e' ef2 t.
Proof.
move=> cenv Gamma Sigma e e' ef t t'.
move eq: (Prim (Bop Cop.Oadd) (e::e'::nil) t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e1 ef1 ef2 t1 e2 heq ht1 hin1 ht2 hin2 [] h1 h2 h3; split=> //=; subst. 
+ by left.
by exists ef1, ef2.
Qed.

Lemma type_infer_sub : forall cenv Gamma Sigma e e' ef t t',
type_expr cenv Gamma Sigma (Prim (Bop Cop.Osub) (e::e'::nil) t) ef t' ->
((is_primint t || is_primlong t)  \/ (is_primint t' || is_primlong t')) /\
exists ef1 ef2, type_expr cenv Gamma Sigma e ef1 t /\ type_expr cenv Gamma Sigma e' ef2 t.
Proof.
move=> cenv Gamma Sigma e e' ef t t'.
move eq: (Prim (Bop Cop.Osub) (e::e'::nil) t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e1 ef1 ef2 t1 e2 heq ht1 hin1 ht2 hin2 [] h1 h2 h3; split=> //=; subst. 
+ by left.
by exists ef1, ef2.
Qed.

Lemma type_infer_mul : forall cenv Gamma Sigma e e' ef t t',
type_expr cenv Gamma Sigma (Prim (Bop Cop.Omul) (e::e'::nil) t) ef t' ->
((is_primint t || is_primlong t)  \/ (is_primint t' || is_primlong t')) /\
exists ef1 ef2, type_expr cenv Gamma Sigma e ef1 t /\ type_expr cenv Gamma Sigma e' ef2 t.
Proof.
move=> cenv Gamma Sigma e e' ef t t'.
move eq: (Prim (Bop Cop.Omul) (e::e'::nil) t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e1 ef1 ef2 t1 e2 heq ht1 hin1 ht2 hin2 [] h1 h2 h3; split=> //=; subst. 
+ by left.
by exists ef1, ef2.
Qed.

Lemma type_infer_div : forall cenv Gamma Sigma e e' ef t t',
type_expr cenv Gamma Sigma (Prim (Bop Cop.Odiv) (e::e'::nil) t) ef t' ->
((is_primint t || is_primlong t)  \/ (is_primint t' || is_primlong t')) /\
exists ef1 ef2, type_expr cenv Gamma Sigma e ef1 t /\ type_expr cenv Gamma Sigma e' ef2 t.
Proof.
move=> cenv Gamma Sigma e e' ef t t'.
move eq: (Prim (Bop Cop.Odiv) (e::e'::nil) t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e1 ef1 ef2 t1 e2 heq ht1 hin1 ht2 hin2 [] h1 h2 h3; split=> //=; subst. 
+ by left.
by exists ef1, ef2.
Qed.

Lemma type_infer_mod : forall cenv Gamma Sigma e e' ef t t',
type_expr cenv Gamma Sigma (Prim (Bop Cop.Omod) (e::e'::nil) t) ef t' ->
((is_primint t || is_primlong t)  \/ (is_primint t' || is_primlong t')) /\
exists ef1 ef2, type_expr cenv Gamma Sigma e ef1 t /\ type_expr cenv Gamma Sigma e' ef2 t.
Proof.
move=> cenv Gamma Sigma e e' ef t t'.
move eq: (Prim (Bop Cop.Omod) (e::e'::nil) t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e1 ef1 ef2 t1 e2 heq ht1 hin1 ht2 hin2 [] h1 h2 h3; split=> //=; subst. 
+ by left.
by exists ef1, ef2.
Qed.

Lemma type_infer_and : forall cenv Gamma Sigma e e' ef t t',
type_expr cenv Gamma Sigma (Prim (Bop Cop.Oand) (e::e'::nil) t) ef t' ->
((is_primint t || is_primlong t)  \/ (is_primint t' || is_primlong t')) /\
exists ef1 ef2, type_expr cenv Gamma Sigma e ef1 t /\ type_expr cenv Gamma Sigma e' ef2 t.
Proof.
move=> cenv Gamma Sigma e e' ef t t'.
move eq: (Prim (Bop Cop.Oand) (e::e'::nil) t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e1 ef1 ef2 t1 e2 heq ht1 hin1 ht2 hin2 [] h1 h2 h3; split=> //=; subst. 
+ by left.
by exists ef1, ef2.
Qed.

Lemma type_infer_or : forall cenv Gamma Sigma e e' ef t t',
type_expr cenv Gamma Sigma (Prim (Bop Cop.Oor) (e::e'::nil) t) ef t' ->
((is_primint t || is_primlong t)  \/ (is_primint t' || is_primlong t')) /\
exists ef1 ef2, type_expr cenv Gamma Sigma e ef1 t /\ type_expr cenv Gamma Sigma e' ef2 t.
Proof.
move=> cenv Gamma Sigma e e' ef t t'.
move eq: (Prim (Bop Cop.Oor) (e::e'::nil) t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e1 ef1 ef2 t1 e2 heq ht1 hin1 ht2 hin2 [] h1 h2 h3; split=> //=; subst. 
+ by left.
by exists ef1, ef2.
Qed.

Lemma type_infer_xor : forall cenv Gamma Sigma e e' ef t t',
type_expr cenv Gamma Sigma (Prim (Bop Cop.Oxor) (e::e'::nil) t) ef t' ->
((is_primint t || is_primlong t)  \/ (is_primint t' || is_primlong t')) /\
exists ef1 ef2, type_expr cenv Gamma Sigma e ef1 t /\ type_expr cenv Gamma Sigma e' ef2 t.
Proof.
move=> cenv Gamma Sigma e e' ef t t'.
move eq: (Prim (Bop Cop.Oxor) (e::e'::nil) t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e1 ef1 ef2 t1 e2 heq ht1 hin1 ht2 hin2 [] h1 h2 h3; split=> //=; subst. 
+ by left.
by exists ef1, ef2.
Qed.

Lemma type_infer_shl : forall cenv Gamma Sigma e e' ef t t',
type_expr cenv Gamma Sigma (Prim (Bop Cop.Oshl) (e::e'::nil) t) ef t' ->
((is_primint t || is_primlong t)  \/ (is_primint t' || is_primlong t')) /\
exists ef1 ef2, type_expr cenv Gamma Sigma e ef1 t /\ type_expr cenv Gamma Sigma e' ef2 t.
Proof.
move=> cenv Gamma Sigma e e' ef t t'.
move eq: (Prim (Bop Cop.Oshl) (e::e'::nil) t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e1 ef1 ef2 t1 e2 heq ht1 hin1 ht2 hin2 [] h1 h2 h3; split=> //=; subst. 
+ by left.
by exists ef1, ef2.
Qed.

Lemma type_infer_shr : forall cenv Gamma Sigma e e' ef t t',
type_expr cenv Gamma Sigma (Prim (Bop Cop.Oshr) (e::e'::nil) t) ef t' ->
((is_primint t || is_primlong t)  \/ (is_primint t' || is_primlong t')) /\
exists ef1 ef2, type_expr cenv Gamma Sigma e ef1 t /\ type_expr cenv Gamma Sigma e' ef2 t.
Proof.
move=> cenv Gamma Sigma e e' ef t t'.
move eq: (Prim (Bop Cop.Oshr) (e::e'::nil) t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e1 ef1 ef2 t1 e2 heq ht1 hin1 ht2 hin2 [] h1 h2 h3; split=> //=; subst. 
+ by left.
by exists ef1, ef2.
Qed.

Lemma type_infer_eq : forall cenv Gamma Sigma e e' ef t t',
type_expr cenv Gamma Sigma (Prim (Bop Cop.Oeq) (e::e'::nil) t) ef t' ->
t = Vtype Tbool /\ t' = Vtype Tbool /\
exists t ef1 ef2, type_expr cenv Gamma Sigma e ef1 t /\ type_expr cenv Gamma Sigma e' ef2 t 
/\ is_primint t || is_primlong t || is_primbool t.
Proof.
move=> cenv Gamma Sigma e e' ef t t'.
move eq: (Prim (Bop Cop.Oeq) (e::e'::nil) t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e1 ef1 ef2 t1 e2 heq ht1 hin1 ht2 hin2 [] h1 h2 h3; split=> //=; subst. 
split=> /=. + auto. by exists t1, ef1, ef2.
Qed.

Lemma type_infer_ne : forall cenv Gamma Sigma e e' ef t t',
type_expr cenv Gamma Sigma (Prim (Bop Cop.One) (e::e'::nil) t) ef t' ->
t = Vtype Tbool /\ t' = Vtype Tbool /\
exists t ef1 ef2, type_expr cenv Gamma Sigma e ef1 t /\ type_expr cenv Gamma Sigma e' ef2 t 
/\ is_primint t || is_primlong t || is_primbool t.
Proof.
move=> cenv Gamma Sigma e e' ef t t'.
move eq: (Prim (Bop Cop.One) (e::e'::nil) t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e1 ef1 ef2 t1 e2 heq ht1 hin1 ht2 hin2 [] h1 h2 h3; split=> //=; subst. 
split=> /=. + auto. by exists t1, ef1, ef2.
Qed.

Lemma type_infer_lt : forall cenv Gamma Sigma e e' ef t t',
type_expr cenv Gamma Sigma (Prim (Bop Cop.Olt) (e::e'::nil) t) ef t' ->
t = Vtype Tbool /\ t' = Vtype Tbool /\
exists t ef1 ef2, type_expr cenv Gamma Sigma e ef1 t /\ type_expr cenv Gamma Sigma e' ef2 t 
/\ is_primint t || is_primlong t.
Proof.
move=> cenv Gamma Sigma e e' ef t t'.
move eq: (Prim (Bop Cop.Olt) (e::e'::nil) t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e1 ef1 ef2 t1 e2 heq ht1 hin1 ht2 hin2 [] h1 h2 h3; split=> //=; subst. 
split=> /=. + auto. by exists t1, ef1, ef2.
Qed.

Lemma type_infer_gt : forall cenv Gamma Sigma e e' ef t t',
type_expr cenv Gamma Sigma (Prim (Bop Cop.Ogt) (e::e'::nil) t) ef t' ->
t = Vtype Tbool /\ t' = Vtype Tbool /\
exists t ef1 ef2, type_expr cenv Gamma Sigma e ef1 t /\ type_expr cenv Gamma Sigma e' ef2 t 
/\ is_primint t || is_primlong t.
Proof.
move=> cenv Gamma Sigma e e' ef t t'.
move eq: (Prim (Bop Cop.Ogt) (e::e'::nil) t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e1 ef1 ef2 t1 e2 heq ht1 hin1 ht2 hin2 [] h1 h2 h3; split=> //=; subst. 
split=> /=. + auto. by exists t1, ef1, ef2.
Qed.

Lemma type_infer_le : forall cenv Gamma Sigma e e' ef t t',
type_expr cenv Gamma Sigma (Prim (Bop Cop.Ole) (e::e'::nil) t) ef t' ->
t = Vtype Tbool /\ t' = Vtype Tbool /\
exists t ef1 ef2, type_expr cenv Gamma Sigma e ef1 t /\ type_expr cenv Gamma Sigma e' ef2 t 
/\ is_primint t || is_primlong t.
Proof.
move=> cenv Gamma Sigma e e' ef t t'.
move eq: (Prim (Bop Cop.Ole) (e::e'::nil) t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e1 ef1 ef2 t1 e2 heq ht1 hin1 ht2 hin2 [] h1 h2 h3; split=> //=; subst. 
split=> /=. + auto. by exists t1, ef1, ef2.
Qed.


Lemma type_infer_ge : forall cenv Gamma Sigma e e' ef t t',
type_expr cenv Gamma Sigma (Prim (Bop Cop.Oge) (e::e'::nil) t) ef t' ->
t = Vtype Tbool /\ t' = Vtype Tbool /\
exists t ef1 ef2, type_expr cenv Gamma Sigma e ef1 t /\ type_expr cenv Gamma Sigma e' ef2 t 
/\ is_primint t || is_primlong t.
Proof.
move=> cenv Gamma Sigma e e' ef t t'.
move eq: (Prim (Bop Cop.Oge) (e::e'::nil) t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e1 ef1 ef2 t1 e2 heq ht1 hin1 ht2 hin2 [] h1 h2 h3; split=> //=; subst. 
split=> /=. + auto. by exists t1, ef1, ef2.
Qed.

Lemma type_infer_bind: forall cenv Gamma Sigma e x t e' t' ef t'',
type_expr cenv Gamma Sigma (Bind x t e e' t') ef t'' ->
(t'' = t' /\
exists ef' ef'', type_expr cenv Gamma Sigma e ef'' t /\
                 type_expr cenv (extend_context Gamma x t) Sigma e' ef' t').
Proof.
move=> cenv Gamma Sigma e x t e' t' ef t''.
move eq:(Bind x t e e' t')=> rv ht. elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' x' t1 e1 e2 t2 ef1 ef' ht1 hin ht2 hin'
       [] h1 h2 h3 h4 h5; subst; split=> //=. by exists ef', ef1.
Qed.

Lemma type_infer_cond: forall cenv Gamma Sigma e1 e2 e3 t ef' t',
type_expr cenv Gamma Sigma (Cond e1 e2 e3 t) ef' t' ->
t' = t /\
exists ef1 ef2, type_expr cenv Gamma Sigma e1 ef1 (Vtype Tbool) /\
                type_expr cenv Gamma Sigma e2 ef2 t /\
                type_expr cenv Gamma Sigma e3 ef2 t.
Proof.
move=> cenv Gamma Sigma e1 e2 e3 t ef' t'.
move eq: (Cond e1 e2 e3 t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e1' e2' e3' t1 ef1 ef2 ht1 hin1
       ht2 hin2 ht3 hin3 [] h1 h2 h3 h4; subst; split=> //=.
by exists ef1, ef2.
Qed.

Lemma type_infer_unit: forall cenv Gamma Sigma ef t t',
type_expr cenv Gamma Sigma (Unit t) ef t' ->
t = tunit /\ t' = tunit.
Proof.
move=> cenv Gamma Sigma ef t t'. move eq: (Unit t)=> rv ht.
elim: ht eq=> //=. by move=> cenv' Gamma' Sigma' [] h; subst.
Qed.

Lemma type_infer_addr: forall cenv Gamma Sigma l ofs ef t t',
type_expr cenv Gamma Sigma (Addr l ofs t) ef t' ->
(exists h bt a, t = Ptrtype (Reftype h bt a) /\ 
                t'= Ptrtype (Reftype h bt a) /\ 
                PTree.get l.(lname) Sigma = Some (Ptrtype (Reftype h bt a))).
Proof.
move=> cenv Gamma Sigma l ofs ef t t'.
move eq: (Addr l ofs t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' l' ofs' h' bt' a' hs [] h1 h2; subst.
by exists h', bt', a'.
Qed.

Lemma type_infer_sinit : forall cenv Gamma Sigma x ids es t efs t',
type_expr cenv Gamma Sigma (Sinit x ids es t) efs t' ->
exists h id a a' efs bts co cts, 
t = (Ptrtype (Reftype h (Bstruct id a) a')) /\ t' = (Ptrtype (Reftype h (Bstruct id a) a')) /\
type_exprs cenv Gamma Sigma es efs bts /\ PTree.get id cenv = Some co /\ 
type_of_members (combine (map Ctypes.attr_of_type (transBeePL_types transBeePL_type bts)) ids) 
(bmembers_cmembers co.(co_members)) = OK cts /\ trans_ctypes_btypes trans_ctype_btype cts = OK bts.
Proof.
move=> cenv Gamma Sigma x ids es t efs t'.
move eq: (Sinit x ids es t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' x' es' efs' h id a a' co ids' cts bts htes hc htm ht [] h1 h2 h3 h4; subst. 
by exists h, id, a, a', efs', bts, co, cts; split=> //=.
Qed.

Lemma type_infer_sfield : forall cenv Gamma Sigma e x t ef t',
type_expr cenv Gamma Sigma (Sfield e x t) ef t' ->
exists id a co ct ef te, 
t = (Stype id a) /\ t' = (Ptrtype (Reftype mem_ident (Bstruct id a) noattr)) /\
type_expr cenv Gamma Sigma e ef te ->
PTree.get id cenv = Some co /\ 
Ctyping.type_of_member a x (bmembers_cmembers co.(co_members)) = OK ct /\
trans_ctype_btype ct = OK t.            
Proof.
move=> cenv Gamma Sigma e x t ef t'.
move eq: (Sfield e x t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e' x' id' a te ef' co ct bt ht hi hi' ho hct ht' [] h1 h2 h3; subst.
by exists id', a, co, ct, ef', te; split=> //=.
Qed.

Lemma type_infer_for : forall cenv Gamma Sigma e1 e2 d e t ef t', 
type_expr cenv Gamma Sigma (For e1 e2 d e t) ef t' ->
exists te t1 t2 ef1 ef2 efe fv1 fv2 fv, 
type_expr cenv Gamma Sigma e1 ef1 t1 /\ type_expr cenv Gamma Sigma e2 ef2 t2 /\
type_expr cenv Gamma Sigma e efe te /\ t = te /\ t' = te /\
(is_primint t || is_primlong t) /\ (is_primint t' || is_primlong t') /\
free_variables e1 = fv1 /\ free_variables e2 = fv2 /\ free_variables e = fv /\
disjoint_vars fv fv1 /\ disjoint_vars fv fv2.
Proof.
move=> cenv Gamma Sigma e1 e2 d e t ef t'.
move eq: (For e1 e2 d e t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e1' e2' d' e' ef1 t1 ef2 t2 fv1 fv2 fv ef' t'' ht1 hin ht2 hin'.
move=> ht3 hin1 heq heq' hf hf' hf1 hd1 hd2 [] h1 h2 h3 h4 h5; subst.
by exists t'', t1, t2, ef1, ef2, ef', (free_variables e1'), (free_variables e2'), (free_variables e').
Qed.


Lemma type_infer_none : forall cenv Gamma Sigma t ef t',
type_expr cenv Gamma Sigma (Enone t) ef t' ->
exists t1, t = (Ptrtype t1) /\ t' = (Ptrtype t1) /\ is_option_ptr_type t1.
Proof.
move=> cenv Gamma Sigma t ef t'.
move eq: (Enone t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' pt ho [] h1; subst.
by exists pt.
Qed.

Lemma type_infer_some : forall cenv Gamma Sigma t e ef t',
type_expr cenv Gamma Sigma (Esome e t) ef t' ->
exists t1 ef' te, t = (Ptrtype t1) /\ t' = (Ptrtype t1) /\ is_option_ptr_type t1 /\
type_expr cenv Gamma Sigma e ef' te.
Proof.
move=> cenv Gamma Sigma t e ef t'.
move eq: (Esome e t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' pt e' te ef' hte hi ho h1 [] h2 h3; subst.
by exists pt, ef', (get_data_type pt).
Qed.

Lemma type_infer_match : forall cenv Gamma Sigma t e ef ps es t',
type_expr cenv Gamma Sigma (Match e ps es t) ef t' ->
exists fvs efe te efs ts, t = (hd tunit ts) /\ t' = (hd tunit ts) /\
get_patterns_var ps = fvs /\ type_expr cenv Gamma Sigma e efe te /\ all_eq_types ts /\
type_exprs cenv (extends_context Gamma fvs (construct_list_type (hd tunit ts) (length fvs))) Sigma es efs ts.
Proof.
move=> cenv Gamma Sigma t e ef ps es t'.
move eq: (Match e ps es t)=> rv ht.
elim: ht eq=> //=.
move=> cenv' Gamma' Sigma' e' ef' te ps' es' efs ts fvs hg hte hi hts ho hall [] h1 h2 h3 h4; subst.
by exists (get_patterns_var ps'), ef', te, efs, ts.
Qed.

Lemma type_val_reflx : forall cenv Gamma Sigma v t ef t',
type_expr cenv Gamma Sigma (Val v t) ef t' -> 
t = t'.
Proof.
move=> cenv Gamma Sigma v t ef t'. move eq: (Val v t)=> rv ht. 
elim: ht eq=> //=.  
+ by move=> cenv' Gamma' Sigma' [] h; subst.
+ by move=> cenv' Gamma' Sigma' b [] h h'; subst.
+ by move=> cenv' Gamma' Sigma' i sz s a [] h h'; subst.
+ by move=> cenv' Gamma' Sigma' i s a [] h h'; subst.
+ by move=> cenv' Gamma' Sigma' l ofs h t'' a hs [] h1 h2; subst.
by move=> cenv' Gamma' Sigma' o pt [] h1 h2.
Qed.

Lemma type_expr_exprs_deterministic: 
(forall cenv Gamma Sigma es efs ts efs' ts', type_exprs cenv Gamma Sigma es efs ts ->
                                        type_exprs cenv Gamma Sigma es efs' ts' ->
                                        ts = ts') /\
(forall cenv Gamma Sigma e ef t ef' t', type_expr cenv Gamma Sigma e ef t ->
                                        type_expr cenv Gamma Sigma e ef' t' ->
                                        t = t').
Proof.
suff : (forall cenv Gamma Sigma es efs ts, type_exprs cenv Gamma Sigma es efs ts ->
                          forall efs' ts', type_exprs cenv Gamma Sigma es efs' ts' ->
                                                       ts = ts') /\
       (forall cenv Gamma Sigma e ef t, type_expr cenv Gamma Sigma e ef t ->
                         forall ef' t', type_expr cenv Gamma Sigma e ef' t' ->
                                                  t = t').
+ move=> [] ih ih'. split=> //=.
  + move=> cenv Gamma Sigma es efs ts efs' ts' hes hes'. 
    by move: (ih cenv Gamma Sigma es efs ts hes efs' ts' hes').
  move=> cenv Gamma Sigma e ef t ef' t' he he'.
  by move: (ih' cenv Gamma Sigma e ef t he ef' t' he').
apply type_exprs_type_expr_ind_mut => //=.
(*+ move=> cenv Gamma Sigma ef' t' ht; inversion ht; subst; auto.
  by have [h1 h2] := type_infer_vunit cenv Gamma Sigma ef' tunit t' ht.
+ move=> cenv Gamma Sigma i sz s a ef' t' ht; inversion ht; subst; auto.
  have := type_infer_int cenv Gamma Sigma i ef' (Vtype (Tint sz s a)) t' ht. 
  by move=> [] sz' [] s' [] a' [] h1 h2; subst.
+ move=> cenv Gamma Sigma i s a ef' t' ht; inversion ht; subst; auto.
  have := type_infer_long cenv Gamma Sigma i ef' (Vtype (Tlong s a)) t' ht.
  by move=> [] s' [] a' [] h1 h2; subst.
+ move=> cenv Gamma Sigma l ofs h t a hs ef' t' ht; inversion ht; subst; auto.
  have := type_infer_loc cenv Gamma Sigma l ofs ef' (Ptrtype (Reftype h t a)) t' ht.
  by move=> [] h' [] bt [] a' [] h1 [] h2 h3; subst.
+ move=> cenv Gamma Sigma x t ht ef' t' ht'; subst; inversion ht'; subst; auto.
  by have [h1 h2]:= type_infer_var cenv Gamma Sigma x t ef' t' ht'.
+ move=> cenv Gamma Sigma sz s a i ef' t' ht; subst; inversion ht; subst; auto.
  have := type_infer_consti cenv Gamma Sigma i ef' (Vtype (Tint sz s a)) t' ht.
  by move=> [] sz' [] s' [] a' [] h1 h2; subst.
+ move=> cenv Gamma Sigma s a i ef' t' ht; subst; inversion ht; subst; auto.
  have := type_infer_constl cenv Gamma Sigma i ef' (Vtype (Tlong s a)) t' ht.
  by move=> [] s' [] a' [] h1 h2; subst.
+ move=> cenv Gamma Sigma ef' t' ht; inversion ht; subst; auto.
  have := type_infer_constu cenv Gamma Sigma ef' tunit t' ht.
  by move=> [] h h'.
+ move=> cenv Gamma Sigma e es rt efs ts ef efs' hte hin htes hin' ef' t ef'' t' ht; 
  inversion ht; subst; auto.
  have := type_infer_app cenv Gamma Sigma.
  have [h [ts'] [ef1 [efs1] [] ht' [efs'' hts]]]:= type_infer_app cenv Gamma Sigma e es rt ef' t ht.
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
Qed.*) Admitted.

Lemma type_rel_typeof : forall cenv Gamma Sigma e ef t,
type_expr cenv Gamma Sigma e ef t ->
typeof_expr e = t.
Proof.
by move=> cenv Gamma Sigma e ef t ht; elim: ht=> //=.
Qed.

(* Complete me : easy *)
Lemma type_rel_typeof_val : forall cenv Gamma Sigma v ef t t',
type_expr cenv Gamma Sigma (Val v t) ef t' ->
typeof_value v t.
Proof.
Admitted.

Lemma eq_type_rel : forall v t t',
eq_type t t' ->
wtypeof_value v (wtype_of_type t') ->
wtypeof_value v (wtype_of_type t).
Proof.
(*move=> v t t'. case: t=> //=.
+ move=> p. case: t' p=> //= p'.
  case:p=> //=.
  + by case: p'=> //=.
  + by case: p'=> //=.
  by case: p'=> //=.
+ by case: t'=> //=. 
by case: t'=> //=.
Qed.*) Admitted.

(* Complete Me: Easy *)
(* There always exists a C type for BeePL type which is 
   inferred from the typing rules. *)
Lemma well_typed_success: 
(forall cenv Gamma Sigma es efs ts, type_exprs cenv Gamma Sigma es efs ts ->
                               exists cts, transBeePL_types transBeePL_type ts = cts) /\
(forall cenv Gamma Sigma e ef t, type_expr cenv Gamma Sigma e ef t ->
                            exists ct, transBeePL_type t = ct).
Proof.
apply type_exprs_type_expr_ind_mut=> //=.
Admitted.

(* Compelete Me: Easy *)
Lemma typed_well_formed_value : forall cenv Gamma Sigma v t ef, 
type_expr cenv Gamma Sigma (Val v t) ef t ->
well_formed_value v t.
Proof.
Admitted.

Lemma get_type_fundef : forall cenv Gamma Sigma (bge: BeePL.genv) fd l o ef te ts efs rt,
type_expr cenv Gamma Sigma (Val (Vloc l o) te) ef te -> 
eq_type te (Ptrtype (Fptype ts efs rt)) || eq_type te (Ftype ts efs rt) ->
Genv.find_funct bge (trans_bvalue_cvalue (Vloc l o)) = Some (Internal fd) ->
BeePL.type_of_fundef (Internal fd) = Ftype (unzip2 fd.(fn_args)) (get_effect_fundef (Internal fd)) (get_rt_fundef (Internal fd)).
Proof.
move=> cenv Gamma Sigma bge fd l o ef te ts efs rt hte hteq hg. by case:fd hg=> //=.
Qed.

