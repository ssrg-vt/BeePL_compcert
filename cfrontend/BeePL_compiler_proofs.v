Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Ctypesdefs Smallstep SimplExpr.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL_values BeePL BeePL_typesystem Csyntax Csem Clight Globalenvs BeePL_Csyntax.
Require Import Initializersproof Cstrategy BeePL_auxlemmas Coqlib Errors.


From mathcomp Require Import all_ssreflect. 

(***** Correctness proof for the Csyntax generation from BeePL using BeePL compiler *****)

Section specifications.

Variable cenv : Csem.env.

(* The first function_ctx here represents the one that is input into the function,
   while the second one represents the returned context *)
Inductive sim_bexpr_cexpr : vmap -> BeePL.expr -> function_ctx -> Csyntax.expr -> function_ctx -> Prop :=
| sim_val : forall le ctx v t ct, 
            transBeePL_type t = ct ->
            sim_bexpr_cexpr le (BeePL.Val v t) ctx (Csyntax.Eval (trans_bvalue_cvalue v) ct) ctx
| sim_var : forall le ctx x t ct,
            transBeePL_type t = ct ->
            sim_bexpr_cexpr le (BeePL.Var x t) ctx (Csyntax.Evar x ct) ctx
| sim_const_int : forall le ctx i t ct,
                  transBeePL_type t = ct ->
                  sim_bexpr_cexpr le (BeePL.Const (ConsInt i) t) ctx (Csyntax.Eval (Values.Vint i) ct) ctx
| sim_const_long : forall le ctx i t ct,
                   transBeePL_type t = ct ->
                   sim_bexpr_cexpr le (BeePL.Const (ConsLong i) t) ctx (Csyntax.Eval (Values.Vlong i) ct) ctx
| sim_const_unit : forall le ctx  t ct,
                   transBeePL_type t = ct ->
                   sim_bexpr_cexpr le (BeePL.Const ConsUnit t) ctx (Csyntax.Eval (Values.Vint (Int.repr 0)) ct) ctx
| sim_app : forall le ctx ctx' ctx'' e es t ce ces ct,
            sim_bexpr_cexpr le e ctx ce ctx' ->
            sim_bexprs_cexprs le es ctx' ces ctx'' ->
            transBeePL_type t = ct ->  
            sim_bexpr_cexpr le (BeePL.App e es t) ctx (Csyntax.Ecall ce ces ct) ctx''
| sim_prim_ref : forall le ctx ctx' ctx'' es t ct ces id str pty cpty g g' i g'' i',
                sim_bexprs_cexprs le es ctx ces ctx' ->
                transBeePL_type t = ct ->
                fresh_ident (List.map unzip_ident ctx') max_fresh g = Res (id, str) g' i ->
                length es = 1%nat ->
                ref_to_prim t g' = Res pty g'' i' ->
                transBeePL_type (Ptype pty) = cpty ->
                (id, (Ptype pty), str) :: ctx' = ctx'' ->
                sim_bexpr_cexpr le (BeePL.Prim Ref es t) ctx
                           (Csyntax.Ecomma 
                              (Csyntax.Eassign (Csyntax.Evar id cpty) 
                                             (hd default_expr (exprlist_list_expr ces)) 
                                             cpty) 
                              (Csyntax.Eaddrof (Csyntax.Evar id ct) ct)
                              ct) ctx''
| sim_prim_deref : forall le ctx ctx' es t ct ces,
                   sim_bexprs_cexprs le es ctx ces ctx' ->
                   transBeePL_type t = ct ->
                   sim_bexpr_cexpr le (BeePL.Prim Deref es t) ctx (Csyntax.Evalof (hd default_expr (exprlist_list_expr ces)) ct) ctx'
| sim_prim_massgn : forall le ctx ctx' es t ct ces,
                    sim_bexprs_cexprs le es ctx ces ctx' ->
                    transBeePL_type t = ct ->
                    sim_bexpr_cexpr le (BeePL.Prim Massgn es t) ctx
                                   (Csyntax.Eassign 
                                      (hd default_expr (exprlist_list_expr ces))
                                      (hd default_expr (tl (exprlist_list_expr ces)))
                                      ct) ctx'
| sim_prim_run : forall le ctx es h t,
                 sim_bexpr_cexpr le (BeePL.Prim (Run h) es t) ctx (Eval (Values.Vundef) Tvoid) ctx
| sim_prim_uop : forall le ctx ctx' o es t ct ces, 
                sim_bexprs_cexprs le es ctx ces ctx' ->
                transBeePL_type t = ct ->
                sim_bexpr_cexpr le (BeePL.Prim (Uop o) es t) ctx
                               (Csyntax.Eunop o
                                  (hd default_expr (exprlist_list_expr ces))
                                  ct) ctx'
| sim_prim_bop_undef : forall le ctx o es t ct v g g' i,
                 transBeePL_type t = ct ->
                 return_czero ct g = Res v g' i ->
                 sim_bexpr_cexpr le (BeePL.Prim (Bop o) es t) ctx (Eval v ct) ctx
| sim_prim_bop : forall le ctx ctx' o es t ct ces,
                 sim_bexprs_cexprs le es ctx ces ctx' ->
                 transBeePL_type t = ct ->
                 sim_bexpr_cexpr le (BeePL.Prim (Bop o) es t) ctx
                                (Csyntax.Ebinop o
                                   (hd default_expr (exprlist_list_expr ces))
                                   (hd default_expr (tl (exprlist_list_expr ces)))
                                   ct) ctx'
| sim_bind : forall le ctx ctx' ctx'' x t e e' t' ct ct' ce ce',
             transBeePL_type t = ct ->
             sim_bexpr_cexpr le e ctx ce ctx' ->
             sim_bexpr_cexpr le e' ctx' ce' ctx'' ->
             transBeePL_type t' = ct ->
             sim_bexpr_cexpr le (BeePL.Bind x t e e' t') ctx (Csyntax.Ecomma (Eassign (Csyntax.Evar x ct) ce ct) ce' ct') ctx''
| sim_cond : forall le ctx ctx' ctx'' ctx''' e1 e2 e3 t ct ce1 ce2 ce3,
             sim_bexpr_cexpr le e1 ctx ce1 ctx' ->
             sim_bexpr_cexpr le e2 ctx' ce2 ctx'' ->
             sim_bexpr_cexpr le e3 ctx'' ce3 ctx''' ->
             transBeePL_type t = ct ->
             sim_bexpr_cexpr le (BeePL.Cond e1 e2 e3 t) ctx (Csyntax.Econdition ce1 ce2 ce3 ct) ctx'''
| sim_unit : forall le ctx t ct, (* Fix me *)
             transBeePL_type t = ct ->
             sim_bexpr_cexpr le (BeePL.Unit t) ctx (Csyntax.Eval (trans_bvalue_cvalue Vunit) ct) ctx
| sim_addr : forall le ctx l ofs t ct,
             transBeePL_type t = ct ->
             sim_bexpr_cexpr le (BeePL.Addr l ofs t) ctx (Csyntax.Eloc l.(lname) ofs l.(lbitfield) ct) ctx
| sim_hexpr : forall le ctx h e t, (* Fix me *)
              sim_bexpr_cexpr le (BeePL.Hexpr h e t) ctx (Eval (Values.Vundef) Tvoid) ctx
| sim_eapp : forall le ctx ctx' ef ts es t cef cts ces ct,
             befunction_to_cefunction ef = cef ->
             transBeePL_types transBeePL_type ts = cts ->  
             transBeePL_type t = ct ->
             sim_bexprs_cexprs le es ctx ces ctx' ->
             sim_bexpr_cexpr le (BeePL.Eapp ef ts es t) ctx
                            (Csyntax.Ebuiltin cef cts ces ct) ctx'
| sim_sfield : forall le ctx ctx' e x t ce ct,
               transBeePL_type t = ct ->
               sim_bexpr_cexpr le e ctx ce ctx' ->
               sim_bexpr_cexpr le (BeePL.Sfield e x t) ctx (Csyntax.Efield (Evalof ce (transBeePL_type (typeof_expr e))) x ct) ctx'
(*| sim_for : forall le x e1 e2 d e t,
            sim_bexpr_cexpr le (BeePL.For x e1 e2 d e t) ... *)
with sim_bexprs_cexprs : vmap -> list BeePL.expr -> function_ctx -> Csyntax.exprlist -> function_ctx -> Prop :=
| sim_nil : forall le ctx,
            sim_bexprs_cexprs le [::] ctx Enil ctx
| sim_cons : forall le ctx ctx' ctx'' e es ce ces,
             sim_bexpr_cexpr le e ctx ce ctx' ->
             sim_bexprs_cexprs le es ctx' ces ctx'' ->
             sim_bexprs_cexprs le (e :: es) ctx (Econs ce ces) ctx''.
 
Scheme sim_bexpr_cexpr_ind_mut := Induction for sim_bexpr_cexpr Sort Prop
with sim_bexprs_cexprs_ind_mut := Induction for sim_bexprs_cexprs Sort Prop.
Combined Scheme sim_bexprs_cexprs_bexpr_cexpr_ind_mut from sim_bexpr_cexpr_ind_mut, sim_bexprs_cexprs_ind_mut.

Inductive sim_bexpr_cstmt : vmap -> BeePL.expr -> function_ctx -> Csyntax.statement -> function_ctx -> Prop :=
| sim_val_st : forall le ctx v t ct cv,
               transBeePL_type t = ct ->
               trans_bvalue_cvalue v = cv ->
               sim_bexpr_cstmt le (BeePL.Val v t) ctx
                                  (Csyntax.Sreturn (Some (Eval (trans_bvalue_cvalue v) ct))) ctx
| sim_var_st : forall le ctx x t ct,
                  transBeePL_type t = ct ->
                  sim_bexpr_cstmt le (BeePL.Var x t) ctx (Csyntax.Sreturn (Some (Evalof (Csyntax.Evar x ct) ct))) ctx
| sim_const_int_st : forall le ctx i t ct,
                     transBeePL_type t = ct ->
                     sim_bexpr_cstmt le (BeePL.Const (ConsInt i) t) ctx
                                        (Csyntax.Sreturn (Some (Evalof (Csyntax.Eval (Values.Vint i) ct) ct))) ctx
| sim_const_long_st : forall le ctx i t ct,
                      transBeePL_type t = ct ->
                      sim_bexpr_cstmt le (BeePL.Const (ConsLong i) t) ctx
                                          (Csyntax.Sreturn (Some (Evalof (Csyntax.Eval (Values.Vlong i) ct) ct))) ctx
| sim_const_unit_st : forall le ctx t ct,
                      transBeePL_type t = ct ->
                      sim_bexpr_cstmt le (BeePL.Const ConsUnit t) ctx
                                         (Csyntax.Sreturn (Some (Evalof (Csyntax.Eval (Values.Vint (Int.repr 0)) ct) ct))) ctx
| sim_const_bool_true_st : forall le ctx b t ct,
                           transBeePL_type t = ct ->
                           eqb b true ->
                           sim_bexpr_cstmt le (BeePL.Const (ConsBool b) t) ctx 
                                              (Csyntax.Sreturn (Some (Evalof (Csyntax.Eval (Values.Vint (Int.repr 1)) ct) ct))) ctx
| sim_const_bool_false_st : forall le ctx b t ct,
                            transBeePL_type t = ct ->
                            eqb b false ->
                            sim_bexpr_cstmt le (BeePL.Const (ConsBool b) t) ctx 
                                               (Csyntax.Sreturn (Some (Evalof (Csyntax.Eval (Values.Vint (Int.repr 0)) ct) ct))) ctx
| sim_app_st : forall le ctx ctx' ctx'' e es t ce ces ct,
               transBeePL_type t = ct ->
               sim_bexprs_cexprs le es ctx ces ctx' ->
               sim_bexpr_cexpr le e ctx' ce ctx'' ->
               sim_bexpr_cstmt le (BeePL.App e es t) ctx
                              (Csyntax.Sdo (Csyntax.Ecall ce ces ct)) ctx''
| sim_prim_ref_st : forall le ctx ctx' ctx'' es t ct ces id str pty cpty g g' i g'' i',
                   transBeePL_type t = ct ->
                   sim_bexprs_cexprs le es ctx ces ctx' ->
                   fresh_ident (List.map unzip_ident ctx') max_fresh g = Res (id, str) g' i ->
                   length es = 1%nat ->
                   ref_to_prim t g' = Res pty g'' i' ->
                   transBeePL_type (Ptype pty) = cpty ->
                   (id, (Ptype pty), str) :: ctx' = ctx'' ->
                   sim_bexpr_cstmt le (BeePL.Prim Ref es t) ctx
                                  (Csyntax.Ssequence
                                       (Sdo (Csyntax.Eassign (Csyntax.Evar id cpty) (hd default_expr (exprlist_list_expr ces)) cpty))
                                       (Sdo (Csyntax.Eaddrof (Csyntax.Evar id ct) ct))) ctx''
| sim_prim_deref_st : forall le ctx ctx' es t ct ces,
                     transBeePL_type t = ct ->
                     sim_bexprs_cexprs le es ctx ces ctx' ->
                     sim_bexpr_cstmt le (BeePL.Prim Deref es t) ctx (Sdo (Csyntax.Evalof (hd default_expr (exprlist_list_expr ces)) ct)) ctx'
| sim_prim_massgn_st : forall le ctx ctx' es t ces ct,
                       transBeePL_type t = ct ->
                       sim_bexprs_cexprs le es ctx ces ctx' ->
                       sim_bexpr_cstmt le (BeePL.Prim Massgn es t) ctx (Sdo (Csyntax.Eassign
                                                                        (Csyntax.Ederef (hd default_expr (exprlist_list_expr ces)) (Csyntax.typeof (hd default_expr (exprlist_list_expr ces))))
                                                                        (hd default_expr (tl (exprlist_list_expr ces)))
                                                                        ct)) ctx'
| sim_prim_uop_st : forall le ctx ctx' o es t ct ces, 
                    transBeePL_type t = ct ->
                    sim_bexprs_cexprs le es ctx ces ctx' ->
                    sim_bexpr_cstmt le (BeePL.Prim (Uop o) es t) ctx (Sdo (Csyntax.Eunop o (hd default_expr (exprlist_list_expr ces)) ct)) ctx'
| sim_prim_bop_undef_st : forall le ctx o es t ct v g g' i,
                 transBeePL_type t = ct ->
                 return_czero ct g = Res v g' i ->
                 sim_bexpr_cstmt le (BeePL.Prim (Bop o) es t) ctx (Sdo (Eval v ct)) ctx
| sim_prim_bop_st : forall le ctx ctx' o es t ct ces,
                    transBeePL_type t = ct ->
                    sim_bexprs_cexprs le es ctx ces ctx' ->
                    sim_bexpr_cstmt le (BeePL.Prim (Bop o) es t) ctx (Sdo (Csyntax.Ebinop o 
                                                                      (hd default_expr (exprlist_list_expr ces))
                                                                      (hd default_expr (tl (exprlist_list_expr ces)))
                                                                      ct)) ctx'
| sim_prim_run_st : forall le ctx es h t,
                    sim_bexpr_cstmt le (BeePL.Prim (Run h) es t) ctx (Sdo (Eval (Values.Vundef) Tvoid)) ctx
(* The t in Prim Massgn is shadowed, may need to add another one *)
| sim_bind_massgn_st : forall le ctx ctx' ctx'' x t e e' t' ct ce ce' es,
                       transBeePL_type t = ct ->
                       sim_bexpr_cstmt le e' ctx ce' ctx' ->
                       e = Prim Massgn es t ->
                       sim_bexpr_cexpr le e ctx' ce ctx'' ->
                       sim_bexpr_cstmt le (BeePL.Bind x t e e' t') ctx
                                          (Csyntax.Ssequence (Sdo ce) ce') ctx''
| sim_bind_for_st : forall le ctx ctx' ctx'' x t e e' t' ct cs ce' e1 e2 d e3,
                    transBeePL_type t = ct ->
                    sim_bexpr_cstmt le e' ctx ce' ctx' ->
                    e = For x e1 e2 d e3 t ->
                    sim_bexpr_cstmt le e ctx' cs ctx'' ->
                    sim_bexpr_cstmt le (BeePL.Bind x t e e' t') ctx
                                       (Csyntax.Ssequence cs ce') ctx''
| sim_bind_st : forall le ctx ctx' ctx'' x t e e' t' ct ce ce', (* Fix me *)
                transBeePL_type t = ct ->
                sim_bexpr_cstmt le e' ctx ce' ctx' ->
                sim_bexpr_cexpr le e ctx' ce ctx'' ->
                sim_bexpr_cstmt le (BeePL.Bind x t e e' t') ctx
                                   (Csyntax.Ssequence (Sdo (Eassign (Csyntax.Evar x ct) ce Tvoid)) ce') ctx''
(*
| sim_cond_vars_st : forall le e1 e2 e3 t ct ce1 ce2 ce3 g g' i',
                     transBeePL_type t g = Res ct g' i' ->
                     sim_bexpr_cexpr le e1 ce1 ->
                     sim_bexpr_cexpr le e2 ce2 ->
                     sim_bexpr_cexpr le e3 ce3 ->
                     check_var_const e2 ->
                     check_var_const e3 ->
                     sim_bexpr_cstmt le (BeePL.Cond e1 e2 e3 t) 
                                        (Csyntax.Sifthenelse ce1 (Csyntax.Sreturn (Some (Evalof ce2 ct))) (Csyntax.Sreturn (Some (Evalof ce3 ct))))
| sim_cond_var1_st : forall le e1 e2 e3 t ct ce1 ce2 ce3 g g' i',
                     transBeePL_type t g = Res ct g' i' ->
                     sim_bexpr_cexpr le e1 ce1 ->
                     sim_bexpr_cexpr le e2 ce2 ->
                     sim_bexpr_cexpr le e3 ce3 ->
                     check_var_const e2 ->
                     sim_bexpr_cstmt le (BeePL.Cond e1 e2 e3 t) 
                                        (Csyntax.Sifthenelse ce1 (Csyntax.Sreturn (Some (Evalof ce2 ct))) (Csyntax.Sdo ce3))
| sim_cond_var2_st : forall le e1 e2 e3 t ct ce1 ce2 ce3 g g' i',
                     transBeePL_type t g = Res ct g' i' ->
                     sim_bexpr_cexpr le e1 ce1 ->
                     sim_bexpr_cexpr le e2 ce2 ->
                     sim_bexpr_cexpr le e3 ce3 ->
                     check_var_const e3 ->
                     sim_bexpr_cstmt le (BeePL.Cond e1 e2 e3 t) 
                                        (Csyntax.Sifthenelse ce1 (Csyntax.Sdo ce2) (Csyntax.Sreturn (Some (Evalof ce3 ct))))
*)                    
| sim_cond_st : forall le ctx ctx' ctx'' ctx''' e1 e2 e3 t ct ce1 ce2 ce3,
                transBeePL_type t = ct ->
                sim_bexpr_cexpr le e1 ctx ce1 ctx' ->
                sim_bexpr_cstmt le e2 ctx' ce2 ctx'' ->
                sim_bexpr_cstmt le e3 ctx'' ce3 ctx''' ->
                sim_bexpr_cstmt le (BeePL.Cond e1 e2 e3 t) ctx'
                                   (Csyntax.Sifthenelse ce1 ce2 ce3) ctx'''
| sim_unit_st : forall le ctx t ct,
                transBeePL_type t = ct ->
                sim_bexpr_cstmt le (BeePL.Unit t) ctx (Csyntax.Sskip) ctx
| sim_addr_st : forall le ctx l ofs t ct,
                transBeePL_type t = ct ->
                sim_bexpr_cstmt le (BeePL.Addr l ofs t) ctx (Csyntax.Sdo (Csyntax.Eloc l.(lname) ofs l.(lbitfield) ct)) ctx
| sim_hexpr_st : forall le ctx h e t, (* Fix me *)
                 sim_bexpr_cstmt le (BeePL.Hexpr h e t) ctx (Sdo (Eval (Values.Vundef) Tvoid)) ctx
| sim_eapp_st : forall le ctx ctx' ef ts es t cef cts ct ces,
               befunction_to_cefunction ef = cef ->
               transBeePL_types transBeePL_type ts = cts ->
               transBeePL_type t = ct ->
               sim_bexprs_cexprs le es ctx ces ctx' ->
               sim_bexpr_cstmt le (BeePL.Eapp ef ts es t) ctx
                              (Csyntax.Sdo (Csyntax.Ebuiltin cef cts ces ct)) ctx
| sim_sfield_st : forall le ctx ctx' e x t ce ct,
                  transBeePL_type t = ct ->
                  sim_bexpr_cexpr le e ctx ce ctx' ->
                  sim_bexpr_cstmt le (BeePL.Sfield e x t) ctx
                                     (Csyntax.Sdo (Evalof (Csyntax.Efield (Evalof ce (transBeePL_type (typeof_expr e))) x ct) ct)) ctx'
| sim_for_up_st : forall le ctx ctx' ctx'' ctx''' x e1 e2 d e t ce1 ce2 ce3,
                  sim_bexpr_cexpr le e1 ctx ce1 ctx' ->
                  sim_bexpr_cexpr le e2 ctx' ce2 ctx'' ->
                  sim_bexpr_cstmt le e ctx'' ce3 ctx''' ->
                  is_primunsigned_int_long (typeof_expr e1) (typeof_expr e2) = true ->
                  check_range_expr e1 e2 d = true ->
                  d = Up ->
                  sim_bexpr_cstmt le (BeePL.For x e1 e2 d e t) ctx (Csyntax.Sfor (Sdo (Eassign (Csyntax.Evar x (Ctypes.Tint I32 Unsigned noattr)) ce1 (Ctypes.Tint I32 Unsigned noattr)))
                                                   (Csyntax.Ebinop Cop.Ole (Evalof (Csyntax.Evar x (Ctypes.Tint I32 Unsigned noattr)) (Ctypes.Tint I32 Unsigned noattr))
                                                    ce2 (Ctypes.Tint I32 Unsigned noattr))
                                                   (Sdo (Epostincr Cop.Incr (Csyntax.Evar x (Ctypes.Tint I32 Unsigned noattr)) (Ctypes.Tint I32 Unsigned noattr)))
                                                   ce3) ctx'''
| sim_for_down_st : forall le ctx ctx' ctx'' ctx''' x e1 e2 d e t ce1 ce2 ce3,
                  sim_bexpr_cexpr le e1 ctx ce1 ctx' ->
                  sim_bexpr_cexpr le e2 ctx' ce2 ctx'' ->
                  sim_bexpr_cstmt le e ctx'' ce3 ctx''' ->
                  is_primunsigned_int_long (typeof_expr e1) (typeof_expr e2) = true ->
                  check_range_expr e1 e2 d = true ->
                  d = Down ->
                  sim_bexpr_cstmt le (BeePL.For x e1 e2 d e t) ctx (Csyntax.Sfor (Sdo (Eassign (Csyntax.Evar x (Ctypes.Tint I32 Unsigned noattr)) ce1 (Ctypes.Tint I32 Unsigned noattr)))
                                                   (Csyntax.Ebinop Cop.Oge (Evalof (Csyntax.Evar x (Ctypes.Tint I32 Unsigned noattr)) (Ctypes.Tint I32 Unsigned noattr))
                                                    ce2 (Ctypes.Tint I32 Unsigned noattr))
                                                   (Sdo (Epostincr Cop.Decr (Csyntax.Evar x (Ctypes.Tint I32 Unsigned noattr)) (Ctypes.Tint I32 Unsigned noattr)))
                                                   ce3) ctx'''
| sim_enone_st : forall le ctx t t',
                 t = Otype t' ->
                 is_reftype t' = true ->
                 sim_bexpr_cstmt le (BeePL.Enone t) ctx (Csyntax.Sdo ((Csyntax.Ecast (Eval (Values.Vint (Int.repr 0)) tint) (tptr (transBeePL_type t))))) ctx
| sim_esome_st : forall le ctx e t t' cs,
                 t = Otype t' ->
                 is_reftype t' = true ->
                 sim_bexpr_cstmt le e ctx cs ctx ->
                 sim_bexpr_cstmt le (BeePL.Esome e t) ctx cs ctx
| sim_match_fst_st : forall le ctx ctx' ctx'' ctx''' e pes t ce e1 e2 x ce1 ce2,
                     sim_bexpr_cexpr le e ctx ce ctx' -> 
                     length pes = 2%nat ->
                     pes = ((Pnone, e1) :: (Psome x, e2) :: nil) ->
                     sim_bexpr_cstmt le e1 ctx' ce1 ctx'' ->
                     sim_bexpr_cstmt le e2 ctx'' ce2 ctx''' ->
                     sim_bexpr_cstmt le (BeePL.Match e pes t) ctx
                                  (Csyntax.Sifthenelse (Csyntax.Ebinop Cop.Oeq ce
                                                (Csyntax.Ecast (Eval (Values.Vint (Int.repr 0)) tint) (tptr (transBeePL_type t)))
                                               (Ctypes.Tint Ctypes.I8 Ctypes.Unsigned noattr))
                                  ce1 ce2) ctx''
| sim_match_snd_st : forall le ctx ctx' ctx'' ctx''' e pes t ce e1 e2 x ce1 ce2,
                     sim_bexpr_cexpr le e ctx ce ctx' -> 
                     length pes = 2%nat ->
                     pes = ((Psome x, e1) :: (Pnone, e2) :: nil) ->
                     sim_bexpr_cstmt le e1 ctx' ce1 ctx'' ->
                     sim_bexpr_cstmt le e2 ctx'' ce2 ctx''' ->
                     sim_bexpr_cstmt le (BeePL.Match e pes t) ctx
                                  (Csyntax.Sifthenelse (Csyntax.Ebinop Cop.Oeq ce
                                                (Csyntax.Ecast (Eval (Values.Vint (Int.repr 0)) tint) (tptr (transBeePL_type t)))
                                               (Ctypes.Tint Ctypes.I8 Ctypes.Unsigned noattr))
                                  ce2 ce1) ctx''.




(***** Specification for types *****) 
Inductive rel_ptype : BeeTypes.primitive_type -> Ctypes.type -> Prop :=
| rel_tbool : rel_ptype Tbool (Ctypes.Tint I8 Unsigned noattr)
| rel_tint : forall sz s a, 
             rel_ptype (Tint sz s a) (Ctypes.Tint sz s a)
| rel_tlong : forall s a, 
              rel_ptype (Tlong s a) (Ctypes.Tlong s a). 

Inductive rel_btype : BeeTypes.basic_type -> Ctypes.type -> Prop :=
| rel_bprim : forall p ct,
              rel_ptype p ct ->
              rel_btype (Bprim p) ct
| rel_bstruct : forall s a,
                rel_btype (Bstruct s a) (Tstruct s a).

Inductive rel_type : BeeTypes.type -> Ctypes.type -> Prop :=
| rel_utype : rel_type Utype (Ctypes.Tvoid)
| rel_vtype : forall p ct,
              rel_ptype p ct ->
              rel_type (Vtype p) ct
| rel_ptrtype : forall ptr cptr,
                rel_ptr_type ptr cptr ->
                rel_type (Ptrtype ptr) cptr
| rel_stype : forall s a,
              rel_type (Stype s a) (Tstruct s a)
| rel_ftype : forall ts cts ef t ct,
              rel_types ts cts ->
              rel_type t ct -> 
              length ts = length (from_typelist cts) ->
              rel_type (Ftype ts ef t) (Tfunction cts ct 
                                        {| cc_vararg := Some (Z.of_nat (length ts)); cc_unproto := false; cc_structret := false |}) 
| rel_bytes : rel_type Bytes (Tstruct bytes_t noattr)
with rel_ptr_type : BeeTypes.ptr_type -> Ctypes.type -> Prop :=
| rel_reftype_bool : forall i a,
                     rel_ptr_type (Reftype i (Bprim Tbool) a) (Tpointer (Ctypes.Tint I8 Unsigned noattr) noattr)
| rel_reftype : forall i bt a ct,
                rel_btype bt ct ->
(* if ct is Tbool then a should be noattr, hopefully can discriminaite otherwise need another case *)
                rel_ptr_type (Reftype i bt a) (Tpointer ct a) 
| rel_vptype : forall pt ct,
               rel_ptype pt ct ->
               rel_ptr_type (Vptype pt) (tptr tvoid) (* replace with Tpointer ct once compiler is fixed *)
| rel_otype : forall ptr cptr,
              rel_ptr_type ptr cptr ->
              rel_ptr_type (Otype ptr) cptr
| rel_fptype : forall ts cts ef t ct,
               rel_types ts cts ->
               rel_type t ct ->
               length ts = length (from_typelist cts) ->
               rel_ptr_type (Fptype ts ef t) (Ctypes.Tpointer (Tfunction cts ct
                                              {| cc_vararg := None; cc_unproto := false; cc_structret := false |})
                                              noattr)
| rel_sptype : forall s a,
               rel_ptr_type (Sptype s a) (Ctypes.Tpointer (Tstruct s a) a)
with rel_types : list BeeTypes.type -> Ctypes.typelist -> Prop :=
| rel_tnil : rel_types nil Tnil
| rel_tcons : forall bt bts ct cts,
              rel_type bt ct ->
              rel_types bts cts ->
              rel_types (bt :: bts) (Tcons ct cts).

Scheme rel_type_ind_mut := Induction for rel_type Sort Prop
  with rel_ptrtype_ind_mut := Induction for rel_ptr_type Sort Prop
  with rel_typelist_ind_mut := Induction for rel_types Sort Prop.
Combined Scheme rel_type_typelist_ind_mut from rel_type_ind_mut, rel_ptrtype_ind_mut, rel_typelist_ind_mut.

Section rel_type_ind.
Context (Rpt : BeeTypes.primitive_type -> Ctypes.type -> Prop).
Context (Rbt : BeeTypes.basic_type -> Ctypes.type -> Prop).
Context (Rt : BeeTypes.type -> Ctypes.type -> Prop).
Context (Rptr : BeeTypes.ptr_type -> Ctypes.type -> Prop).
Context (Rts : list BeeTypes.type -> Ctypes.typelist -> Prop).
Context (Htbool : Rpt Tbool (Ctypes.Tint I8 Unsigned noattr)).
Context (Htint : forall sz s a, Rpt (Tint sz s a) (Ctypes.Tint sz s a)).
Context (Htlong : forall s a, Rpt (Tlong s a) (Ctypes.Tlong s a)).
Context (Hbprim : forall p ct, Rpt p ct -> Rbt (Bprim p) ct).
Context (Hbstruct : forall s a, Rbt (Bstruct s a) (Tstruct s a)).
Context (Hutype : Rt Utype (Ctypes.Tvoid)).
Context (Hvtype : forall p ct, Rpt p ct -> Rt (Vtype p) ct).
Context (Hptrtype : forall ptr cptr, Rptr ptr cptr -> Rt (Ptrtype ptr) cptr).
Context (Hstype : forall s a, Rt (Stype s a) (Tstruct s a)).
Context (Hftype : forall ts cts ef t ct, Rts ts cts -> Rt t ct -> Rt (Ftype ts ef t) (Tfunction cts ct
                  {| cc_vararg := Some (Z.of_nat (length ts)); cc_unproto := false; cc_structret := false|})).
Context (Hbytes : Rt Bytes (Tstruct bytes_t noattr)).
Context (Hreftypebool : forall i a, Rptr (Reftype i (Bprim Tbool) a) (Tpointer (Ctypes.Tint I8 Unsigned noattr) noattr)).
Context (Hreftype : forall i bt a ct, Rbt bt ct -> Rptr (Reftype i bt a) (Tpointer ct a)).
Context (Hvptype : forall pt ct, Rpt pt ct -> Rptr (Vptype pt) (tptr tvoid)).
Context (Hotype : forall ptr cptr, Rptr ptr cptr -> Rptr (Otype ptr) cptr).
Context (Hfptype : forall ts cts ef t ct, Rts ts cts -> Rt t ct -> Rptr (Fptype ts ef t) (Tpointer (Tfunction cts ct
                   {| cc_vararg := None; cc_unproto := false; cc_structret := false|}) noattr)).
Context (Hsptype : forall s a, Rptr (Sptype s a) (Tpointer (Tstruct s a) a)).
Context (Hnil : Rts nil Tnil).
Context (Hcons : forall t ct ts cts, Rt t ct -> Rts ts cts -> Rts (t :: ts) (Tcons ct cts)).

Lemma rel_type_indP : 
(forall t ct, rel_type t ct -> Rt t ct) /\
(forall ptr cptr, rel_ptr_type ptr cptr -> Rptr ptr cptr) /\
(forall ts cts, rel_types ts cts -> Rts ts cts).
Proof. 
  apply rel_type_typelist_ind_mut; auto.
  - destruct p; intros; inversion r; auto.
  - intros. apply Hreftype. destruct bt.
    + apply Hbprim. inv r. destruct p; inversion H0; auto. 
    + inv r. apply Hbstruct.
  - intros. apply Hvptype with (ct := ct).
    inv r; auto. 
Qed.

End rel_type_ind.

(***** Proof for correctness of type transformation *****)
Lemma type_translated: 
(forall t ct, 
transBeePL_type t = ct ->
rel_type t ct) /\ 
(forall ts cts, 
transBeePL_types transBeePL_type ts = cts ->
rel_types ts cts) /\
(forall ptr cptr,
transBeePL_ptr_type ptr = cptr ->
rel_ptr_type ptr cptr).
Proof.
  apply beepl_type_ind_mut with
    (Pt := fun t => forall ct,
           transBeePL_type t = ct ->
           rel_type t ct)
    (Pptr := fun ptr => forall cptr,
             transBeePL_ptr_type ptr = cptr ->
             rel_ptr_type ptr cptr)
    (Pts := fun ts => forall cts,
           transBeePL_types transBeePL_type ts = cts ->
           rel_types ts cts);
  intros.
  - destruct bt eqn:Ebt; try destruct p eqn:Ep; subst cptr; repeat constructor.
  - inv H. destruct pt.
    + apply rel_vptype with (ct := Ctypes.Tint I8 Unsigned noattr). constructor.
    + apply rel_vptype with (ct := Ctypes.Tint i s a). constructor.
    + apply rel_vptype with (ct := Ctypes.Tlong s a). constructor.
  - constructor. auto.
  - subst cptr. constructor; auto.
    eapply transBeePL_types_length. eauto.
  - subst cptr. constructor.
  - subst ct. constructor.
  - subst ct. constructor.
  - destruct pt; constructor.
  - constructor; auto.
  - subst ct. constructor.
  - subst ct. constructor; auto.
    eapply transBeePL_types_length. eauto.
  - subst ct. constructor.
  - subst cts. constructor.
  - subst cts. constructor; auto.
Qed.

(*
Lemma transBeePL_type_int : forall t g g' i sz s a,
transBeePL_type t g = Res (Ctypes.Tint sz s a) g' i ->
t = Ptype (Tint sz s a) \/ t = Ptype Tbool.
Proof.
(*move=> [].
+ move=> p g g' i sz s a /=. case: p=> //= sz' s' a' [] h1 h2 h3 h4; subst.
+ by move=> h b a g g' i' sz a' a'' /=;case: b=> //= p; case: p=> //=.
move=> es e t g g' i sz s a /=. rewrite /SimplExpr.bind /=.
case hts: (transBeePL_types transBeePL_type es g)=> [errs | cts gs igs] //=.
by case ht: (transBeePL_type t gs)=> [er | ct1 g1 i1] //=.
Qed.*) Admitted.

Lemma transBeePL_type_long : forall t g g' i s a,
transBeePL_type t g = Res (Ctypes.Tlong s a) g' i ->
t = Ptype (Tlong s a).
Proof.
(*move=> [].
+ move=> p g g' i s a /=. by case: p=> //= s' a' [] h1 h2 h3; subst.  
+ by move=> h b a g g' i' a' a'' /=;case: b=> //= p; case: p=> //=.
move=> es e t g g' i sz s /=. rewrite /SimplExpr.bind /=.
case hts: (transBeePL_types transBeePL_type es g)=> [errs | cts gs igs] //=.
by case ht: (transBeePL_type t gs)=> [er | ct1 g1 i1] //=.
Qed.*) Admitted.

Lemma transBeePL_type_void : forall t g g' i,
transBeePL_type t g = Res Tvoid g' i ->
t = Ptype Tunit.
Proof.
(*move=> [].
+ by move=> p g g' i /=; case: p=> //=.
+ by move=> h b a g g' i /=; case: b=> //= p; case: p=> //=.
move=> es ef t g g' i /=. rewrite /SimplExpr.bind /=.
case hts: (transBeePL_types transBeePL_type es g)=> [errs | cts gs igs] //=.
by case ht: (transBeePL_type t gs)=> [er | ct1 g1 i1] //=.
Qed.*) Admitted.

Lemma transBeePL_type_function : forall t ts t1 ct g g' i,
transBeePL_type t g = Res (Tfunction ts t1 ct) g' i ->
exists bts bef brt, t = Ftype bts bef brt. 
Proof.
(*move=> [].
+ by move=> p ts t1 ct g g' i /=; case: p=> //=.
+ by move=> h b a ts t1 ct g g' i' /=; case: b=> //=; move=> p; case: p=> //=.
move=> es ef t ts t1 ct g g' i /=. rewrite /SimplExpr.bind /=.
case hts: (transBeePL_types transBeePL_type es g)=> [errs | cts gs igs] //=.
case ht: (transBeePL_type t gs)=> [er | ct1 g1 i1] //=. move=> [] h1 h2 h3 h4; subst.
exists es. exists ef. by exists t.
Qed.*) Admitted.

Lemma transBeePL_type_ref : forall t t' a' g g' i,
transBeePL_type t g = Res (Tpointer t' a') g' i ->
exists h bt a, t = Reftype h bt a. 
Proof.
(*move=> [].
+ by move=> p t' a' g g' i; case: p=> //=.
+ move=> h b a t' a' g g' i' /=; case: b=> //= p; case: p=> //=.
  + move=> [] h1 h2 h3; subst. exists h. exists (Bprim Tunit). by exists a'.
  + move=> sz s a'' [] h1 h2 h3; subst. exists h. exists (Bprim (Tint sz s a'')). by exists a'.
  move=> s a'' [] h1 h2 h3; subst. exists h. exists (Bprim (Tlong s a'')). by exists a'.
move=> es e t t' a' g g' i /=. rewrite /SimplExpr.bind /=.
case hts: (transBeePL_types transBeePL_type es g)=> [errs | cts gs igs] //=.
by case ht: (transBeePL_type t gs)=> [er | ct1 g1 i1] //=.
Qed.*) Admitted.

Lemma no_btype_to_float : forall t g f a g' i,
transBeePL_type t g <> Res (Tfloat f a) g' i.
Proof.
move=> t g f a g' i /=. case: t=> //=.
+ by move=> p; case: p=> //=.
+ by move=> h b a';case: b=> //= p;case: p=> //=.
move=> es ef t. rewrite /SimplExpr.bind /=.
case hts: (transBeePL_types transBeePL_type es g)=> [errs | cts gs igs] //=.
by case ht: (transBeePL_type t gs)=> [er | ct1 g1 i1] //=.
Qed.

Lemma no_btype_to_array : forall t t' z a g g' i,
transBeePL_type t g <> Res (Tarray t' z a) g' i.
Proof.
move=> t t' z a g g' i /=. case: t=> //=.
+ by move=> p; case: p=> //=.
+ by move=> h b a';case: b=> //= p;case: p=> //=.
move=> es ef t. rewrite /SimplExpr.bind /=.
case hts: (transBeePL_types transBeePL_type es g)=> [errs | cts gs igs] //=.
by case ht: (transBeePL_type t gs)=> [er | ct1 g1 i1] //=.
Qed.


Lemma no_btype_to_union : forall t s a g g' i,
transBeePL_type t g <> Res (Tunion s a) g' i.
Proof.
move=> t s a g g' i /=. case: t=> //=.
+ by move=> p; case: p=> //=.
+ by move=> h b a';case: b=> //= p;case: p=> //=.
move=> es ef t. rewrite /SimplExpr.bind /=.
case hts: (transBeePL_types transBeePL_type es g)=> [errs | cts gs igs] //=.
by case ht: (transBeePL_type t gs)=> [er | ct1 g1 i1] //=.
Qed.

 *)
(***** End of Proof for correctness of type transformation *****)

Lemma transBeePL_expr_expr_spec: forall vm,
(forall e ce g g' i,
  transBeePL_expr_expr e g = Res ce g' i ->
  sim_bexpr_cexpr vm e ce) /\
(forall es ces g g' i,
  transBeePL_expr_exprs transBeePL_expr_expr es g = Res ces g' i ->
  sim_bexprs_cexprs vm es ces).
Proof.
  intro vm. 
  apply expr_list_expr_ind_mut with
    (Pe := fun e => forall ce g g' i, transBeePL_expr_expr e g = Res ce g' i -> sim_bexpr_cexpr vm e ce)
    (Pl := fun es => forall ces g g' i, transBeePL_expr_exprs transBeePL_expr_expr es g = Res ces g' i -> sim_bexprs_cexprs vm es ces);
  intros;
  simpl in *.
  (* Val *)
  - unfold SimplExpr.bind in H.
    destruct (transBeePL_type t g) as [| ct g1 i1] eqn:Htype; try discriminate.
    inv H.
    econstructor; eauto.
  (* Var *)
  - unfold SimplExpr.bind in H.
    destruct (transBeePL_type t g) as [| ct g1 i1] eqn:Htype; try discriminate.
    inv H.
    econstructor; eauto.
  (* Const *)
  - destruct c eqn:Hconst; unfold SimplExpr.bind in H;
    destruct (transBeePL_type t g) as [| ct g1 i1] eqn:Htype; try discriminate;
    inv H;
    econstructor; eauto.
  (* App *)
  - unfold SimplExpr.bind in H1.
    destruct (transBeePL_expr_expr e g) as [|cexpr g1 i1] eqn:Hexpr; try discriminate.
    destruct (transBeePL_expr_exprs transBeePL_expr_expr es g1) as [|cexprs g2 i2] eqn:Hexprs; try discriminate.
    destruct (transBeePL_type t g2) as [|ct g3 i3] eqn:Htype; try discriminate.
    inv H1.
    econstructor; eauto.
  (* Prim *)
  - destruct b eqn:Hprim; unfold SimplExpr.bind in H0;
    try (destruct (transBeePL_expr_exprs transBeePL_expr_expr es g) as [|cexprs g1 i1] eqn:Hexprs; try discriminate;
      destruct (transBeePL_type t g1) as [|ct g2 i2] eqn:Htype; try discriminate;
      destruct (gensym ct g2) as [|i0 g3 p] eqn:Hgen; try discriminate;
      inv H0;
    econstructor; eauto).
    destruct (is_bop_undef t b0 es) eqn:Hundef.
    + destruct (transBeePL_type t g) as [|ct g1 i1] eqn:Htype; try discriminate.
      destruct (return_czero ct g1) as [|v g2 i2] eqn:Hzero; try discriminate.
      inv H0.
      econstructor; eauto.
    + destruct (transBeePL_expr_exprs transBeePL_expr_expr es g) as [|ces g1 i1] eqn:Hexprs; try discriminate.
      destruct (transBeePL_type t g1) as [|ct g2 i2] eqn:Htype; try discriminate.
      inv H0.
      econstructor; eauto.
    inv H0.
    econstructor.
  (* Bind *)
  - unfold SimplExpr.bind in H1.
    destruct (transBeePL_type t g) as [| ct g1 i1] eqn:Htype; try discriminate.
    destruct (transBeePL_type t' g1) as [| ct' g2 i2] eqn:Htype'; try discriminate.
    destruct (transBeePL_expr_expr e g2) as [| ce' g3 i3] eqn:Hexpr; try discriminate.
    destruct (transBeePL_expr_expr e' g3) as [| ce'' g4 i4] eqn:Hexpr'; try discriminate.
    inv H1.
    econstructor; eauto.
  (* Cond *)
  - unfold SimplExpr.bind in H2.
    destruct (transBeePL_expr_expr e1 g) as [| ce1 g1 i1] eqn:Hexpr1; try discriminate.
    destruct (transBeePL_expr_expr e2 g1) as [| ce2 g2 i2] eqn:Hexpr2; try discriminate.
    destruct (transBeePL_expr_expr e3 g2) as [| ce3 g3 i3] eqn:Hexpr3; try discriminate.
    destruct (transBeePL_type t g3) as [| ct g4 i4] eqn:Htype; try discriminate.
    inv H2.
    econstructor; eauto.
  (* Unit *)
  - unfold SimplExpr.bind in H.
    destruct (transBeePL_type t g) as [| ct g1 i1] eqn:Htype; try discriminate.
    inv H.
    econstructor; eauto.
  (* Addr *)
  - unfold SimplExpr.bind in H.
    destruct (transBeePL_type t g) as [| ct g1 i1] eqn:Htype; try discriminate.
    inv H.
    econstructor; eauto.
  (* Hexpr: Fix me*)
  - inv H0.
    econstructor.
  (* Eapp *)
  - unfold SimplExpr.bind in H0.
    destruct (befunction_to_cefunction ef g) as [| ce' g1 i1] eqn:Hfun; try discriminate.
    destruct (transBeePL_types transBeePL_type ts g1) as [| cts g2 i2] eqn:Htypes; try discriminate.
    destruct (transBeePL_type t g2) as [| ct g3 i3] eqn:Htype; try discriminate.
    destruct (transBeePL_expr_exprs transBeePL_expr_expr es g3) as [| ces g4 i4] eqn:Hexprs; try discriminate.
    inv H0.
    econstructor; eauto.
  (* Nil *)
  - inv H.
    apply sim_nil.
  - unfold SimplExpr.bind in H1.
    destruct (transBeePL_expr_expr e g) as [| ce g1 i1] eqn:Hexpr; try discriminate.
    destruct (transBeePL_expr_exprs transBeePL_expr_expr es g1) as [| ces' g2 i2] eqn:Hexprs; try discriminate.
    inv H1.
    econstructor; eauto.
Qed.

(*
Lemma transBeePL_expr_stmt_spec: forall vm e ce g g' i,
transBeePL_expr_st e g = Res ce g' i ->
sim_bexpr_cstmt vm e ce.
Proof.
  intro vm. 
  destruct transBeePL_expr_expr_spec with (vm:=vm) as [Hexprspec Hexprsspec].
  induction e; intros; simpl in H.
  (* Val *)
  - unfold SimplExpr.bind in H.
    destruct (transBeePL_type t g) as [| ct g1 i1] eqn:Htype; try discriminate.
    inv H.
    eapply sim_val_st with (le:=vm) (v:=v) (t:=t) (ct:=ct) (cv:=trans_bvalue_cvalue v); eauto.
  (* Var *)
  - unfold SimplExpr.bind in H.
    destruct (transBeePL_type t g) as [|ct g1 i1] eqn:Htype; try discriminate.
    inv H.
    eapply sim_var_st with (le:=vm); eauto.
  (* Const *)
  - destruct c; unfold SimplExpr.bind in H;
    destruct (transBeePL_type t g) as [|ct g1 i1] eqn:Htype; try discriminate;
    inv H;
    econstructor; eauto.
  (* App *)
  - unfold SimplExpr.bind in H.
    destruct (transBeePL_expr_expr e g) as [|cexpr g1 i1] eqn:Hexpr; try discriminate.
    destruct (transBeePL_expr_exprs transBeePL_expr_expr l g1) as [|cexprs g2 i2] eqn:Hexprs; try discriminate.
    destruct (transBeePL_type t g2) as [|ct g3 i3] eqn:Htype; try discriminate.
    inv H.
    econstructor; eauto.
  (* Prim *)
  - destruct b; unfold SimplExpr.bind in H.
    (* Ref *)
    + destruct (transBeePL_expr_exprs transBeePL_expr_expr l g) as [|cexprs g1 i1] eqn:Hexprs; try discriminate.
      destruct (transBeePL_type t g1) as [|ct g2 i2] eqn:Htype; try discriminate.
      destruct (gensym ct g2) as [|i0 g3 p] eqn:Hgen; try discriminate.
      inv H.
      econstructor; eauto.
    (* Deref *)
    + destruct (transBeePL_expr_exprs transBeePL_expr_expr l g) as [|cexprs g1 i1] eqn:Hexprs; try discriminate.
      destruct (transBeePL_type t g1) as [| ct g2 i2] eqn:Htype; try discriminate.
      inv H.
      econstructor; eauto.
    (* Massgn *)
    + destruct (transBeePL_expr_exprs transBeePL_expr_expr l g) as [|cexprs g1 i1] eqn:Hexprs; try discriminate.
      destruct (transBeePL_type t g1) as [| ct g2 i2] eqn:Htype; try discriminate.
      inv H.
      econstructor; eauto.
    (* Uop *)
    + destruct (transBeePL_expr_exprs transBeePL_expr_expr l g) as [|cexprs g1 i1] eqn:Hexprs; try discriminate.
      destruct (transBeePL_type t g1) as [| ct g2 i2] eqn:Htype; try discriminate.
      inv H.
      econstructor; eauto.
    (* Bop *)
    + destruct (is_bop_undef t b l) eqn:Hundef.
      * destruct (transBeePL_type t g) as [|ct g1 i1] eqn:Htype; try discriminate.
        destruct (return_czero ct g1) as [|v g2 i2] eqn:Hzero; try discriminate.
        inv H.
        econstructor; eauto.
      * destruct (transBeePL_expr_exprs transBeePL_expr_expr l g) as [|cexprs g1 i1] eqn:Hexprs; try discriminate.
        destruct (transBeePL_type t g1) as [| ct g2 i2] eqn:Htype; try discriminate.
        inv H.
        econstructor; eauto.
    (* Run: Fix me *)
    + inv H.
      econstructor.
  (* Bind *)
  - unfold SimplExpr.bind in H.
    destruct e2 eqn:Ee2;
    (* All cases except Const and Var *)
    try (
      destruct (transBeePL_type t g) as [| ct g1 i1'] eqn:Htype; try discriminate;
      destruct (transBeePL_expr_expr e1 g1) as [| ce1 g2 i2'] eqn:Hexpr; try discriminate;
      destruct (transBeePL_expr_st _ g2) as [| ce2 g3 i3'] eqn:Hexpr'; try discriminate;
      inv H;
      econstructor; eauto
    ).
    (* e2 is Var *)
    + destruct (transBeePL_expr_expr e1 g) as [| ce1 g1 i1'] eqn:Hexpr; try discriminate.
      destruct (transBeePL_expr_st (Var i1 t1) g1) as [| ce2 g2 i2] eqn:Hexpr'; try discriminate. 
      destruct (transBeePL_type t g2) as [| ct1 g3 i3] eqn:Htype; try discriminate.
      destruct (transBeePL_type t1 g3) as [| ct2 g4 i4] eqn:Htype'; try discriminate.
      destruct (transBeePL_type (typeof_expr (Var i1 t1)) g4) as [| ct3 g5 i5] eqn:Htype''; try discriminate.
      inv H.
      econstructor; eauto.
    (* e2 is Const *) 
    + destruct (transBeePL_type t1 g) as [| ct g1 i1] eqn:Htype; try discriminate.
      destruct (transBeePL_expr_expr e1 g1) as [| ce1 g2 i2] eqn:Hexpr; try discriminate.
      destruct (transBeePL_expr_st (Const c t1) g2) as [| ce2 g3 i3] eqn:Hexpr'; try discriminate.
      inv H.
      econstructor; eauto.
  (* Cond *)
  - unfold SimplExpr.bind in H.
    destruct (transBeePL_expr_expr e1 g) as [| ce1 g1 i1] eqn:Hexpr1; try discriminate.
    destruct (transBeePL_expr_st e2 g1) as [| ce2 g2 i2] eqn:Hexpr2; try discriminate.
    destruct (transBeePL_expr_st e3 g2) as [| ce3 g3 i3] eqn:Hexpr3; try discriminate.
    destruct (transBeePL_type t g3) as [| ct g4 i4] eqn:Htype; try discriminate.
    inv H.
    econstructor; eauto.
  (* Unit *)
  - unfold SimplExpr.bind in H.
    destruct (transBeePL_type t g) as [| ct g1 i1] eqn:Htype; try discriminate.
    inv H.
    econstructor; eauto.
  (* Addr *)
  - unfold SimplExpr.bind in H.
    destruct (transBeePL_type t g) as [| ct g1 i1] eqn:Htype; try discriminate. 
    inv H.
    econstructor; eauto.
  (* Hexpr: Fix me *)
  - inv H.
    econstructor; eauto.
  (* Eapp *)
  - unfold SimplExpr.bind in H.
    destruct (befunction_to_cefunction e g) as [| cf g1 i1] eqn:Hfunc; try discriminate.
    destruct (transBeePL_types transBeePL_type l g1) as [| cts g2 i2] eqn:Htypes; try discriminate.
    destruct (transBeePL_type t g2) as [| ct g3 i3] eqn:Htype; try discriminate.
    destruct (transBeePL_expr_exprs transBeePL_expr_expr l0 g3) as [| ces g4 i4] eqn:Hexprs; try discriminate.
    inv H.
    econstructor; eauto.
Qed.
 *)

Variable benv : BeePL.vmap.

(* Relates global variables of BeePL and Csyntax *)
Inductive match_globvar : BeePL.globvar type -> AST.globvar Ctypes.type -> Prop :=
| match_globvar_intro : forall t init t' init' rd vo g g' i,
  transBeePL_type t g = Res t' g' i ->
  rel_type t t' ->
  match_globvar (mkglobvar t init rd vo) (AST.mkglobvar t' init' rd vo).

(* Relates the function definition of BeePL and Csyntax *)
Inductive match_function : BeePL.function -> Csyntax.function -> Prop :=
| match_fun : forall vm bf cf g1 i1 g2 i2 g3 i3,
  transBeePL_type (BeePL.fn_return bf) (initial_generator tt) = Res (Csyntax.fn_return cf) g1 i1 ->
  BeePL.fn_callconv bf = Csyntax.fn_callconv cf ->
  BeePL_aux.unzip1 (BeePL.fn_args bf) = BeePL_aux.unzip1 (Csyntax.fn_params cf) ->
  transBeePL_types transBeePL_type (BeePL_aux.unzip2 (BeePL.fn_args bf)) (initial_generator tt) = 
  Res (to_typelist (BeePL_aux.unzip2 (Csyntax.fn_params cf))) g2 i2 ->
  BeePL_aux.unzip1 (BeePL.fn_vars bf) = BeePL_aux.unzip1 (Csyntax.fn_vars cf) ->
  transBeePL_types transBeePL_type (BeePL_aux.unzip2 (BeePL.fn_vars bf)) (initial_generator tt) = 
  Res (to_typelist (BeePL_aux.unzip2 (Csyntax.fn_vars cf))) g3 i3 ->
  sim_bexpr_cstmt vm (BeePL.fn_body bf) (Csyntax.fn_body cf) ->
  match_function bf cf.

<<<<<<< HEAD
Lemma transBeePL_function_spec: forall bf cf,
transBeePL_function_function bf = OK cf ->
match_function bf cf.
Proof.
  intros.
  unfold transBeePL_function_function in H.
  destruct (transBeePL_type (BeePL.fn_return bf) (initial_generator tt)) as [|crt g1 i1] eqn:Hreturn; try discriminate.
  destruct (transBeePL_types transBeePL_type (BeePL_aux.unzip2 (fn_args bf)) (initial_generator tt)) as [|pt g2 i2] eqn:Hargs; try discriminate.
  destruct (transBeePL_types transBeePL_type (BeePL_aux.unzip2 (BeePL.fn_vars bf)) (initial_generator tt)) as [|vt g3 i3] eqn:Hvars; try discriminate.
  destruct (transBeePL_expr_st (BeePL.fn_body bf) (initial_generator tt)) as [|fbody g4 i4] eqn:Hbody; try discriminate.
  injection H as H.
  erewrite <- H.
  eapply match_fun with (vm := benv); cbn in *.
  - eauto.
  - eauto.
  - apply transBeePL_types_length in Hargs.
    eapply unzip1_cancel.
    rewrite unzip2_preserves_length in Hargs.
    rewrite <- unzip1_preserves_length in Hargs.
    apply Hargs.
  - rewrite <- unzip2_cancel.
    + rewrite to_typelist_cancel.
      eauto.
    + apply transBeePL_types_length in Hargs.
      rewrite unzip2_preserves_length in Hargs.
      rewrite <- unzip1_preserves_length in Hargs.
      eauto.
  - apply transBeePL_types_length in Hvars.
    eapply unzip1_cancel.
    rewrite unzip2_preserves_length in Hvars.
    rewrite <- unzip1_preserves_length in Hvars.
    apply Hvars.
  - rewrite <- unzip2_cancel.
    + rewrite to_typelist_cancel.
      eauto.
    + apply transBeePL_types_length in Hvars.
      rewrite unzip2_preserves_length in Hvars.
      rewrite <- unzip1_preserves_length in Hvars.
      eauto.
  - eapply transBeePL_expr_stmt_spec.
    eauto.
Qed.
=======
(* Lemma tranBeePL_function_spec: forall bf cf,
transBeePL_function_function bf = OK cf ->
match_function bf cf.
Proof.
Admitted. *)
>>>>>>> bwip

(* Relates the fundef of BeePL and Csyntax *)
(* Fix me: Add external function rel later *) 
Inductive match_fundef : BeePL.fundef -> Csyntax.fundef -> Prop :=
| match_fundef_internal : forall f cf,
  match_function f cf -> 
  match_fundef (Internal f) (Ctypes.Internal cf)
| match_fundef_external : forall ef cef ts cts t ct cc gs gs' i'' g g' i' gf gf' if',
  transBeePL_types transBeePL_type ts gs = Res cts gs' i'' ->
  transBeePL_type t g = Res ct g' i' ->
  befunction_to_cefunction ef gf = Res cef gf' if' ->
  match_fundef (External ef ts t cc) (Ctypes.External cef cts ct cc).

(* Lemma transBeePL_fundef_spec : forall f cf, 
transBeePL_fundef_fundef (Internal f) = OK (Ctypes.Internal cf) ->
match_fundef (Internal f) (Ctypes.Internal cf).
Proof.
rewrite /transBeePL_fundef_fundef /= /transBeePL_function_function /=. 
move=> f cf h. monadInv h. move: EQ.
case ht: (transBeePL_type (BeePL.fn_return f) (initial_generator tt))=> [er | r g i]//=. 
case hts : (transBeePL_types transBeePL_type (BeePL_aux.unzip2 (fn_args f))
      (initial_generator tt))=> [er' | r' g' i'] //=.
case hts' : (transBeePL_types transBeePL_type (BeePL_aux.unzip2 (BeePL.fn_vars f)) (initial_generator tt))=> [er1 | r1 g1 i1] //=.
case hes : (transBeePL_expr_st (BeePL.fn_body f) (initial_generator tt))=> [er2 | r2 g2 i2] //=.
move=> [] <- /=.
apply match_fundef_internal; rewrite /=; auto. 
apply transBeePL_function_spec; auto.
by rewrite /transBeePL_function_function /= ht hts hts' hes /=. 
Qed. *)

(* Relates the global definitions of BeePL and Csyntax *) 
Inductive match_globdef : BeePL.globdef BeePL.fundef type -> AST.globdef Csyntax.fundef Ctypes.type -> Prop :=
| match_gfun : forall f cf,
  match_fundef f cf ->
  match_globdef (AST.Gfun f) (AST.Gfun cf)
| match_gvar : forall g cg,
  match_globvar g cg ->
  match_globdef (Gvar g) (AST.Gvar cg).

Definition match_ident_globdef (igd1 : ident * BeePL.globdef BeePL.fundef type) 
  (igd2 : ident *  AST.globdef Csyntax.fundef Ctypes.type) : Prop :=
fst igd1 = fst igd2 /\ match_globdef (snd igd1) (snd igd2).

Definition match_program_gen (p1 : BeePL.program) (p2 : Csyntax.program) : Prop :=
  list_forall2 (match_ident_globdef) p1.(prog_defs) p2.(AST.prog_defs)
  /\ p2.(AST.prog_main) = p1.(prog_main)
  /\ p2.(AST.prog_public) = p1.(prog_public).

Definition match_prog (p1: BeePL.program) (p2: Csyntax.program) :=
    match_program_gen p1 p2
 /\ prog_types p1 = Ctypes.prog_types p2. 

(* Lemma transf_program_match:
forall p cp, BeePL_compcert p = OK cp -> match_prog p cp.
Proof.
rewrite /BeePL_compcert /=. move=> p cp H. monadInv H.
split; auto; rewrite /match_program_gen /=; split; auto.
move: x EQ. elim: (prog_defs p)=> //=.
(* nil *)
+ move=> xs [] eq /=; subst. by apply list_forall2_nil.
(* cons *)
move=> [] id gd gds ih /= xs h. monadInv h.
move: (ih x0 EQ1)=> hl. apply list_forall2_cons; auto.
rewrite /match_ident_globdef /=; split; auto.
rewrite /transBeePL_globdef_globdef in EQ. case: gd EQ=> //=.
+ move=> fd h. monadInv h. apply match_gfun. rewrite /transBeePL_fundef_fundef in EQ.
  case: fd EQ=> //= f h. monadInv h. apply match_fundef_internal.
  by apply transBeePL_function_spec.
+ move=> t cc. case hef: (befunction_to_cefunction f (initial_generator tt))=> [er | cef g1 i1] //=.
  case hts: (transBeePL_types transBeePL_type h (initial_generator tt))=> [er1 | cts g3 i3] //=.
  case ht: (transBeePL_type t (initial_generator tt))=> [er2 | ct g4 i4] //=.
  move=> [] heq; subst. by apply match_fundef_external with (initial_generator tt) g3 i3 
  (initial_generator tt) g4 i4 (initial_generator tt) g1 i1; auto. 
move=> gv h. monadInv h. apply match_gvar. case: gv EQ=> //= gi i r v.
case: x1=> //= gi' i' r' v'. rewrite /transBeePLglobvar_globvar /=. move=> h.
move: h. case ht: (transBeePL_type gi (initial_generator tt))=> [er | r1 g1 i1] //=.
move=> [] h1 h2 h3 h4; subst. apply match_globvar_intro with (initial_generator tt) g1 i1; auto.
have [h1 h2] := type_translated. by move: (h1 gi gi' (initial_generator tt) g1 i1 ht).
Qed. *)

(* Relation between BeePL vmap and Csyntax local env *)
Record match_env (vm : BeePL.vmap) (cvm : env) : Prop :=
mk_match_env {
 local_match: forall id b t ct g g' i,
              vm!id = Some (b, t) ->
              transBeePL_type t g = Res ct g' i ->
              cvm!id = Some (b, ct);
 global_match: forall id,
               vm!id = None ->
               cvm!id = None }.

End specifications.

Section semantic_preservation.

Variable bprog : BeePL.program.

Variable cprog : Csyntax.program.

Hypothesis TRANSBPL: match_prog bprog cprog.

Let bge := BeePL.globalenv bprog.

Let cge := Csem.globalenv cprog.

Variable benv : BeePL.vmap.

Variable cenv : Csem.env.

(* Preservation of composite env *) 
Lemma comp_env_preserved :
Csem.genv_cenv cge = BeePL.genv_cenv bge. 
Proof.
rewrite /=. case: TRANSBPL=> //= h1 h2.
have /= := prog_comp_env_eq bprog. rewrite h2 /=.
generalize (prog_comp_env_eq bprog) (compcert.cfrontend.Ctypes.prog_comp_env_eq cprog). 
congruence.
Qed.

(* Complete Me *)
(* Preservation of symbols *) 
Lemma symbols_preserved : forall (id : ident), 
Genv.find_symbol (Csem.genv_genv cge) id = Genv.find_symbol bge id.
Proof.
Admitted.

(* Complete Me *)
(* Preservation of symbol env *)
Lemma senv_preserved : Senv.equiv bge (Csem.genv_genv cge).
Proof.
Admitted.

(* Equivalence between vmaps benv and cenv *)
Lemma equiv_global_benv_cenv : forall vi, 
match_env benv cenv ->
benv ! vi = None ->
cenv ! vi = None.
Proof.
move=> vi h hm. case hb: (cenv ! vi)=> [ [l t] | ] //=.
case h=> //= h' h''. move: (h'' vi hm)=> hc. by rewrite hc in hb.
Qed.

Lemma equiv_local_benv_cenv : forall vi l t ct g g' i, 
match_env benv cenv ->
transBeePL_type t g = Res ct g' i ->
benv ! vi = Some (l, t) ->
cenv ! vi = Some (l, ct).
Proof.
move=> vi l t ct g g' i h ht hm. 
case h=> //= h' h''. by move: (h' vi l t ct g g' i hm ht). 
Qed.

Search Genv.find_funct_ptr.
Print trans_program_astprog.
(* Complete Me *)
(* Preservation of function ptr *) 
Lemma function_ptr_translated : forall v f,
Genv.find_funct_ptr bge v = Some f ->
exists tf, Genv.find_funct_ptr (Csem.genv_genv cge) v = Some tf /\ match_fundef f tf. 
Proof.
  intros v f FIND.
  simpl in FIND.
  destruct TRANSBPL as [MATCH_PROG _].
  exploit (Genv.find_funct_ptr_inversion); eauto.
  eapply Genv.find_funct_ptr_match in FIND; eauto.
  destruct FIND as (cunit & tf & FIND_TF & MATCH_F & LINKORD).
  simpl.
  exists tf; split; eauto.
  eapply MATCH_F.
  unfold match_program_gen in MATCH_PROG.
  unfold Linking.match_program_gen.
  eapply MATCH_PROG.
Admitted.

(* Complete Me *)
(* Preservation of function *)
Lemma functions_translated: forall v f,
Genv.find_funct bge v = Some f ->
exists tf, Genv.find_funct (Csem.genv_genv cge) v = Some tf /\ match_fundef f tf.
Proof.
Admitted.

(* Complete me *)
(* Preservation of function returns *)
(* changed to exists because match_function gives a specific g its true for *)
Lemma function_return_preserved : forall f tf,
match_function f tf ->
exists g i, transBeePL_type (BeePL.fn_return f) (initial_generator tt) = Res (Csyntax.fn_return tf) g i.
Proof. intros. inv H. eauto. Qed.

(* Preservation of deref_addr between BeePL and Csyntax *) 
Lemma deref_addr_translated:  forall ty m addr ofs bf v cty cv g g' i,
deref_addr bge ty m addr ofs bf v ->
transBeePL_type ty g = Res cty g' i ->
trans_bvalue_cvalue v = cv ->
match chunk_for_volatile_type cty bf with 
| None => Csem.deref_loc cge cty m addr ofs bf Events.E0 cv
| Some chunk => exists tr, bf = Full /\ 
                Events.volatile_load (Csem.genv_genv cge) chunk m addr ofs tr cv
end.
Proof.
move=> ty m addr ofs bf v cty cv g g' i hd ht hv. 
rewrite /chunk_for_volatile_type /=. inversion hd; subst.
(* by value *)
+ have hcty := non_volatile_type_preserved ty cty g g' i false H0 ht. rewrite hcty /=.
  apply Csem.deref_loc_value with (transl_bchunk_cchunk chunk); auto.
  + by have := BeePL_auxlemmas.access_mode_preserved ty cty (By_value (transl_bchunk_cchunk chunk)) 
               g g' i H ht.
  rewrite /trans_bvalue_cvalue in H1. by have -> := bv_cv_reflex v0 v H2. 
(* by value, volatile *)
+ have -> /= := non_volatile_type_preserved ty cty g g' i true H0 ht. 
  have -> /= := access_mode_preserved ty cty (By_value (transl_bchunk_cchunk chunk)) g g' i H ht.
  exists tr. split=> //=. have -> := bv_cv_reflex v0 v H2. have hequiv := senv_preserved. 
  rewrite /Csem.genv_genv /= in hequiv.
  by have := @Events.volatile_load_preserved bge (Genv.globalenv cprog) (transl_bchunk_cchunk chunk)
           m addr ofs tr v0 hequiv H1.
(* by reference *)
have h /= := BeePL_auxlemmas.access_mode_preserved ty cty By_reference g g' i H ht. 
case: ifP=> //= hc. 
+ rewrite h /=. by apply Csem.deref_loc_reference.
by apply Csem.deref_loc_reference.
Qed.

(* Preservation of assign_addr between BeePL and Csyntax *)
Lemma assign_addr_translated: forall ty m addr ofs bf v m' cty cv v' cv' g g' i,
assign_addr bge ty m addr ofs bf v m' v' ->
transBeePL_type ty g = Res cty g' i ->
trans_bvalue_cvalue v = cv ->
trans_bvalue_cvalue v' = cv' ->
match chunk_for_volatile_type cty bf with 
| None => Csem.assign_loc cge cty m addr ofs bf cv Events.E0 m' cv
| Some chunk => exists tr, bf = Full /\ 
                Events.volatile_store (Csem.genv_genv cge) chunk m addr ofs cv tr m'
end.
Proof.
  intros ty m addr ofs bf v m' cty cv v' cv' g g' i hd ht hv hv'.
  unfold chunk_for_volatile_type.
  inv hd.
  - have hcty := non_volatile_type_preserved ty cty g g' i false H0 ht.
    rewrite hcty.
    eapply Csem.assign_loc_value.
    + erewrite BeePL_auxlemmas.access_mode_preserved; eauto.
    + assumption.
    + inv H1. simpl. f_equal. 
      unfold transC_val_bplvalue in H2.
      destruct v0; try discriminate;
      inv H2;
      reflexivity.
  - have -> := non_volatile_type_preserved ty cty g g' i true H0 ht.
    have -> := access_mode_preserved ty cty (By_value (transl_bchunk_cchunk chunk)) g g' i H ht.
    exists tr.
    split. reflexivity.
    simpl.
    have -> := bv_cv_reflex v0 v' H2.
    have hequiv := senv_preserved.
    simpl in hequiv.
    by have := @Events.volatile_store_preserved bge (Genv.globalenv cprog) (transl_bchunk_cchunk chunk)
           m addr ofs v0 tr m' hequiv H1.
Qed.


End semantic_preservation.


(*
(* Big step semantics with rvalue *) 
(* If an expression evaluates to a value then in the c semantics if the expression is 
   evaluated in RV position then it should also produce the same value 
   If an expression evaluates to a value then in the c semantics if the expression is 
   evaluated in LV position then it should produce a location (deref, var)*)
Lemma bsem_cexpr_lsimple : forall m e l ofs ce g g' i, 
bsem_expr_slv bge benv m e l ofs ->
transBeePL_expr_expr e g = Res ce g' i ->
match_env benv cenv ->
eval_simple_lvalue cge cenv m ce l.(lname) ofs l.(lbitfield). 
Proof.
move=> m e l ofs ce g g' i hl /= hte henv. induction hl => //=.
(* lvar *)
+ rewrite /transBeePL_expr_expr /SimplExpr.bind in hte. 
  case htt: (transBeePL_type t g) hte=> [er | r g'' i'] //=.
  move=> [] h1 h2; subst. 
  apply esl_var_local. by have := equiv_local_benv_cenv x l (Reftype h t' a) r g g' i' henv htt H.
(* gvar *)
+ rewrite /transBeePL_expr_expr /SimplExpr.bind in hte. 
  case hte': (transBeePL_type t g) hte=> [er | r g'' i'] //=.
  move=> [] h1 h2; subst.
  apply esl_var_global.
  + by have := equiv_global_benv_cenv x henv H. 
  by have := symbols_preserved x=> ->. 
(* Loc *) 
rewrite /transBeePL_expr_expr /SimplExpr.bind in hte. 
case ht: (transBeePL_type t g) hte=> [er | r g'' i'] //=.
move=> [] h1 h2; subst. by apply esl_loc.
Qed.

Lemma bsem_cexpr_rsimple : forall m e v ce g g' i, 
bsem_expr_srv bge benv m e v ->
transBeePL_expr_expr e g = Res ce g' i ->
match_env benv cenv ->
eval_simple_rvalue cge cenv m ce (trans_bvalue_cvalue v).
Proof.
move=> m e v ce g g' i hr. move: ce g g' i. induction hr=> //=.
(* val *)
+ move=> ce g g' i ht henv /=. 
  rewrite /SimplExpr.bind in ht. 
  case ht: (transBeePL_type t g) ht=> [er | r g'' i'] //=.
  move=> [] h1 h2; subst. by apply esr_val. 
(* deref *)
+ move=> ce g g' i' hte henv /=.
  rewrite /transBeePL_expr_exprs /SimplExpr.bind in hte.
  case he1:(transBeePL_expr_expr e g) hte=> [er | r g'' i''] //=.
  case he2: (transBeePL_type t g'')=> [er1 | r1 g1 i1] //=.
  move=> [] h1 h2; subst. apply esr_rvalof with l.(lname) ofs l.(lbitfield).
    + by have := bsem_cexpr_lsimple hm e l ofs r g g'' i'' H he1 henv.
    + have h := transBeePL_expr_expr_type_equiv e r g g'' i'' he1. 
      by have := type_preserved_generator (typeof_expr e) r1 (Csyntax.typeof r) g'' g' g g'' i1 i''
              i1 i'' he2 h. 
    + by have := non_volatile_type_preserved (typeof_expr e) r1 g'' g' i1 false H2 he2. 
   have := deref_addr_translated (typeof_expr e) hm l.(lname) ofs l.(lbitfield) v r1
           (trans_bvalue_cvalue v) g'' g' i1 H0 he2 refl_equal. 
   have hc := non_volatile_type_preserved (typeof_expr e) r1 g'' g' i1 false H2 he2.
   by rewrite /chunk_for_volatile_type /= hc /=. 
(* uop *)
+ move=> ce g1 g2 i1 /= hte /= henv.
  rewrite /transBeePL_expr_exprs /SimplExpr.bind in hte. 
  case he1: (transBeePL_expr_expr e g1) hte=> [er | r1 g1' i1'] //=.
  case ht1: (transBeePL_type t g1')=> [er' | r2 g2' i2'] //=.
  move=> [] h1 h2; subst; rewrite /=. rewrite /exprlist_list_expr /=. 
  apply esr_unop with (trans_bvalue_cvalue v).
  + by move: (IHhr r1 g1 g1' i1' he1 henv).
  have heq := bv_cv_reflex v' v'' H2; subst.
  have ht' := transBeePL_expr_expr_type_equiv e r1 g1 g1' i1' he1.
  have heq1 := type_preserved_generator (typeof_expr e) (Csyntax.typeof r1) r2 
               g1 g1' g1' g2 i1' i2' i1' i2' ht' ht1.
  rewrite -heq1 in ht1.
  by have heq' := type_preserved_generator (typeof_expr e) (Csyntax.typeof r1) ct g1' g2 g g' i2' i
          i2' i ht1 H; subst.
(* Bop *)
+ move=> ce g1 g2 i1 /= hte henv. rewrite /SimplExpr.bind in hte. 
  case hte1 : (transBeePL_expr_expr e1 g1) hte=> [er1 | re1 ge1 ie1] //=.
  case hte2 : (transBeePL_expr_expr e2 ge1)=> [er2 | re2 ge2 ie2] //=.
  case ht : (transBeePL_type t ge2)=> [ert | rt gt it] //=.
  move=> [] h1 h2; subst. rewrite /exprlist_list_expr /=. 
  apply esr_binop with (trans_bvalue_cvalue v1) (trans_bvalue_cvalue v2).
  + by move: (IHhr1 re1 g1 ge1 ie1 hte1 henv).
  + by move: (IHhr2 re2 ge1 ge2 ie2 hte2 henv).
  have hv1 := bv_cv_reflex v v' H3.
  have ht1' := transBeePL_expr_expr_type_equiv e1 re1 g1 ge1 ie1 hte1. case: H1=> [] h1 h2; subst.
  have heq := type_preserved_generator (typeof_expr e1) ct1 rt g g' ge2 g2 i it i it H ht; subst.
  have heq' := type_preserved_generator (typeof_expr e1) (Csyntax.typeof re1) rt g1 ge1 ge2 g2 ie1
               it ie1 it ht1' ht; subst.
  have ht2' := transBeePL_expr_expr_type_equiv e2 re2 ge1 ge2 ie2 hte2. 
  have heq'' := type_preserved_generator (typeof_expr e2) ct2 (Csyntax.typeof re2) g' g'' ge1 ge2 
                i' ie2 i' ie2 H0 ht2'; subst. by have -> := comp_env_preserved.
(* Unit *)
move=> ce g g' i /=. rewrite /SimplExpr.bind /=.
move=> [] h1 h2 henv /=; subst. by apply esr_val.
Qed.

(* A final state does not step forward *)
Lemma final_state_no_step : forall s s',
BeePL.final_state s ->
~ (bstep bge s s').
Proof.
move=> s s'. elim: s=> //=.
+ move=> f e k vm m hf. by inversion hf.
+ move=> fd args k m hf. by inversion hf.
+ move=> res m hf. move=> h. by inversion h.
move=> hf. by inversion hf.
Qed.

Lemma decompose_expr: forall f e k m,
BeePL.safe bge (BeePL.ExprState f e k benv m) -> 
is_simple_expr e \/ exists S, bstep bge (BeePL.ExprState f e k benv m) S.
Proof.
move=> f e. move: f. elim: e=> //=.
(* val *)
+ move=> v t f k m hs. by left.
(* var *)
+ move=> v f k m hs. by left.
(* const *)
+ move=> c t f k m hs. by left.
(* app *)
+ move=> e hi es t f k m hs. right.
  inversion hs; subst.
  + by inversion H.
  move: H. move=> [] s' he. by exists s'.
(* builtin *)
+ move=> [] /=.
  (* ref *)
  + move=> [] //=.
    + move=> t f k m he. inversion he; subst. + by inversion H.
      move: H. move=> [] s' href. inversion href; subst. by inversion H5.
    move=> e es t f k m hs. elim: es hs=> //=.
    + move=> hs. rewrite /BeePL.safe in hs. inversion hs.
      + by inversion H.
      move: H. move=> [] s' href. right. by exists s'.
    move=> e' es hi hs. rewrite /BeePL.safe in hs.
    inversion hs; subst.
    + by inversion H.
    move: H. move=> [] s' he. inversion he; subst. by inversion H5.
  (* deref *)
  + move=> [] //=.
    + move=> t f k m hs. rewrite /BeePL.safe in hs.
      inversion hs; subst.
      + by inversion H.
      move: H. move=> [] s' he. inversion he; subst. by inversion H5.
    move=> e es t f k m hs. elim: es hs=> //=.
    + move=> hs. rewrite /BeePL.safe in hs. inversion hs; subst.
      + by inversion H.
      move: H. move=> [] s' he. right. by exists s'.
    move=> e' es hi hs. rewrite /BeePL.safe in hs.
    inversion hs; subst.
    + by inversion H.
    move: H. move=> [] s' he. inversion he; subst. by inversion H5.
  (* massgn *)
  + move=> [] //=.
    + move=> t f k m hs. inversion hs; subst.
      + by inversion H.
      move: H. move=> [] s' he. inversion he; subst. by inversion H5.
    move=> e es t f k m hs. elim: es hs=> //=.
    + move=> hs. rewrite /BeePL.safe in hs. inversion hs; subst.
      + by inversion H.
      move: H. move=> [] s' he. right. by exists s'.
    move=> e' es hi hs. rewrite /BeePL.safe in hs.
    inversion hs; subst.
    + by inversion H.
    move: H. move=> [] s' he. inversion he; subst. by inversion H5.
    right. exists (BeePL.ExprState f (Val v' (typeof_expr e)) k benv m').
    by apply step_prim_massgn with ct1 ct2 l ofs v g1 g2 g3 i i'.
  (* unary *)
  + move=> u [] //=.
    + move=> t f k m hs. inversion hs; subst.
      + by inversion H. move: H. move=> [] s' he. inversion he; subst. by inversion H5.
    move=> e es t f k m hs. elim: es hs=> //=.
    + move=> hs. inversion hs; subst.
      + by inversion H.
      move: H. move=> [] s' he. right. by exists s'.
    move=> e' es hi hs. rewrite /BeePL.safe in hs.
    inversion hs; subst.
    + by inversion H.
    move: H. move=> [] s' he. inversion he; subst. by inversion H5.
  (* binary *)
  + move=> b [] //=.
    + move=> t f k m hs. inversion hs; subst.
      + by inversion H. move: H. move=> [] s' he. inversion he; subst. by inversion H5.
    move=> e es t f k m hs. elim: es hs=> //=.
    + move=> hs. inversion hs; subst.
      + by inversion H.
      move: H. move=> [] s' he. right. by exists s'.
    move=> e' es hi hs. rewrite /BeePL.safe in hs.
    inversion hs; subst.
    + by inversion H.
    move: H. move=> [] s' he. inversion he; subst. inversion H5; subst.
    right. exists (BeePL.ExprState f (Val v (typeof_expr (Prim (Bop b) [:: e; e'] t))) k benv m).
    apply BeePL.step_expr; auto. 
  (* run *) (* fix me *)
  move=> m es t f k m' hs. inversion hs; subst.
  + by inversion H.
  move: H. move=> [] s' H. inversion H; subst. by inversion H6.
(* bind *)
+ move=> i t e hi e' hi' t' f k m hs. inversion hs; subst.
  + by inversion H.
  move: H. move=> [] s' he. right. by exists s'.
(* cond *)
+ move=> e hi e1 hi1 e2 hi2 t f k m hs. inversion hs; subst.
  + by inversion H.
  move: H. move=> [] s' H. right. by exists s'.
(* unit *)
+ move=> t f k m hs. by left.
(* addr *)
+ move=> l i f k m hs. by left.
(* hexpr *) (* fix me *)
+ move=> m e hi t f k m' hs. inversion hs; subst.
  + by inversion H.
  move: H. move=> [] s' he. right. by exists s'.
(* eapp *)
move=> e ts es t f k m hs. inversion hs; subst.
+ by inversion H.
move: H. move=> [] s' he. right. by exists s'.
Qed.
  
(* Progress for expression state: A safe expression state always make progress except the val *)
(* Need to add well formedness about store *)
Lemma expr_state_can_step: forall f e k m,
BeePL.safe bge (BeePL.ExprState f e k benv m) ->
exists S, bstep bge (BeePL.ExprState f e k benv m) S.
Proof.
move=> f e k m hs. move: f k benv m hs. elim: e=> //=.
(* Val *)
+ move=> v t f k benv' m hs. inversion hs; subst.
  + by inversion H.
  move: H. move=> [] s' he. by exists s'. 
(* Var *)
+ admit.
(* Const *)
Admitted.  

Lemma safe_steps: forall s s',
BeePL.safe bge s -> 
bstep bge s s' -> 
BeePL.safe bge s'.
Proof.
move=> s. elim: s=> //=.
Admitted.

Lemma bsem_expr_srv_safe: forall C e v m k f,
bsem_expr_srv bge benv m e v ->
BeePL.leftcontext RV RV C -> 
BeePL.safe bge (BeePL.ExprState f (C e) k benv m) ->
BeePL.safe bge (BeePL.ExprState f (C (Val v (typeof_expr e))) k benv m).
Proof.
Admitted.

(*Lemma simple_can_eval:
  forall e from C,
  simple e = true -> leftcontext from RV C -> safe (BeePL.ExprState f (C e) k benv m) ->
  match from with
  | LV => exists b ofs bf, eval_simple_lvalue e m a b ofs bf
  | RV => exists v, eval_simple_rvalue e m a v
  end.
Proof.*)

Lemma bsem_cexpr_list :
forall m es tes vs cts ces g g' i, 
bsem_expr_srvs bge benv m es vs ->
transBeePL_expr_exprs transBeePL_expr_expr es g = Res ces g' i ->
typeof_exprs es = tes ->
transBeePL_types transBeePL_type tes g = Res cts g' i ->
match_env benv cenv ->
eval_simple_list cge cenv m ces cts (transBeePL_values_cvalues vs).
Proof.
Admitted.

(* Complete Me *)
(* Preservation of allocation of variables between BeePL and Csyntax *)
Lemma alloc_variables_preserved: forall m m' benv' vrs cvrs cvrs' cvrs'' cts g g' i,
BeePL.alloc_variables benv m vrs benv' m' ->
unzip1 vrs = cvrs ->
unzip2 vrs = cvrs' ->
transBeePL_types transBeePL_type cvrs' g = Res cvrs'' g' i ->
from_typelist cvrs'' = cts ->
exists cenv', Csem.alloc_variables cge cenv m (zip cvrs cts) cenv' m'.
Proof.
Admitted.

(* Complete Me *)
(* Preservation of bind parameters between BeePL and Csyntax *)
Lemma bind_variables_preserved: forall m m' benv' vrs cvrs cvrs' cvrs'' cts g g' i,
BeePL.bind_variables bge benv m vrs benv' m' ->
unzip1 vrs = cvrs ->
unzip2 vrs = cvrs' ->
transBeePL_types transBeePL_type cvrs' g = Res cvrs'' g' i ->
from_typelist cvrs'' = cts ->
exists cenv', Csem.bind_parameters cge cenv m (zip cvrs cts) cenv' m'.
Proof.
Admitted.

(* Preservation of semantics of expressions in BeePL and expressions in Csyntax *) 
(* Refer: sstep_simulation in SimplExprproof.v *)
(* Equivalence between left reduction top level *)
Lemma equiv_lreduction : forall e m e' m' ce g g' i', 
lreduction bge benv e m e' m' ->
transBeePL_expr_expr e g = Res ce g' i' ->
match_env benv cenv ->
exists ce', Csem.lred cge cenv ce m ce' m' /\ sim_bexpr_cexpr benv e' ce'.
Proof.
move=> e m e' m' ce g g' i' hl. induction hl. 
(* local var *)
+ move=> /= he henv. 
  rewrite /SimplExpr.bind in he.
  case ht: (transBeePL_type t g) he=> [er | r g'' i''] //=.
  move=> [] h1 h2; subst. case: henv=> [hm1 hm2]; subst.
  move: (hm1 x l (Reftype h (Bprim t') a) r g g' i'' H ht)=> H'.
  exists (Eloc l Ptrofs.zero Full r). split=> //=.
  + by apply Csem.red_var_local.
  apply sim_addr with g g' i''; rewrite /=. by case: t' H ht=> //=.
(* global var *)
move=> /= he henv. 
rewrite /SimplExpr.bind in he.
case ht: (transBeePL_type t g) he=> [er | r g'' i''] //=.
move=> [] h1 h2; subst. case: henv=> [hm1 hm2]; subst. 
move: (hm2 x H)=> H'.
exists (Eloc l Ptrofs.zero Full r). split=> //=.
+ apply Csem.red_var_global.
  + by apply H'.
  by have := symbols_preserved x=> ->. 
by apply sim_addr with g g' i''; rewrite /=.
Qed. 

(* Equivalence between right reduction top level *)
Lemma equiv_rreduction : forall e m e' m' ce g g' i',
rreduction bge benv e m e' m' ->
transBeePL_expr_expr e g = Res ce g' i' ->
exists ce' t, Csem.rred cge ce m t ce' m' /\ sim_bexpr_cexpr benv e' ce'.
Proof.
move=> e m e' m' ce g g' i' hr. induction hr; subst; rewrite /=.
(* deref *)
+ (*move=> hr. rewrite /SimplExpr.bind in hr.
  case hte: (transBeePL_type (typeof_expr e) g) hr=> [ere | cte ge ie] //=.
  case hte': (transBeePL_type (typeof_expr e) ge )=> [ere' | cte' ge' ie'] //=.
  move=> [] h1 h2; subst.
  exists (Eval (trans_bvalue_cvalue v) cte'). exists Events.E0.
  split=> //=.
  + have heq:= type_preserved_generator (typeof_expr e) cte cte' g ge ge g' ie ie' ie ie'
            hte hte'; subst. apply Csem.red_rvalof.
    have := deref_addr_translated (typeof_expr e) hm l ofs bf v cte' 
            (trans_bvalue_cvalue v) ge g' ie' H hte' refl_equal.
    have hc := non_volatile_type_preserved (typeof_expr e) cte' ge g' ie' false H1 hte'.
    by rewrite /chunk_for_volatile_type /= hc /=.
  by apply sim_val with ge g' ie'.*) admit.
(* ref *) (* Fix me *)
+ admit.
(* uop *)
+ move=> hr. rewrite /SimplExpr.bind in hr.
  case ht: (transBeePL_type t g) hr=> [er | ct1 g1 i1] //=.
  case ht1: (transBeePL_type t g1)=> [er1 | ct2 g2 i2] //=.
  move=> [] h1 h2; subst. 
  exists (Eval v' ct2). exists Events.E0. split=> //=.
  + apply Csem.red_unop. 
    by have heq:= type_preserved_generator t ct ct1 g0 g'0 g g1 i'0 i1 i'0 i1 H ht; subst.
  have <- /= := bv_cv_reflex v' v'' H1. by apply sim_val with g1 g' i2.
(* bop *)
+ move=> hr. rewrite /SimplExpr.bind in hr.
  case ht1: (transBeePL_type t1 g) hr=> [er1 | ct1' g1 i1] //=.
  case ht2: (transBeePL_type t2 g1)=> [er2 | ct2' g2 i2] //=.
  case ht3: ( transBeePL_type t g2)=> [er3 | ct3 g3 i3] //=.
  move=> [] h1 h2; subst.
  exists (Eval v ct3). exists Events.E0. split=> //=.
  + apply Csem.red_binop. have -> := comp_env_preserved.
    have heq1 := type_preserved_generator t1 ct1 ct1' g0 g'0 g g1 i'0 i1 i'0 i1 H ht1; subst.
    by have heq2 := type_preserved_generator t2 ct2 ct2' g'0 g'' g1 g2 i'' i2 i'' i2 H0 ht2; subst.
  have <- /= := bv_cv_reflex v v' H2. by apply sim_val with g2 g' i3.
(* cond *) (* cond steps to Eparen which we don't have in our language *)
+ admit.
(* massgn *) 
+ (*move=> hr. rewrite /SimplExpr.bind in hr.
  case ht: (transBeePL_type t g) hr=> [er | ct1' g1 i1] //=.
  case ht2: (transBeePL_type tv2 g1)=> [er2 | ct2' g2 i1'] //=.
  case ht3: (transBeePL_type t g2)=> [er3 | ct3' g3 i2'] //=.
  move=> [] h1 h2; subst. inversion H2; subst.
  + exists (Eval (trans_bvalue_cvalue v') ct3'). exists Events.E0. split=> //=.
    + have heq1 := type_preserved_generator t ct1 ct1' g0 g'0 g g1 i'0 i1 i'0 i1 H ht; subst.
      have heq1 := type_preserved_generator tv2 ct2 ct2' g'0 g'' g1 g2 i'' i1' i'' i1' H0 ht2; subst.
      have heq1 := type_preserved_generator t ct1' ct3' g g1 g2 g' i1 i2' i1 i2' ht ht3; subst.
      apply Csem.red_assign with (trans_bvalue_cvalue v').
      + by apply H1. 
        have := assign_addr_translated t hm l ofs Full v' hm' ct3'
            (trans_bvalue_cvalue v') v' (trans_bvalue_cvalue v') g2 g' i2' H2 ht3
            refl_equal refl_equal. 
      have hc := non_volatile_type_preserved t ct3' g2 g' i2' false H4 ht3.
      by rewrite /chunk_for_volatile_type /= hc /=. 
    by apply sim_val with g2 g' i2'.
   exists (Eval (trans_bvalue_cvalue v') ct3'). exists tr. split=> //=.
   have heq1 := type_preserved_generator t ct1 ct1' g0 g'0 g g1 i'0 i1 i'0 i1 H ht; subst.
   have heq1 := type_preserved_generator tv2 ct2 ct2' g'0 g'' g1 g2 i'' i1' i'' i1' H0 ht2; subst.
   have heq1 := type_preserved_generator t ct1' ct3' g g1 g2 g' i1 i2' i1 i2' ht ht3; subst.
   apply Csem.red_assign with (trans_bvalue_cvalue v').
   + by apply H1. 
     have := assign_addr_translated t hm l ofs Full v' hm' ct3'
            (trans_bvalue_cvalue v') v' (trans_bvalue_cvalue v') g2 g' i2' H2 ht3
            refl_equal refl_equal. 
     have hc := non_volatile_type_preserved t ct3' g2 g' i2' true H4 ht3.
     rewrite /chunk_for_volatile_type /= hc /=. 
     have -> /= := access_mode_preserved t ct3' (By_value (transl_bchunk_cchunk chunk)) g2 g' i2'
             H3 ht3. move=> [] x [] _ hs. 
     apply Csem.assign_loc_volatile with (transl_bchunk_cchunk chunk).
     by have := access_mode_preserved t ct3' (By_value (transl_bchunk_cchunk chunk)) g2 g' i2'
             H3 ht3. by apply hc. have -> := bv_cv_reflex v0 v' H6.
     have hequiv := senv_preserved. rewrite /cge /Csem.genv_genv /= in hequiv.
     by have := @Events.volatile_store_preserved bge (Genv.globalenv cprog) 
                (transl_bchunk_cchunk chunk) hm l ofs v0 tr hm' hequiv H5. rewrite /Csem.genv_genv /=. 
  by apply sim_val with g2 g' i2'.*) admit.
(* bind *) (* need to think about how bind translates *)
+ admit.
(* unit *)
admit.
Admitted.  
  
(*** Matching between continuations ***) 
Inductive match_bcont_ccont : composite_env -> BeePL.cont -> Csem.cont -> Prop :=
| match_Kstop : match_bcont_ccont bprog.(prog_comp_env) BeePL.Kstop Csem.Kstop
| match_Kdo : forall bc cc,
              match_bcont_ccont bprog.(prog_comp_env) bc cc ->
              match_bcont_ccont bprog.(prog_comp_env) (BeePL.Kdo bc) (Csem.Kdo cc)
| match_Kcall : forall bf cf vm cenv CC bt ct bc cc,
                (* add linking order ?? *)
                transBeePL_function_function bf = OK cf ->
                match_env benv cenv ->
                match_bcont_ccont bprog.(prog_comp_env) bc cc ->
                match_bcont_ccont bprog.(prog_comp_env) (BeePL.Kcall bf vm bt bc) 
                                       (Csem.Kcall cf cenv CC ct cc).

(*** Matching between states ***) 
Inductive match_bstate_cstate : BeePL.state -> Csem.state -> Prop :=
| match_exprstate : forall bf cf be ce bc cc m g g' i,
                    transBeePL_function_function bf = OK cf ->
                    transBeePL_expr_expr be g = Res ce g' i ->
                    sim_bexpr_cexpr benv be ce ->
                    match_env benv cenv ->
                    match_bcont_ccont bprog.(prog_comp_env) bc cc ->
                    match_bstate_cstate (BeePL.ExprState bf be bc benv m) 
                                        (Csem.ExprState cf ce cc cenv m)
| match_state : forall bf cf be cst bc cc m g g' i, (* Fix me *)
                transBeePL_function_function bf = OK cf ->
                transBeePL_expr_st be g = Res cst g' i ->
                sim_bexpr_cstmt benv be cst ->
                match_env benv cenv ->
                match_bcont_ccont bprog.(prog_comp_env) bc cc ->
                match_bstate_cstate (BeePL.ExprState bf be bc benv m) 
                                    (Csem.State cf cst cc cenv m)
| match_callstate : forall bfd bvs bc m cfd cvs cc,
                    transBeePL_fundef_fundef bfd = OK cfd ->
                    transBeePL_values_cvalues bvs = cvs ->
                    match_bcont_ccont bprog.(prog_comp_env) bc cc ->
                    match_bstate_cstate (BeePL.CallState bfd bvs bc m)
                                        (Csem.Callstate cfd cvs cc m)
| match_stuckstate : match_bstate_cstate (BeePL.StuckState) (Csem.Stuckstate).


(* Simulation proof *)
(*         ==
     BS1 ------- CS1
     |          |
     |        + | t
     v          v
     BS2 ------- CS2
           ==                         I
*)

(* Equivalence between resultant state of BeePL big step semantics 
   and Csyntax (Cstrategy) big step semantics *) 
Lemma bstep_estep_simulation: forall bs1 bs2, 
bstep bge bs1 bs2 ->
forall cs1 (MS: match_bstate_cstate bs1 cs1),
exists cs2 t, (star Cstrategy.estep cge cs1 t cs2 (*/\(measure S2 < measure S1)%nat*) 
               \/ Cstrategy.estep cge cs1 t cs2) /\
              match_bstate_cstate bs2 cs2.
Proof.
move=> bs1 bs2 hs cs1 hm. elim: bs1 hs hm=> //=.
+ move=> f e k vm m he hm. elim: e he hm=> //=.
  (* val *)
  + move=> v t he hm. inversion hm; subst.
    inversion H6; subst. rewrite /SimplExpr.bind in H0.
    case ht: (transBeePL_type t g) H0=> [er | ct g'' i''] //=. 
    move=> [] h1 h2; subst. 
    exists (Csem.ExprState cf (Eval (trans_bvalue_cvalue v) ct) cc cenv m).
    exists Events.E0. split=> //=. 
    + admit.
    admit.
  + admit.
  (* Var *)
  + move=> v he hm. inversion hm; subst. 
    inversion H6; subst. 
Admitted.

(* Equivalence between resultant state of BeePL small step semantics 
   and Csytax (Csem) small step semantics *)
Lemma equiv_bstep_cstep : forall bs1 bs2,
BeePL.step bge benv bs1 bs2 ->
forall cs1, match_bstate_cstate bs1 cs1 ->
exists cs2 t, Csem.step cge cs1 t cs2 /\ match_bstate_cstate bs2 cs2.
Proof.
induction 1; intros.
Admitted.
*)