Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Coq.Lists.List.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes Coqlib SimplExpr.
Require Import BeePL_aux BeePL BeeTypes Csyntax Errors SimplExpr BeePL_values.

Local Open Scope string_scope.
Local Open Scope gensym_monad_scope.
(**** BeePL Compiler *****)
Section transBeePL_exprs.

Variables transBeePL_expr_expr : BeePL.expr -> mon Csyntax.expr.

(* Translates list of BeePL expressions to list of C expressions *)
Fixpoint transBeePL_expr_exprs (es : list BeePL.expr) : mon Csyntax.exprlist :=
match es with 
| nil => ret Enil 
| e :: es => do ce <- (transBeePL_expr_expr e);
             do ces <- (transBeePL_expr_exprs es);
             ret (Econs ce ces)
end.

End transBeePL_exprs.

Fixpoint exprlist_list_expr (es: Csyntax.exprlist) : list expr :=
match es with 
| Enil => nil 
| Econs e1 es => (e1 :: exprlist_list_expr es)
end.

Definition default_expr := (Eval (Values.Vundef) Tvoid).

(*Definition Ederef' (a: Csyntax.expr) (t: Ctypes.type) : Csyntax.expr :=
  match a with
  | Eaddrof a' t' => if type_eq t (typeof a') then a' else Ederef a t
  | _ => Ederef a t
  end.*)

Fixpoint transBeePL_expr_expr (e : BeePL.expr) : mon Csyntax.expr := 
match e with 
| Val v t => do vt <- (transBeePL_type t);
             ret (Eval (transBeePL_value_cvalue v) vt) 
(*| Valof e t => do ct <- (transBeePL_type t);
               do ce <- (transBeePL_expr_expr e);
               ret (Evalof ce ct)*)
| Var x t => do xt <- (transBeePL_type t);
           ret (Evar x xt)
| Const c t => match c with 
               | ConsInt i => do it <- (transBeePL_type t); ret (Eval (Values.Vint i) it)
               | ConsLong i => do it <- (transBeePL_type t); ret (Eval (Values.Vlong i) it)
               | ConsUnit => do ut <- (transBeePL_type t); ret (Eval (Values.Vint (Int.repr 0)) ut) 
               end
| App e es t => do ce <- (transBeePL_expr_expr e); 
                do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                do ct <- (transBeePL_type t);
                ret (Ecall ce ces ct)
| Prim b es t => match b with 
                 | Ref => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                          do ct <- (transBeePL_type t);
                          do tv <- (gensym ct);
                          ret (Ecomma (Eassign (Evar tv ct) (hd default_expr (exprlist_list_expr ces)) ct) (Eaddrof (Evar tv ct) ct)
                              ct) (* Fix me *) 
                 | Deref => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                            do ct <- (transBeePL_type t);
                            ret (Evalof (hd default_expr (exprlist_list_expr ces)) 
                                ct)   
                 | Massgn => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                             do ct <- (transBeePL_type t);
                             ret (Eassign (hd default_expr (exprlist_list_expr ces))
                                    (hd default_expr (tl (exprlist_list_expr ces)))
                                 ct)
                 | Run h => ret (Eval (Values.Vundef) Tvoid) (* Fix me *)
                 | Uop o => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                            do ct <- (transBeePL_type t);
                            ret (Eunop o
                                (hd default_expr (exprlist_list_expr ces)) 
                                ct)
                 | Bop o => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                            do ct <- (transBeePL_type t);
                            ret (Ebinop o
                                  (hd default_expr (exprlist_list_expr ces)) 
                                  (hd default_expr (tl (exprlist_list_expr ces)))
                                ct)
                 end 
| Bind x t e e' t' => do ct <- (transBeePL_type t);
                      do ce <- (transBeePL_expr_expr e);
                      do ce' <- (transBeePL_expr_expr e');
                      do ct' <- (transBeePL_type t');
                      ret (Ecomma (Eassign (Evar x ct) ce ct) ce' ct') 
| Cond e e' e'' t => do ce <- (transBeePL_expr_expr e);
                     do ce' <- (transBeePL_expr_expr e');
                     do ce'' <- (transBeePL_expr_expr e'');
                     do ct <- (transBeePL_type t);
                     ret (Econdition ce ce' ce'' ct)  
| Unit t=> do ct <- (transBeePL_type t);
           ret (Eval (transBeePL_value_cvalue Vunit) ct) (* Fix me *)
| Addr l ofs t => do ct <- transBeePL_type t;
                  ret (Eloc l.(lname) ofs l.(lbitfield) ct)
| Hexpr h e t => ret (Eval (Values.Vundef) Tvoid) (* FIX ME *)
| Eapp ef ts es t => do cef <- befunction_to_cefunction ef;
                     do cts <- (transBeePL_types transBeePL_type ts);
                     do ct <- (transBeePL_type t);
                     do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                     ret (Ebuiltin cef cts ces ct)
end.

Definition check_var_const (e : BeePL.expr) : bool :=
match e with 
| Var x t => true 
| Const c t => true 
| _ => false
end.


Fixpoint transBeePL_expr_st (e : BeePL.expr) : mon Csyntax.statement :=
match e with 
| Val v t => do vt <- (transBeePL_type t);
             ret (Sreturn (Some (Eval (transBeePL_value_cvalue v) vt))) 
(*| Valof e t => do ct <- (transBeePL_type t);
               do ce <- (transBeePL_expr_expr e);
               ret (Sreturn (Some (Evalof ce ct)))*)
| Var x t => do ct <- (transBeePL_type t);
             ret (Sreturn (Some (Evalof (Evar x ct) ct)))
| Const c t => do ct <- (transBeePL_type t);
               ret (Sreturn (Some (Evalof (match c with 
                                      | ConsInt i => Eval (Values.Vint i) ct
                                      | ConsLong i => Eval (Values.Vlong i) ct
                                      | ConsUnit => Eval (Values.Vint (Int.repr 0)) ct
                                      end) ct)))
| App e es t => do ce <- (transBeePL_expr_expr e);
                do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                do ct <- (transBeePL_type t);
                ret (Sdo (Ecall ce ces ct))  
| Prim b es t => match b with 
                 | Ref => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                          do ct <- (transBeePL_type t);
                          do tv <- (gensym ct);
                          ret (Sdo (Ecomma (Eassign (Evar tv ct) (hd default_expr (exprlist_list_expr ces)) ct) 
                                   (Eaddrof (Evar tv ct) ct)
                              ct)) (* Fix me *)
                 | Deref => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                            do ct <- (transBeePL_type t);
                            ret (Sdo (Evalof (hd default_expr (exprlist_list_expr ces)) 
                                     ct))   
                 | Massgn => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                             do ct <- (transBeePL_type t);
                             ret (Sdo (Eassign (hd default_expr (exprlist_list_expr ces))
                                              (hd default_expr (tl (exprlist_list_expr ces)))
                                      ct)) 
                 | Run h => ret (Sdo (Eval (Values.Vundef) Tvoid)) (* Fix me *)
                 | Uop o => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                            do ct <- (transBeePL_type t); 
                            ret (Sdo (Eunop o 
                                     (hd default_expr (exprlist_list_expr ces)) 
                                     ct)) 
                 | Bop o => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                            do ct <- (transBeePL_type t);
                            ret (Sdo (Ebinop o 
                                     (hd default_expr (exprlist_list_expr ces)) 
                                     (hd default_expr (tl (exprlist_list_expr ces)))
                                     ct))
                 end 
| Bind x t e e' t' => match e' with 
                      (* no side-effect case *)
                      | Var x' t' => do ce <- (transBeePL_expr_expr e);
                                     do ce' <- (transBeePL_expr_st e'); 
                                     do ct <- (transBeePL_type t);
                                     do ct' <- (transBeePL_type t');
                                     do rt <- (transBeePL_type (BeePL.typeof_expr (e')));
                                     ret (Ssequence (Sdo (Eassign (Evar x ct) ce Tvoid))
                                                    (ce'))
                      | Const c t => do ct <- (transBeePL_type t); 
                                     do ce <- (transBeePL_expr_expr e);
                                     do ce' <- (transBeePL_expr_st e');
                                     ret (Ssequence (Sdo (Eassign (Evar x ct) ce Tvoid)) 
                                                    ce')
                      (* can produce side-effects *)
                      | _ => do ct <- (transBeePL_type t);
                             do ce <- (transBeePL_expr_expr e);
                             do ce' <- (transBeePL_expr_st e');
                             ret (Ssequence (Sdo (Eassign (Evar x ct) ce Tvoid)) 
                                            (ce'))
                    end
| Cond e e' e'' t' => do ce <- (transBeePL_expr_expr e);
                      do ce' <- (transBeePL_expr_st e');
                      do ce'' <- (transBeePL_expr_st e'');
                      do ct' <- (transBeePL_type t');
                      ret (Sifthenelse ce ce' ce'')
                      (*if (check_var_const e' && check_var_const e'') (* check for expressions with side-effects *)
                      then ret (Sifthenelse ce ce' ce'')
                      else if (check_var_const e') then ret (Sifthenelse ce ce' ce'')
                                                   else if (check_var_const e'') 
                                                        then ret (Sifthenelse ce ce' (Sreturn (Some (Evalof ce'' ct'))))
                                                        else ret (Sifthenelse ce ce' (Sdo ce''))*)
| Unit t=> do ct <- (transBeePL_type t);
           ret (Sreturn (Some (Evalof (Eval (transBeePL_value_cvalue Vunit) ct) ct))) (* Fix me *)
| Addr l ofs t => do ct <- (transBeePL_type t);
                  ret (Sdo (Eloc l.(lname) ofs l.(lbitfield) ct))                    
| Hexpr h e t => ret (Sdo (Eval (Values.Vundef) Tvoid)) (* FIX ME *)
| Eapp ef ts es t => do cef <- befunction_to_cefunction ef;
                     do cts <- (transBeePL_types transBeePL_type ts);
                     do ct <- (transBeePL_type t);
                     do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                     ret (Sdo (Ebuiltin cef cts ces ct))
end.

(* Translates the BeePL function declaration to C function *) 
Definition transBeePL_function_function (fd : BeePL.function) : res (Csyntax.function) :=
match (transBeePL_type (fd.(BeePL.fn_return)) (initial_generator tt)) with 
| Err msg => Error msg
| Res crt g i => match (transBeePL_types transBeePL_type (unzip2 (fd.(fn_args))) (initial_generator tt)) with 
                | Err msg => Error msg
                | Res pt g i => match (transBeePL_types transBeePL_type (unzip2 (fd.(BeePL.fn_vars))) (initial_generator tt)) with 
                                | Err msg => Error msg
                                | Res vt g i => match (transBeePL_expr_st (fd.(BeePL.fn_body)) (initial_generator tt)) with 
                                                | Err msg => Error msg
                                                | Res fbody g i => OK {| fn_return := crt; 
                                                                         fn_callconv := cc_default; 
                                                                         fn_params := zip (unzip1 (fd.(fn_args)))
                                                                                   (from_typelist pt);
                                                                         fn_vars := zip (unzip1 (fd.(BeePL.fn_vars)))
                                                                                 (from_typelist vt);
                                                                         fn_body :=  fbody|}
                                    end
                        end
            end
end.

Local Open Scope error_monad_scope.

Definition transBeePL_fundef_fundef (fd : BeePL.fundef) : res Csyntax.fundef :=
match fd with 
| Internal f => do tf <- transBeePL_function_function f;
                OK (Ctypes.Internal tf)
| External ef ts t cc => match (befunction_to_cefunction ef (initial_generator tt)) with
                         | Err msg => Error msg
                         | Res cef g' i => match (transBeePL_types transBeePL_type ts (initial_generator tt)) with 
                                           | Err msg => Error msg
                                           | Res cts g' i => match (transBeePL_type t (initial_generator tt)) with 
                                                             | Err msg => Error msg
                                                             | Res ct g' i => OK (Ctypes.External cef cts ct cc)
                                                             end
                                           end
                         end
end.

(* Translates the value that is assigned to global variable to C global variable data *)

Definition transBeePL_init_data_init_data (g : BeePL.init_data) : AST.init_data :=
match g with 
| Init_int8 i => AST.Init_int8 i
| Init_int16 i => AST.Init_int16 i
| Init_int32 i => AST.Init_int32 i
| Init_int64 i => AST.Init_int64 i
end. 

(* Translates the list of global variable data to list of C global variable data *)
Fixpoint transBeePL_init_datas_init_datas (gs : list BeePL.init_data) : list AST.init_data :=
match gs with 
| nil => nil
| g :: gs => transBeePL_init_data_init_data g :: transBeePL_init_datas_init_datas gs
end. 

(* Translates BeePL global variable to C global variable *) 
Definition transBeePLglobvar_globvar (gv : BeePL.globvar type) : res (AST.globvar Ctypes.type)  :=
match transBeePL_type (gv.(gvar_info)) (initial_generator tt) with 
| Err msg => Error msg
| Res gvt g i => OK {| AST.gvar_info := gvt; 
                       AST.gvar_init := (gv.(gvar_init)); 
                       AST.gvar_readonly := gv.(gvar_readonly); 
                       AST.gvar_volatile :=  gv.(gvar_volatile)|}
end.

Definition transBeePL_globdef_globdef (gd : BeePL.globdef BeePL.fundef BeeTypes.type) : res (AST.globdef fundef Ctypes.type) :=
match gd with 
| AST.Gfun f => do cf <- transBeePL_fundef_fundef f;
            OK (AST.Gfun cf)
| Gvar g => do cg <- transBeePLglobvar_globvar g;
            OK (AST.Gvar cg)
end.

Fixpoint transBeePL_globdefs_globdefs (gds : list (BeePL.globdef BeePL.fundef BeeTypes.type)) : res (list (AST.globdef fundef Ctypes.type)) :=
match gds with 
| nil => OK (nil)
| d :: ds => do gd <-  transBeePL_globdef_globdef d; 
             do gds <- transBeePL_globdefs_globdefs ds;
             OK (gd :: gds)
end.

Lemma composite_default :
build_composite_env nil = OK (PTree.empty composite).
Proof.
unfold build_composite_env; simpl; reflexivity.
Qed.

(* Missing compositie information and list of public functions *) 
Definition BeePL_compcert (p : BeePL.program) : res Csyntax.program :=
  do pds <- transBeePL_globdefs_globdefs (unzip2 (p.(prog_defs)));
  OK {| Ctypes.prog_defs := zip (unzip1 p.(prog_defs)) pds;
        Ctypes.prog_public := prog_public p;
        Ctypes.prog_main := prog_main p;
        Ctypes.prog_types := prog_types p;
        Ctypes.prog_comp_env := prog_comp_env p;
        Ctypes.prog_comp_env_eq := prog_comp_env_eq p |}.

