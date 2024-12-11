Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Coq.Lists.List.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes Coqlib.
Require Import BeePL_aux BeePL BeeTypes Csyntax Errors.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

(**** BeePL Compiler *****)
Section transBeePL_exprs.

Variables transBeePL_expr_expr : BeePL.expr -> res Csyntax.expr.

(* Translates list of BeePL expressions to list of C expressions *)
Fixpoint transBeePL_expr_exprs (es : list BeePL.expr) : res Csyntax.exprlist :=
match es with 
| nil => OK Enil 
| e :: es => do ce <- (transBeePL_expr_expr e);
             do ces <- (transBeePL_expr_exprs es);
             OK (Econs ce ces)
end.

End transBeePL_exprs.

Fixpoint exprlist_list_expr (es: Csyntax.exprlist) : list expr :=
match es with 
| Enil => nil 
| Econs e1 es => (e1 :: exprlist_list_expr es)
end.

Definition default_expr := (Eval (Values.Vundef) Tvoid).

Fixpoint transBeePL_expr_expr (e : BeePL.expr) : res Csyntax.expr := 
match e with 
| Val v t => do vt <- (transBeePL_type t);
             OK (Eval (transBeePL_value_cvalue v) vt) 
| Var x => do xt <- (transBeePL_type (vtype x));
           OK (Evar (vname x) xt)
| Const c t => match c with 
               | ConsInt i => do it <- (transBeePL_type t); OK (Eval (Values.Vint i) it)
               | ConsLong i => do it <- (transBeePL_type t); OK (Eval (Values.Vlong i) it)
               | ConsUnit => do ut <- (transBeePL_type t); OK (Eval (Values.Vint (Int.repr 0)) ut) 
               end
| App r e es t => do ce <- (transBeePL_expr_expr e); 
                  do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                  do ct <- (transBeePL_type t);
                  OK (Ecall ce ces ct)
| Prim b es t => match b with 
                 | Ref => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                          do ct <- (transBeePL_type t);
                          OK (Eaddrof (hd default_expr (exprlist_list_expr ces)) 
                              ct) 
                 | Deref => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                            do ct <- (transBeePL_type t);
                            OK (Ederef (hd default_expr (exprlist_list_expr ces)) 
                                ct)   
                 | Massgn => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                             do ct <- (transBeePL_type t);
                             OK (Eassign (hd default_expr (exprlist_list_expr ces))
                                    (hd default_expr (tl (exprlist_list_expr ces)))
                                 ct)
                 | Run h => OK (Eval (Values.Vundef) Tvoid) (* Fix me *)
                 | Uop o => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                            do ct <- (transBeePL_type t);
                            OK (Eunop o
                                (hd default_expr (exprlist_list_expr ces)) 
                                ct)
                 | Bop o => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                            do ct <- (transBeePL_type t);
                            OK (Ebinop o
                                  (hd default_expr (exprlist_list_expr ces)) 
                                  (hd default_expr (tl (exprlist_list_expr ces)))
                                ct)
                 end 
| Bind x t e e' t' => do ct <- (transBeePL_type t);
                      do ce <- (transBeePL_expr_expr e);
                      do ce' <- (transBeePL_expr_expr e');
                      do ct' <- (transBeePL_type t');
                      OK (Ecomma (Eassign (Evar x ct) ce ct) ce' ct') 
| Cond e e' e'' t => do ce <- (transBeePL_expr_expr e);
                     do ce' <- (transBeePL_expr_expr e');
                     do ce'' <- (transBeePL_expr_expr e'');
                     do ct <- (transBeePL_type t);
                     OK (Econdition ce ce' ce'' ct)  
| Unit t=> do ct <- (transBeePL_type t);
           OK (Eval (transBeePL_value_cvalue Vunit) ct) (* Fix me *)
| Addr l ofs => do ct <- (transBeePL_type (ltype l));
            OK (Eloc l.(lname) ofs l.(lbitfield) ct)
| Hexpr h e t => OK (Eval (Values.Vundef) Tvoid) (* FIX ME *)
end.

Definition check_var_const (e : BeePL.expr) : bool :=
match e with 
| Var x => true 
| Const c t => true 
| _ => false
end.


Definition transBeePL_expr_st (e : BeePL.expr) : res Csyntax.statement :=
match e with 
| Val v t => do vt <- (transBeePL_type t);
             OK (Sreturn (Some (Eval (transBeePL_value_cvalue v) vt))) 
| Var x => do ct <- (transBeePL_type x.(vtype));
           OK (Sreturn (Some (Evalof (Evar x.(vname) ct) ct)))
| Const c t => do ct <- (transBeePL_type t);
               OK (Sreturn (Some (Evalof (match c with 
                                      | ConsInt i => Eval (Values.Vint i) ct
                                      | ConsLong i => Eval (Values.Vlong i) ct
                                      | ConsUnit => Eval (Values.Vint (Int.repr 0)) ct
                                      end) ct)))
| App r e es t => do ce <- (transBeePL_expr_expr e);
                  do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                  do ct <- (transBeePL_type t);
                  OK (Sdo (Ecall ce ces ct))  
| Prim b es t => match b with 
                 | Ref => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                          do ct <- (transBeePL_type t);
                          OK (Sdo (Eaddrof (hd default_expr (exprlist_list_expr ces)) 
                                   ct))   
                 | Deref => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                            do ct <- (transBeePL_type t);
                            OK (Sdo (Ederef (hd default_expr (exprlist_list_expr ces)) 
                                     ct))   
                 | Massgn => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                             do ct <- (transBeePL_type t);
                             OK (Sdo (Eassign (hd default_expr (exprlist_list_expr ces))
                                              (hd default_expr (tl (exprlist_list_expr ces)))
                                      ct)) 
                 | Run h => OK (Sdo (Eval (Values.Vundef) Tvoid)) (* Fix me *)
                 | Uop o => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                            do ct <- (transBeePL_type t); 
                            OK (Sdo (Eunop o 
                                     (hd default_expr (exprlist_list_expr ces)) 
                                     ct)) 
                 | Bop o => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                            do ct <- (transBeePL_type t);
                            OK (Sdo (Ebinop o 
                                     (hd default_expr (exprlist_list_expr ces)) 
                                     (hd default_expr (tl (exprlist_list_expr ces)))
                                     ct))
                 end 
| Bind x t e e' t' => match e' with 
                      (* no side-effect case *)
                      | Var x' => do ce <- (transBeePL_expr_expr e);
                                  do ce' <- (transBeePL_expr_expr e'); 
                                  do ct <- (transBeePL_type t);
                                  do ct' <- (transBeePL_type t');
                                  do rt <- (transBeePL_type (BeePL.typeof_expr (e')));
                                  OK (Ssequence (Sdo (Eassign (Evar x ct) ce Tvoid))
                                                (Sreturn (Some (Evalof ce' rt))))
                      | Const c t => do ct <- (transBeePL_type t); 
                                     do ce <- (transBeePL_expr_expr e);
                                     do ce' <- (transBeePL_expr_expr e');
                                     OK (Ssequence (Sdo (Eassign (Evar x ct) ce Tvoid)) 
                                                   (Sreturn (Some ce')))
                      (* can produce side-effects *)
                      | _ => do ct <- (transBeePL_type t);
                             do ce <- (transBeePL_expr_expr e);
                             do ce' <- (transBeePL_expr_expr e');
                             OK (Ssequence (Sdo (Eassign (Evar x ct) ce Tvoid)) 
                                           (Sdo ce'))
                    end
| Cond e e' e'' t' => do ce <- (transBeePL_expr_expr e);
                      do ce' <- (transBeePL_expr_expr e');
                      do ce'' <- (transBeePL_expr_expr e'');
                      do ct' <- (transBeePL_type t');
                      if (check_var_const e' && check_var_const e'') (* check for expressions with side-effects *)
                      then OK (Sifthenelse ce (Sreturn (Some (Evalof ce' ct'))) (Sreturn (Some (Evalof ce'' ct'))))
                      else if (check_var_const e') then OK (Sifthenelse ce (Sreturn (Some (Evalof ce' ct'))) (Sdo ce''))
                                                   else if (check_var_const e'') 
                                                        then OK (Sifthenelse ce (Sdo ce') (Sreturn (Some (Evalof ce'' ct'))))
                                                        else OK (Sifthenelse ce (Sdo ce') (Sdo ce''))
| Unit t=> do ct <- (transBeePL_type t);
           OK (Sreturn (Some (Evalof (Eval (transBeePL_value_cvalue Vunit) ct) ct))) (* Fix me *)
| Addr l ofs => do ct <- (transBeePL_type (ltype l));
                OK (Sdo (Eloc l.(lname) ofs l.(lbitfield) ct))                    
| Hexpr h e t => OK (Sdo (Eval (Values.Vundef) Tvoid)) (* FIX ME *)
end.

Definition default_cc (fd : fun_decl) : calling_convention := 
{| cc_vararg := Some (Z.of_nat (length (fd.(args)))); cc_unproto := false; cc_structret := false |}.

(* Translates the BeePL function declaration to C function declaration *)
(* For now we have only internal functions: later change it to include the case of external function *)
Definition BeePLfd_function (fd : fun_decl) : res (Ctypes.fundef function) :=
do crt <- transBeePL_type (fd.(rtype));
do pt <- (transBeePL_types transBeePL_type (unzip2 (extract_list_rvtypes (fd.(args)))));
do vt <- (transBeePL_types transBeePL_type (unzip2 (extract_list_rvtypes (fd.(lvars)))));
do fbody <- transBeePL_expr_st (fd.(body));
OK (Internal {| fn_return := crt; 
                fn_callconv := default_cc(fd); 
                fn_params := zip (unzip1 (extract_list_rvtypes (fd.(args))))
                                 (typelist_list_type pt);
                fn_vars := zip (unzip1 (extract_list_rvtypes (fd.(lvars))))
                               (typelist_list_type vt);
                fn_body :=  fbody|}).

(* Translates the value that is assigned to global variable to C global variable data *)
Definition gconstant_init_data (g : BeePL.gconstant) : init_data :=
match g with 
| Gvalue c => match c with 
              | ConsInt i => Init_int32 i
              | ConsLong i => Init_int64 i
              | ConsUnit => Init_int32 (Int.repr 0)
              end
| Gloc p => Init_addrof p (Ptrofs.of_ints (Int.repr 0))
| Gspace z => Init_space z
end. 

(* Translates the list of global variable data to list of C global variable data *)
Fixpoint gconstants_init_datas (gs : list BeePL.gconstant) : list init_data :=
match gs with 
| nil => nil
| g :: gs => gconstant_init_data g :: gconstants_init_datas gs
end. 

(* Translates BeePL global variable to C global variable *) 
Definition BeePLgd_gd (gv : glob_decl) : res (globvar Ctypes.type)  :=
do gvt <- transBeePL_type (gv.(gtype));
OK {| gvar_info := gvt; 
      gvar_init := gconstants_init_datas(gv.(gval)); 
      gvar_readonly := false; 
      gvar_volatile := false |}.

(* Translates a BeePL declaration to C declaration *)
Definition BeePLdecl_gdef (d : BeePL.decl) : res (globdef (Ctypes.fundef function) Ctypes.type) :=
match d with 
| Fdecl (Fun fd) => do cfd <- (BeePLfd_function fd); OK (Gfun cfd)
| Gvdecl (Glob gd) => do gv <- (BeePLgd_gd gd) ; OK (Gvar gv)
(*| Tadecl ta => *) (* Fix me *)
end.

(* Translates a list of BeePL declarations to C declarations *)
Fixpoint BeePLdecls_gdefs (ds : list BeePL.decl) : 
res (list (globdef (Ctypes.fundef function) Ctypes.type)) :=
match ds with 
| nil => OK (nil)
| d :: ds => do gd <- BeePLdecl_gdef d; 
             do gds <- BeePLdecls_gdefs ds;
             OK (gd :: gds)
end.

Lemma composite_default :
build_composite_env nil = OK (PTree.empty composite).
Proof.
unfold build_composite_env; simpl; reflexivity.
Qed.

(* Missing compositie information and list of public functions *) 
Definition BeePL_compcert (m : BeePL.program) : res Csyntax.program :=
do cfd <- (BeePLdecls_gdefs (unzip2 (m.(bprog_defs)))); 
OK {| prog_defs := (zip (unzip1 (m.(bprog_defs))) cfd);
      prog_public := nil;
      prog_main := m.(bprog_main);
      prog_types := nil;
      prog_comp_env := (PTree.empty composite);
      prog_comp_env_eq := composite_default |}.

(*Definition BeePL_compcert (m : BeePL.module) : res (AST.program (Ctypes.fundef function) type) :=
do cfd <- (BeePLdecls_gdefs (unzip2 (fst(m))));
 OK (mkprogram (zip (unzip1 (fst (m))) cfd) nil (snd(m))).*)

