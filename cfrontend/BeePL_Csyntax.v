Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Coq.Lists.List.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes Coqlib.
Require Import BeePL_aux BeePL Csyntax Errors.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

(****** Translation from BeePL to Csyntax ******)

Section translate_types.

Variable transBeePL_type : BeeTypes.type -> res Ctypes.type.

(* Translates a list of BeePL types to list of Clight types *) 
Fixpoint transBeePL_types (ts : list BeeTypes.type) : res Ctypes.typelist :=
match ts with 
| nil => OK Tnil
| t :: ts => do ct <- (transBeePL_type t);
             do cts <- (transBeePL_types ts);
             OK (Tcons ct cts)
end.

End translate_types.

Fixpoint typelist_list_type (ts : Ctypes.typelist) : list type :=
match ts with
| Tnil => nil
| Tcons t ts => t :: typelist_list_type ts
end. 

Definition transBeePL_isize_cisize (sz : BeeTypes.intsize) : intsize :=
match sz with 
| BeeTypes.I8 => I8
| BeeTypes.I16 => I16
| BeeTypes.I32 => I32
end.

Definition transBeePL_sign_csign (s : BeeTypes.signedness) : signedness :=
match s with 
| BeeTypes.Signed => Signed
| BeeTypes.Unsigned => Unsigned
end.

Definition compute_align (i : BeeTypes.intsize) : N :=
match i with 
| BeeTypes.I8 => 1%N
| BeeTypes.I16 => 2%N
| BeeTypes.I32 => 4%N
end.

(* Translation of BeePL types to Clight Types *) 
Fixpoint transBeePL_type (t : BeeTypes.type) : res Ctypes.type :=
match t with 
| BeeTypes.Ptype (BeeTypes.Tunit) => OK (Tint I8 Unsigned {| attr_volatile := false; attr_alignas := Some 1%N |}) (* Fix me *)
| BeeTypes.Ptype (BeeTypes.Tint sz s) => OK (Tint (transBeePL_isize_cisize sz) (transBeePL_sign_csign s)
                                              {| attr_volatile := false; attr_alignas := Some (compute_align sz) |})
| BeeTypes.Ptype (BeeTypes.Tbool) => OK (Tint I8 Unsigned {| attr_volatile := false; attr_alignas := Some 1%N |}) 
| BeeTypes.Reftype h b => match b with 
                          | BeeTypes.Bprim (BeeTypes.Tunit) => OK (Tpointer Tvoid {| attr_volatile := false; attr_alignas := Some 1%N |})
                          | BeeTypes.Bprim (BeeTypes.Tint sz s) => OK (Tpointer (Tint (transBeePL_isize_cisize sz) (transBeePL_sign_csign s)
                                                                             {| attr_volatile := false; attr_alignas := Some (compute_align sz) |})
                                                              {| attr_volatile := false; attr_alignas := Some 8%N |})
                          | BeeTypes.Bprim (BeeTypes.Tbool) => OK (Tpointer (Tint I8 Unsigned {| attr_volatile := false; 
                                                                                             attr_alignas := Some 1%N |}) 
                                                                   {| attr_volatile := false; attr_alignas := Some 8%N |})
                          end
| BeeTypes.Ftype ts ef t => do ats <- (transBeePL_types transBeePL_type ts);
                            do rt <- (transBeePL_type t);
                            OK (Tfunction ats rt {| cc_vararg := Some (Z.of_nat(length(ts))); cc_unproto := false; cc_structret := false |})  
end.

Definition bool_to_int (b : bool) : int :=
match b with 
| true => (Int.repr 1)
| false => (Int.repr 0)
end.

(* Translates BeePL values to C values *)
Definition transBeePL_value_cvalue (v : BeePL_mem.value) : Values.val :=
match v with 
| BeePL_mem.Vunit => Values.Vint (Int.repr 0) (* Fix me *)
| BeePL_mem.Vint i => Values.Vint i
| BeePL_mem.Vbool b => Values.Vint (bool_to_int b)
| BeePL_mem.Vloc p => Values.Vptr p (Ptrofs.of_ints (Int.repr 0))
end.

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

Definition transBeePL_uop_uop (uop : BeePL.uop) : Cop.unary_operation :=
match uop with 
| Notbool => Cop.Onotbool 
| Notint => Cop.Onotint
| Neg => Cop.Oneg
end.

Definition transBeePL_bop_bop (bop : BeePL.bop) : Cop.binary_operation :=
match bop with 
| Plus => Cop.Oadd
| Minus => Cop.Osub
| Mult => Cop.Omul
| Div => Cop.Odiv
| And => Cop.Oand
| Or => Cop.Oor
| Xor => Cop.Oxor
| Shl => Cop.Oshl
| Shr => Cop.Oshr
| Eq => Cop.Oeq
| Neq => Cop.One
| Lt => Cop.Olt
| Lte => Cop.Ole
| Gt => Cop.Ogt
| Gte => Cop.Oge
end.

Fixpoint exprlist_list_expr (es: Csyntax.exprlist) : list expr :=
match es with 
| Enil => nil 
| Econs e1 es => (e1 :: exprlist_list_expr es)
end.

Fixpoint transBeePL_expr_expr (e : BeePL.expr) : res Csyntax.expr := 
match e with 
| Var x => do xt <- (transBeePL_type (x.(BeePL_mem.vtype)));
           OK (Evar x.(BeePL_mem.vname) xt)
| Const c t => match c with 
               | ConsInt i => do it <- (transBeePL_type t); OK (Eval (Values.Vint i) it)
               | ConsBool b => do bt <- (transBeePL_type t); OK (Eval (Values.Vint (bool_to_int b)) bt)
               | ConsUnit => do ut <- (transBeePL_type t); OK (Eval (Values.Vint (Int.repr 0)) ut) 
               end
| App r e es t => do ce <- (transBeePL_expr_expr e); 
                  do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                  do ct <- (transBeePL_type t);
                  OK (Ecall ce ces ct)
| Prim b es t => match b with 
                 | Ref => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                          do ct <- (transBeePL_type t);
                          OK (Eaddrof (hd (Eval (Values.Vint (Int.repr 0))
                                        (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                      (exprlist_list_expr ces)) 
                              ct) 
                 | Deref => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                            do ct <- (transBeePL_type t);
                            OK (Ederef (hd  (Eval (Values.Vint (Int.repr 0))
                                        (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                       (exprlist_list_expr ces)) 
                                ct)   
                 | Massgn => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                             do ct <- (transBeePL_type t);
                             OK (Eassign (hd  (Eval (Values.Vint (Int.repr 0))
                                         (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                         (exprlist_list_expr ces))
                                    (hd  (Eval (Values.Vint (Int.repr 0))
                                       (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                     (tl (exprlist_list_expr ces)))
                                 ct)
                 | Run h => OK (Eval (Values.Vundef) Tvoid) (* Fix me *)
                 | Uop o => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                            do ct <- (transBeePL_type t);
                            OK (Eunop (transBeePL_uop_uop o) 
                                (hd  (Eval (Values.Vint (Int.repr 0))
                                       (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                (exprlist_list_expr ces)) 
                                ct)
                 | Bop o => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                            do ct <- (transBeePL_type t);
                            OK (Ebinop (transBeePL_bop_bop o) 
                                  (hd  (Eval (Values.Vint (Int.repr 0))
                                       (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                   (exprlist_list_expr ces)) 
                                  (hd  (Eval (Values.Vint (Int.repr 0))
                                       (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                    (tl (exprlist_list_expr ces)))
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
| Addr l => do ct <- (transBeePL_type l.(BeePL_mem.ltype));
            OK (Eval (Values.Vptr l.(BeePL_mem.lname) (Ptrofs.of_ints (Int.repr 0))) ct)
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
| Var x => do ct <- (transBeePL_type x.(BeePL_mem.vtype));
           OK (Sreturn (Some (Evalof (Evar x.(BeePL_mem.vname) ct) ct)))
| Const c t => do ct <- (transBeePL_type t);
               OK (Sreturn (Some (Evalof (match c with 
                                      | ConsInt i => Eval (Values.Vint i) ct
                                      | ConsBool b => Eval (Values.Vint (bool_to_int b)) ct
                                      | ConsUnit => Eval (Values.Vint (Int.repr 0)) ct
                                      end) ct)))
| App r e es t => do ce <- (transBeePL_expr_expr e);
                  do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                  do ct <- (transBeePL_type t);
                  OK (Sdo (Ecall ce ces ct))  
| Prim b es t => match b with 
                 | Ref => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                          do ct <- (transBeePL_type t);
                          OK (Sdo (Eaddrof (hd  (Eval (Values.Vint (Int.repr 0))
                                        (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                        (exprlist_list_expr ces)) 
                                   ct))   
                 | Deref => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                            do ct <- (transBeePL_type t);
                            OK (Sdo (Ederef (hd  (Eval (Values.Vint (Int.repr 0))
                                        (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                         (exprlist_list_expr ces)) 
                                     ct))   
                 | Massgn => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                             do ct <- (transBeePL_type t);
                             OK (Sdo (Eassign (hd  (Eval (Values.Vint (Int.repr 0))
                                               (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                               (exprlist_list_expr ces))
                                              (hd  (Eval (Values.Vint (Int.repr 0))
                                               (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                               (tl (exprlist_list_expr ces)))
                                      ct)) 
                 | Run h => OK (Sdo (Eval (Values.Vundef) Tvoid)) (* Fix me *)
                 | Uop o => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                            do ct <- (transBeePL_type t); 
                            OK (Sdo (Eunop (transBeePL_uop_uop o) 
                                     (hd (Eval (Values.Vint (Int.repr 0))
                                       (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                      (exprlist_list_expr ces)) 
                                     ct)) 
                 | Bop o => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                            do ct <- (transBeePL_type t);
                            OK (Sdo (Ebinop (transBeePL_bop_bop o) 
                                     (hd (Eval (Values.Vint (Int.repr 0))
                                         (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                        (exprlist_list_expr ces)) 
                                     (hd (Eval (Values.Vint (Int.repr 0))
                                         (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                      (tl (exprlist_list_expr ces)))
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
                      
| Addr l => do ct <- (transBeePL_type l.(BeePL_mem.ltype)); 
            OK (Sdo (Eval (Values.Vptr l.(BeePL_mem.lname) (Ptrofs.of_ints (Int.repr 0))) ct))
| Hexpr h e t => OK (Sdo (Eval (Values.Vundef) Tvoid)) (* FIX ME *)
end.

Definition default_cc (fd : fun_decl) : calling_convention := 
{| cc_vararg := Some (Z.of_nat (length (fd.(args)))); cc_unproto := false; cc_structret := false |}.

(* Translates the BeePL function declaration to C function declaration *)
(* For now we have only internal functions: later change it to include the case of external function *)
Definition BeePLfd_function (fd : fun_decl) : res (Ctypes.fundef function) :=
do crt <- transBeePL_type (fd.(rtype));
do pt <- (transBeePL_types transBeePL_type (unzip2 (BeePL_mem.extract_list_rvtypes (fd.(args)))));
do vt <- (transBeePL_types transBeePL_type (unzip2 (BeePL_mem.extract_list_rvtypes (fd.(lvars)))));
do fbody <- transBeePL_expr_st (fd.(body));
OK (Internal {| fn_return := crt; 
                fn_callconv := default_cc(fd); 
                fn_params := zip (unzip1 (BeePL_mem.extract_list_rvtypes (fd.(args))))
                                 (typelist_list_type pt);
                fn_vars := zip (unzip1 (BeePL_mem.extract_list_rvtypes (fd.(lvars))))
                               (typelist_list_type vt);
                fn_body :=  fbody|}).

(* Translates the value that is assigned to global variable to C global variable data *)
Definition gconstant_init_data (g : BeePL.gconstant) : init_data :=
match g with 
| Gvalue c => match c with 
              | ConsInt i => Init_int32 i
              | ConsBool b => Init_int8 (bool_to_int b)
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
Definition BeePLgd_gd (gv : globv) : res (globvar Ctypes.type)  :=
do gvt <- transBeePL_type (gv.(gtype));
OK {| gvar_info := gvt; 
      gvar_init := gconstants_init_datas(gv.(gval)); 
      gvar_readonly := false; 
      gvar_volatile := false |}.

(* Translates a BeePL declaration to C declaration *)
Definition BeePLdecl_gdef (d : BeePL.decl) : res (globdef (Ctypes.fundef function) type) :=
match d with 
| Fdecl fd => do cfd <- (BeePLfd_function fd); OK (Gfun cfd)
| Gvdecl gd => do gv <- (BeePLgd_gd gd) ; OK (Gvar gv)
(*| Tadecl ta => *) (* Fix me *)
end.

(* Translates a list of BeePL declarations to C declarations *)
Fixpoint BeePLdecls_gdefs (ds : list BeePL.decl) : 
res (list (globdef (Ctypes.fundef function) type)) :=
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
Definition BeePL_compcert (m : BeePL.module) : res Csyntax.program :=
do cfd <- (BeePLdecls_gdefs (unzip2 (fst(m)))); 
OK {| prog_defs := (zip (unzip1 (fst (m))) cfd);
      prog_public := nil;
      prog_main := snd(m);
      prog_types := nil;
      prog_comp_env := (PTree.empty composite);
      prog_comp_env_eq := composite_default |}.

(*Definition BeePL_compcert (m : BeePL.module) : res (AST.program (Ctypes.fundef function) type) :=
do cfd <- (BeePLdecls_gdefs (unzip2 (fst(m))));
 OK (mkprogram (zip (unzip1 (fst (m))) cfd) nil (snd(m))).*)

