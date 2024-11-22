Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Coq.Lists.List.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes.
Require Import BeePL_aux BeePL Csyntax.


(****** Translation from BeePL to Csyntax ******)

Section translate_types.

Variable transBeePL_type : BeeTypes.type -> Ctypes.type.

Fixpoint transBeePL_types (ts : list BeeTypes.type) : Ctypes.typelist :=
match ts with 
| nil => Tnil
| t :: ts => Tcons (transBeePL_type t) (transBeePL_types ts)
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
Fixpoint transBeePL_type (t : BeeTypes.type) : Ctypes.type :=
match t with 
| BeeTypes.Ptype (BeeTypes.Tunit) => (Tint I8 Unsigned {| attr_volatile := false; attr_alignas := Some 1%N |}) (* Fix me *)
| BeeTypes.Ptype (BeeTypes.Tint sz s) => (Tint (transBeePL_isize_cisize sz) (transBeePL_sign_csign s)
                                          {| attr_volatile := false; attr_alignas := Some (compute_align sz) |})
| BeeTypes.Ptype (BeeTypes.Tbool) => (Tint I8 Unsigned {| attr_volatile := false; attr_alignas := Some 1%N |}) 
| BeeTypes.Reftype h b => match b with 
                          | BeeTypes.Bprim (BeeTypes.Tunit) => Tpointer Tvoid {| attr_volatile := false; attr_alignas := Some 1%N |}
                          | BeeTypes.Bprim (BeeTypes.Tint sz s) => Tpointer (Tint (transBeePL_isize_cisize sz) (transBeePL_sign_csign s)
                                                                             {| attr_volatile := false; attr_alignas := Some (compute_align sz) |})
                                                              {| attr_volatile := false; attr_alignas := Some 8%N |}
                          | BeeTypes.Bprim (BeeTypes.Tbool) => Tpointer (Tint I8 Unsigned {| attr_volatile := false; 
                                                                                             attr_alignas := Some 1%N |}) 
                                                               {| attr_volatile := false; attr_alignas := Some 8%N |}
                          end
| BeeTypes.Ftype ts ef t => Tfunction (transBeePL_types transBeePL_type ts) 
                                        (transBeePL_type t)  
                                        {| cc_vararg := Some (Z.of_nat(length(ts))); cc_unproto := false; cc_structret := false |}  
end. 

Definition bool_to_int (b : bool) : int :=
match b with 
| true => (Int.repr 1)
| false => (Int.repr 0)
end.

Definition transBeePL_value_cvalue (v : BeePL_mem.value) : Values.val :=
match v with 
| BeePL_mem.Vunit => Values.Vint (Int.repr 0) (* Fix me *)
| BeePL_mem.Vint i => Values.Vint i
| BeePL_mem.Vbool b => Values.Vint (bool_to_int b)
| BeePL_mem.Vloc p => Values.Vptr p (Ptrofs.of_ints (Int.repr 0))
end.

Section transBeePL_exprs.

Variables transBeePL_expr_expr : BeePL.expr -> Csyntax.expr.

Fixpoint transBeePL_expr_exprs (es : list BeePL.expr) : Csyntax.exprlist :=
match es with 
| nil => Enil 
| e :: es => Econs (transBeePL_expr_expr e) (transBeePL_expr_exprs es)
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

Fixpoint transBeePL_expr_expr (e : BeePL.expr) : Csyntax.expr := 
match e with 
| Var x => Evar x.(BeePL_mem.vname) (transBeePL_type (x.(BeePL_mem.vtype)))
| Const c t => match c with 
               | ConsInt i => Eval (Values.Vint i) (transBeePL_type t)
               | ConsBool b => Eval (Values.Vint (bool_to_int b)) (transBeePL_type t)
               | ConsUnit => Eval (Values.Vint (Int.repr 0)) (transBeePL_type t)
               end
| App r e es t => Ecall (transBeePL_expr_expr e) (transBeePL_expr_exprs transBeePL_expr_expr es) (transBeePL_type t)  
| Prim b es t => match b with 
                 | Ref => Eaddrof (hd (Eval (Values.Vint (Int.repr 0))
                                      (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                  (exprlist_list_expr (transBeePL_expr_exprs transBeePL_expr_expr es))) 
                          (transBeePL_type t)   
                 | Deref => Ederef (hd  (Eval (Values.Vint (Int.repr 0))
                                        (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                    (exprlist_list_expr (transBeePL_expr_exprs transBeePL_expr_expr es))) 
                           (transBeePL_type t)   
                 | Massgn => Eassign (hd  (Eval (Values.Vint (Int.repr 0))
                                         (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                         (exprlist_list_expr (transBeePL_expr_exprs transBeePL_expr_expr es)))
                                    (hd  (Eval (Values.Vint (Int.repr 0))
                                       (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                 (tl (exprlist_list_expr (transBeePL_expr_exprs transBeePL_expr_expr es))))
                             (transBeePL_type t)
                 | Run h => Eval (Values.Vundef) Tvoid (* Fix me *)
                 | Uop o => Eunop (transBeePL_uop_uop o) 
                            (hd  (Eval (Values.Vint (Int.repr 0))
                                       (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                 (exprlist_list_expr (transBeePL_expr_exprs transBeePL_expr_expr es))) 
                            (transBeePL_type t) 
                 | Bop o => Ebinop (transBeePL_bop_bop o) 
                            (hd  (Eval (Values.Vint (Int.repr 0))
                                       (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                 (exprlist_list_expr (transBeePL_expr_exprs transBeePL_expr_expr es))) 
                            (hd  (Eval (Values.Vint (Int.repr 0))
                                       (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                 (tl (exprlist_list_expr (transBeePL_expr_exprs transBeePL_expr_expr es))))
                            (transBeePL_type t)
                 end 
| Bind x t e e' t' => Ecomma (Eassign (Evar x (transBeePL_type t)) (transBeePL_expr_expr e) (transBeePL_type t)) 
                             (transBeePL_expr_expr e') (transBeePL_type t')
| Cond e e' e'' t => Econdition (transBeePL_expr_expr e) (transBeePL_expr_expr e') (transBeePL_expr_expr e'') (transBeePL_type t)
| Addr l => Eval (Values.Vptr l.(BeePL_mem.lname) (Ptrofs.of_ints (Int.repr 0))) (transBeePL_type l.(BeePL_mem.ltype))
| Hexpr h e t => Eval (Values.Vundef) Tvoid (* FIX ME *)
end.

Definition check_var_const (e : BeePL.expr) : bool :=
match e with 
| Var x => true 
| Const c t => true 
| _ => false
end.


Definition transBeePL_expr_st (e : BeePL.expr) : Csyntax.statement :=
match e with 
| Var x => Sreturn (Some (Evalof (Evar x.(BeePL_mem.vname) (transBeePL_type x.(BeePL_mem.vtype))) (transBeePL_type x.(BeePL_mem.vtype))))
| Const c t => Sreturn (Some (Evalof (match c with 
                                      | ConsInt i => Eval (Values.Vint i) (transBeePL_type t)
                                      | ConsBool b => Eval (Values.Vint (bool_to_int b)) (transBeePL_type t)
                                      | ConsUnit => Eval (Values.Vint (Int.repr 0)) (transBeePL_type t)
                                      end) (transBeePL_type t)))
| App r e es t => Sdo (Ecall (transBeePL_expr_expr e) (transBeePL_expr_exprs transBeePL_expr_expr es) (transBeePL_type t))  
| Prim b es t => match b with 
                 | Ref =>  Sdo (Eaddrof (hd  (Eval (Values.Vint (Int.repr 0))
                                        (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                        (exprlist_list_expr (transBeePL_expr_exprs transBeePL_expr_expr es))) 
                                (transBeePL_type t))   
                 | Deref => Sdo (Ederef (hd  (Eval (Values.Vint (Int.repr 0))
                                        (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                         (exprlist_list_expr (transBeePL_expr_exprs transBeePL_expr_expr es))) 
                                 (transBeePL_type t))   
                 | Massgn => Sdo (Eassign (hd  (Eval (Values.Vint (Int.repr 0))
                                               (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                               (exprlist_list_expr (transBeePL_expr_exprs transBeePL_expr_expr es)))
                                          (hd  (Eval (Values.Vint (Int.repr 0))
                                               (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                               (tl (exprlist_list_expr (transBeePL_expr_exprs transBeePL_expr_expr es))))
                                 (transBeePL_type t)) 
                 | Run h => Sdo (Eval (Values.Vundef) Tvoid) (* Fix me *)
                 | Uop o => Sdo (Eunop (transBeePL_uop_uop o) 
                                 (hd  (Eval (Values.Vint (Int.repr 0))
                                       (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                      (exprlist_list_expr (transBeePL_expr_exprs transBeePL_expr_expr es))) 
                                 (transBeePL_type t)) 
                 | Bop o => Sdo (Ebinop (transBeePL_bop_bop o) 
                            (hd  (Eval (Values.Vint (Int.repr 0))
                                       (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                 (exprlist_list_expr (transBeePL_expr_exprs transBeePL_expr_expr es))) 
                            (hd  (Eval (Values.Vint (Int.repr 0))
                                       (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                 (tl (exprlist_list_expr (transBeePL_expr_exprs transBeePL_expr_expr es))))
                            (transBeePL_type t))
                 end 
| Bind x t e e' t' => match e' with 
                      (* no side-effect case *)
                      | Var x' => Ssequence (Sdo (Eassign (Evar x (transBeePL_type t)) 
                                                            (transBeePL_expr_expr e) 
                                                    Tvoid)) 
                                               (Sreturn (Some (Evalof (transBeePL_expr_expr e') (transBeePL_type (BeePL.typeof_expr (e'))))))
                      | Const c t => Ssequence (Sdo (Eassign (Evar x (transBeePL_type t)) (transBeePL_expr_expr e) Tvoid)) 
                                               (Sreturn (Some (transBeePL_expr_expr e')))
                      (* can produce side-effects *)
                      | _ => Ssequence (Sdo (Eassign (Evar x (transBeePL_type t)) (transBeePL_expr_expr e) Tvoid)) 
                                       (Sdo (transBeePL_expr_expr e'))
                    end
| Cond e e' e'' t' => if (check_var_const e' && check_var_const e'') (* check for expressions with side-effects *)
                      then Sifthenelse (transBeePL_expr_expr e) 
                                       (Sreturn (Some (Evalof (transBeePL_expr_expr e') (transBeePL_type t')))) 
                                       (Sreturn (Some (Evalof (transBeePL_expr_expr e'') (transBeePL_type t'))))
                      else if (check_var_const e') then Sifthenelse (transBeePL_expr_expr e) 
                                                        (Sreturn (Some (Evalof (transBeePL_expr_expr e')(transBeePL_type t')))) 
                                                        (Sdo (transBeePL_expr_expr e''))
                                                   else if (check_var_const e'') 
                                                        then Sifthenelse (transBeePL_expr_expr e) 
                                                                         (Sdo (transBeePL_expr_expr e')) 
                                                                         (Sreturn (Some (Evalof (transBeePL_expr_expr e'') 
                                                                                                 (transBeePL_type t'))))
                                                        else Sifthenelse (transBeePL_expr_expr e) 
                                                                         (Sdo (transBeePL_expr_expr e'))
                                                                         (Sdo (transBeePL_expr_expr e''))
                      
| Addr l => Sdo (Eval (Values.Vptr l.(BeePL_mem.lname) (Ptrofs.of_ints (Int.repr 0))) (transBeePL_type l.(BeePL_mem.ltype)))
| Hexpr h e t => Sdo (Eval (Values.Vundef) Tvoid) (* FIX ME *)
end.

Definition default_cc (fd : fun_decl) : calling_convention := 
{| cc_vararg := Some (Z.of_nat (length (fd.(args)))); cc_unproto := false; cc_structret := false |}.

(* For now we have only internal functions: later change it to include both the case *)
Definition BeePLfd_function (fd : fun_decl) : (Ctypes.fundef function) :=
Internal {| fn_return := transBeePL_type (fd.(rtype)); 
            fn_callconv := default_cc(fd); 
            fn_params := zip (unzip1 (BeePL_mem.extract_list_rvtypes (fd.(args))))
                             (typelist_list_type (transBeePL_types transBeePL_type 
                               (unzip2 (BeePL_mem.extract_list_rvtypes (fd.(args))))));
            fn_vars := zip (unzip1 (BeePL_mem.extract_list_rvtypes (fd.(lvars))))
                             (typelist_list_type (transBeePL_types transBeePL_type 
                               (unzip2 (BeePL_mem.extract_list_rvtypes (fd.(lvars))))));
            fn_body := transBeePL_expr_st (fd.(body)) |}.

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

Fixpoint gconstants_init_datas (gs : list BeePL.gconstant) : list init_data :=
match gs with 
| nil => nil
| g :: gs => gconstant_init_data g :: gconstants_init_datas gs
end. 

Definition BeePLgd_gd (gv : globv) : globvar Ctypes.type  :=
{| gvar_info := transBeePL_type (gv.(gtype)); 
   gvar_init := gconstants_init_datas(gv.(gval)); 
   gvar_readonly := false; 
   gvar_volatile := false |}.

Definition BeePLdecl_gdef (d : BeePL.decl) : (globdef (Ctypes.fundef function) type) :=
match d with 
| Fdecl fd => Gfun (BeePLfd_function fd)
| Gvdecl gd => Gvar (BeePLgd_gd gd)
(*| Tadecl ta => *) (* Fix me *)
end.

Fixpoint BeePLdecls_gdefs (ds : list BeePL.decl) : 
list (globdef (Ctypes.fundef function) type) :=
match ds with 
| nil => nil
| d :: ds => BeePLdecl_gdef d :: BeePLdecls_gdefs ds
end.

(* Fix me: I want to produce Csyntax.program *)  
(* Missing compositie information and list of public functions *)
Definition BeePL_compcert (m : BeePL.module) : (*Csyntax.program*) AST.program (Ctypes.fundef function) type :=
  mkprogram (zip (unzip1 (fst (m))) (BeePLdecls_gdefs (unzip2 (fst(m))))) nil (snd(m)).
