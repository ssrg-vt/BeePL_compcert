Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes.
Require Import BeePL Csyntax.


(****** Translation from BeePL to Csyntax ******)

Section translate_types.

Variable transBeePL_type : BeeTypes.type -> Ctypes.type.

Fixpoint transBeePL_types (ts : list BeeTypes.type) : Ctypes.typelist :=
match ts with 
| nil => Tnil
| t :: ts => Tcons (transBeePL_type t) (transBeePL_types ts)
end.

End translate_types.

(* Translation of BeePL types to Clight Types *) 
Fixpoint transBeePL_type (t : BeeTypes.type) : Ctypes.type :=
match t with 
| BeeTypes.Ptype (BeeTypes.Tunit) => Tvoid
| BeeTypes.Ptype (BeeTypes.Tint) => (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |})
| BeeTypes.Ptype (BeeTypes.Tbool) => (Tint I8 Unsigned {| attr_volatile := false; attr_alignas := Some 1%N |}) 
| BeeTypes.Reftype h b => match b with 
                          | BeeTypes.Bprim (BeeTypes.Tunit) => Tpointer Tvoid {| attr_volatile := false; attr_alignas := None |}
                          | BeeTypes.Bprim (BeeTypes.Tint) => Tpointer (Tint I32 Signed {| attr_volatile := false; 
                                                                                           attr_alignas := Some 4%N |})
                                                              {| attr_volatile := false; attr_alignas := Some 4%N |}
                          | BeeTypes.Bprim (BeeTypes.Tbool) => Tpointer (Tint I8 Unsigned {| attr_volatile := false; 
                                                                                             attr_alignas := Some 1%N |}) 
                                                               {| attr_volatile := false; attr_alignas := Some 4%N |}
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
| Var x t => Evar x (transBeePL_type t)
| Const c t => match c with 
               | ConsInt i => Eval (Values.Vint i) 
                              (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |})
               | ConsBool b => Eval (Values.Vint (bool_to_int b))
                               (Tint I8 Signed {| attr_volatile := false; attr_alignas := Some 1%N |})
               | ConsUnit => Eval (Values.Vint (Int.repr 0)) 
                              (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |})
               end
| App e es t => Ecall (transBeePL_expr_expr e) (transBeePL_expr_exprs transBeePL_expr_expr es) (transBeePL_type t)  
| Prim b es t => match b with 
                 | Ref => Eval (Values.Vundef) Tvoid (* Fix me *)
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
| Addr l t => Eval (Values.Vptr l (Ptrofs.of_ints (Int.repr 0))) (Tpointer (Tint I32 Signed {| attr_volatile := false; 
                                                                                           attr_alignas := Some 4%N |})
                                                                 {| attr_volatile := false; attr_alignas := Some 4%N |})
| Hexpr h e t => Eval (Values.Vundef) Tvoid (* FIX ME *)
end.

Definition check_var_const (e : BeePL.expr) : bool :=
match e with 
| Var x t => true 
| Const c t => true 
| _ => false
end.

Fixpoint transBeePL_expr_st (e : BeePL.expr) : Csyntax.statement :=
match e with 
| Var x t => Sreturn (Some (Evalof (Evar x (transBeePL_type t)) (transBeePL_type t)))
| Const c t => Sreturn (Some (Evalof (match c with 
                                      | ConsInt i => Eval (Values.Vint i) 
                                                       (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |})
                                      | ConsBool b => Eval (Values.Vint (bool_to_int b))
                                                        (Tint I8 Signed {| attr_volatile := false; attr_alignas := Some 1%N |})
                                      | ConsUnit => Eval (Values.Vint (Int.repr 0)) 
                                                      (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |})
                                      end) (transBeePL_type t)))
| App e es t => Sdo (Ecall (transBeePL_expr_expr e) (transBeePL_expr_exprs transBeePL_expr_expr es) (transBeePL_type t))  
| Prim b es t => match b with 
                 | Ref => Sdo (Eval (Values.Vundef) Tvoid) (* Fix me *)
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
                      | Var x' t' => Ssequence (Sdo (Eassign (Evar x (transBeePL_type t)) 
                                                            (transBeePL_expr_expr e) 
                                                    Tvoid)) 
                                               (Sreturn (Some (Evalof (transBeePL_expr_expr e') (transBeePL_type (BeePL.typeof (e'))))))
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
                      
| Addr l t => Sdo (Eval (Values.Vptr l (Ptrofs.of_ints (Int.repr 0))) (Tpointer (Tint I32 Signed {| attr_volatile := false; 
                                                                                           attr_alignas := Some 4%N |})
                                                                 {| attr_volatile := false; attr_alignas := Some 4%N |}))
| Hexpr h e t => Sdo (Eval (Values.Vundef) Tvoid) (* FIX ME *)
end.


