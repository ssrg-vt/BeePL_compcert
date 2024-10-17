Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes.
Require Import BeePL Csyntax.

(****** Translation from BeePL to Clight ******)

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
| BeeTypes.Ftype ts n ef t => Tfunction (transBeePL_types transBeePL_type ts) 
                                        (transBeePL_type t)  
                                        {| cc_vararg := Some (Z.of_nat(n)); cc_unproto := false; cc_structret := false |}  
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

Fixpoint transBeePL_expr_expr (e : BeePL.expr) : Csyntax.expr := 
match e with 
| Var x t => Evar x (transBeePL_type t)
| Const c t => match c with 
               | ConsInt i => Eval (Values.Vint i) 
                              (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |})
               | ConsBool b => Eval (Values.Vint (bool_to_int b))
                               (Tint I8 Signed {| attr_volatile := false; attr_alignas := Some 1%N |})
               | ConsUnit => Eval (Values.Vundef) Tvoid (* FIX ME *)
               end
| App e n es t => Ecall (transBeePL_expr_expr e) (transBeePL_expr_exprs transBeePL_expr_expr es) (transBeePL_type t)  
| Bfun b n es ts t => Eval (Values.Vundef) Tvoid (* FIX ME *)
| Mbind x t e e' => Ecomma (Eassign (Evar x (transBeePL_type t)) (transBeePL_expr_expr e) Tvoid) (transBeePL_expr_expr e') Tvoid
| Cond e t e' e'' t' => Econdition (transBeePL_expr_expr e) (transBeePL_expr_expr e') (transBeePL_expr_expr e'') Tvoid
| Addr l t => Eval (Values.Vptr l (Ptrofs.of_ints (Int.repr 0))) (Tpointer (Tint I32 Signed {| attr_volatile := false; 
                                                                                           attr_alignas := Some 4%N |})
                                                                 {| attr_volatile := false; attr_alignas := Some 4%N |})
| Hexpr h e t => Eval (Values.Vundef) Tvoid (* FIX ME *)
end.

Fixpoint transBeePL_expr_st (e : BeePL.expr) : Csyntax.statement :=
match e with 
| Var x t => Sdo (Evar x (transBeePL_type t))
| Const c t => Sdo (match c with 
                    | ConsInt i => Eval (Values.Vint i) 
                              (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |})
                    | ConsBool b => Eval (Values.Vint (bool_to_int b))
                               (Tint I8 Signed {| attr_volatile := false; attr_alignas := Some 1%N |})
                    | ConsUnit => Eval (Values.Vundef) Tvoid (* FIX ME *)
                    end)
| App e n es t => Sdo (Ecall (transBeePL_expr_expr e) (transBeePL_expr_exprs transBeePL_expr_expr es) (transBeePL_type t))  
| Bfun b n es ts t => Sdo (Eval (Values.Vundef) Tvoid) (* FIX ME *)
| Mbind x t e e' => Ssequence (Sdo (Eassign (Evar x (transBeePL_type t)) (transBeePL_expr_expr e) Tvoid)) 
                              (Sdo (transBeePL_expr_expr e'))
| Cond e t e' e'' t' => Sifthenelse (transBeePL_expr_expr e) (Sdo (transBeePL_expr_expr e')) (Sdo (transBeePL_expr_expr e''))
| Addr l t => Sdo (Eval (Values.Vptr l (Ptrofs.of_ints (Int.repr 0))) (Tpointer (Tint I32 Signed {| attr_volatile := false; 
                                                                                           attr_alignas := Some 4%N |})
                                                                 {| attr_volatile := false; attr_alignas := Some 4%N |}))
| Hexpr h e t => Sdo (Eval (Values.Vundef) Tvoid) (* FIX ME *)
end.

Compute (transBeePL_expr_st (Var 2%positive (BeeTypes.Ptype (BeeTypes.Tint)))).

(* Sdo
         (Evar 2%positive
            (Tint I32 Signed
               {| attr_volatile := false; attr_alignas := Some 4%N |}))
     : statement *)
