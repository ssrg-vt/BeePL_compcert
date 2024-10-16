Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes.
Require Import BeePL Clight.

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

Definition dident := 1%positive.

Fixpoint transBeePL_expr (e: BeePL.expr) : Clight.statement :=
match e with 
| Var x t => Sset x (Ecast (Econst_int (Int.repr 0) (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |})) 
                    (transBeePL_type t))
| Const c t => match c with 
               | ConsInt i => Clight.Ssequence 
                             (Sset dident (Etempvar dident (transBeePL_type t))) 
                             (Sset dident (Econst_int i (transBeePL_type t)))
               | _ => Sskip
               end
| _ => Sskip
end.

