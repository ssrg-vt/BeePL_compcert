Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Coq.Lists.List.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes.
Require Import BeePL_aux BeePL BeePL_values BeeTypes BeePL_mem Errors.
From mathcomp Require Import all_ssreflect. 

Local Open Scope error_monad_scope.

(***** Type checker for BeePL *****)

(* Any number can be treated as bool: 0 for false and rest for true *)
Definition check_type_bool (t : type) : bool :=
match classify_bool t with 
| bool_case_i => true
| bool_case_l => true 
| bool_default => false
end.

(* Type-checking of constants *)
(* We type check it with weak type: wtype because it is 
   hard to get size and signedness from constants *) 
Definition type_constant (c : BeePL_values.constant) : wtype :=
match c with 
| ConsInt i => Twint
| ConsLong i => Twlong
| ConsUnit => Twunit
end.

(* Type-checking of values *)
(* We type check it with weak type: wtype because it is 
   hard to get size and signedness from values *) 
Definition type_value (v : value) : wtype :=
match v with 
| Vunit => Twunit
| Vint i => Twint
| Vint64 i => Twlong
| Vloc p ofs => Twptr
end.

Section Type_check_exprs.
Variable type_check_expr : ty_context -> store_context -> expr -> res (type * effect).

Fixpoint type_check_exprs (Gamma : ty_context) (Sigma : store_context) (es : list expr) : res (list type * effect) :=
match es with 
| nil => OK (nil, nil)
| e :: es => do (te, efe) <- type_check_expr Gamma Sigma e;
             do (tes, efes) <- type_check_exprs Gamma Sigma es;
             OK (te :: tes, efe ++ efes)
end.

End Type_check_exprs.

Definition mem_ident := 2%positive.

Fixpoint type_check_expr (Gamma : ty_context) (Sigma : store_context) (e : expr) : res (type * effect) :=
match e with 
| Val v t => OK (t, nil)
| Var x t => match (PTree.get x (extend_context Gamma x t)) with 
             | Some t' => if (eq_type t t') then OK(t, nil) else Error (msg "Var type does not match") 
             | None => Error (msg "Variable not found")
             end
| Const c t => OK (t, nil)
| App e es t => do (ft, efe) <- type_check_expr Gamma Sigma e;
                do (ts, efs) <- type_check_exprs type_check_expr Gamma Sigma es;
                match ft with 
                | Ftype ts1 ef rt1 => if eq_types eq_type ts ts1 && eq_type rt1 t
                                      then OK (rt1, efe ++ ef ++ efs) 
                                      else Error (msg "Function declaration does not match the inferred type") 
                | _ => Error (msg "Is not a function type")
                end
| Prim b es t => match b with 
                 | Ref => match es with 
                          | e :: nil => do (te, ef) <- type_check_expr Gamma Sigma e;
                                        match te with 
                                        | Ptype bt => if eq_type t (Reftype mem_ident (Bprim bt) (attr_of_primitive_type bt)) 
                                                      then OK (Reftype mem_ident (Bprim bt) (attr_of_primitive_type bt), (ef ++ (Alloc mem_ident :: nil)))
                                                      else Error (msg "Reftype does not match the inferred type")
                                        | _ => Error (msg "Only primitive types are allowed to be allocated in memory")
                                        end
                          |  _ => Error (msg "Wrong number of arguments to Ref")
                          end
                 | Deref => match es with 
                            | e :: nil => do (te, ef) <- type_check_expr Gamma Sigma e;
                                          match te with 
                                          | Reftype mem_ident (Bprim bt) a => if eq_type t (Ptype bt) 
                                                                              then OK (Ptype bt, (ef ++ (Read mem_ident :: nil)))
                                                                              else Error (msg "Dereftype does not match the inferred type")
                                          | _ => Error (msg "Argument of dereferencing should be a ref type")
                                          end
                          |  _ => Error (msg "Wrong number of arguments to Deref")
                          end
                 | Massgn => match es with 
                             | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr Gamma Sigma e1;
                                                  match te1 with 
                                                  | Reftype mem_ident (Bprim bt) a => do (te2, ef2) <- type_check_expr Gamma Sigma e2;
                                                                                      match te2 with 
                                                                                      | Ptype bt => if eq_type t (Ptype Tunit)
                                                                                                    then OK (Ptype Tunit, ef1 ++ ef2 ++ (Write mem_ident :: nil))
                                                                                                    else Error (msg "Massgntype does not match the inferred type")
                                                                                      | _ => Error (msg "Only primitive types are allowed in memory assignment")
                                                                                      end 
                                                 | _ => Error (msg "First argument of Massgn should be a reftype")
                                                 end
                            | _ => Error (msg " Wrong number of arguments to Massgn")
                            end                                                         
                 | Uop o => match es with 
                            | e :: nil => do (te, ef) <- type_check_expr Gamma Sigma e;
                                          if negb(is_reftype te) && negb(is_unittype te) && eq_type t te
                                          then OK (te, ef)
                                          else Error (msg "Reftype and unitype are not allowed as arguments of unary operators")
                            | _ => Error (msg "Wrong number of arguments to Unary operator")
                            end
                 | Bop o => match es with 
                            | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr Gamma Sigma e1;
                                                 do (te2, ef2) <- type_check_expr Gamma Sigma e2;
                                                 if (eq_type te1 te2 && negb(is_reftype te1) && negb(is_unittype te1) && eq_effect ef1 ef2 && eq_type te1 t) 
                                                 then OK(te1, ef1)
                                                 else Error (msg "Reftype and unitype are not allowed as arguments of binary operators") 
                            | _ => Error (msg "Wrong number of arguments to Binary operators") 
                            end
                 | Run h => Error (msg "Run is not yet supported")
                 end
| Bind x t e1 e2 t' => do (te1, ef1) <- type_check_expr Gamma Sigma e1;
                       do (te2, ef2) <- type_check_expr (extend_context Gamma x t) Sigma e2;
                       if eq_type te2 t'
                       then OK (te2, ef1 ++ ef2)
                       else Error (msg "Type of bind does not match the inferred type")
| Cond e1 e2 e3 t =>  do (te1, ef1) <- type_check_expr Gamma Sigma e1;
                      do (te2, ef2) <- type_check_expr Gamma Sigma e2;
                      do (te3, ef3) <- type_check_expr Gamma Sigma e3;
                      if check_type_bool te1 && eq_type te2 te3 && eq_effect ef2 ef3 && eq_type t te2
                      then OK (te1, ef1 ++ ef2)
                      else Error (msg "Type of cond does not match the inferred type")
| Unit t => OK (Ptype Tunit, nil)
| Addr l ofs t =>  match PTree.get l.(lname) Sigma with 
                   | Some (Reftype mem_ident bt a) => if eq_type t (Reftype mem_ident bt a)
                                              then OK (Reftype mem_ident bt a, nil)
                                              else Error (msg "Type of location does not match the inferred type")
                   | Some _ => Error (msg "Wrong type inferred for location")
                   | None => Error (msg "Location not found")
                   end
| Hexpr h e t =>  Error (msg "Hexpr is not yet supported")
| Eapp ef ts es t => Error (msg "Not found")
end.


