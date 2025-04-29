Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Coq.Lists.List.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes Ctyping.
Require Import BeePL_aux BeePL BeePL_values BeeTypes BeePL_mem Errors Csyntaxdefs.
From mathcomp Require Import all_ssreflect. 

Local Open Scope error_monad_scope.

(***** Type checker for BeePL *****)

(***** Map containing information about external calls *****)
Definition ef_info : Type := list type * (type * effect).

Definition ef_empty_map := PTree.empty ef_info.

Definition ef_env : Type := PTree.t ef_info.

Notation "m [ a <- b ]" := (PTree.set (ident_of_string a) b m) (at level 10, left associativity).
Notation "m [ a ]" := (PTree.get (ident_of_string a) m) (at level 10, left associativity).

(* Add all external functions needed for BeePL *)
Definition  beepl_ef_env : ef_env :=
ef_empty_map ["bpf_get_prandom_u32" <- (nil, (Ptype (BeeTypes.Tint I32 Unsigned noattr), nil))].

Definition get_ef_type (efenv : ef_env) (s : string) : res ef_info :=
match efenv[s] with 
| Some t => OK t
| None => Error (msg "TYPE ERROR: The type signature of external function is not present in ef_env")
end.

(* Type-checking of constants *)
(* We type check it with weak type: wtype because it is 
   hard to get size and signedness from constants *) 
Definition type_constant (c : BeePL_values.constant) : wtype :=
match c with 
| ConsInt i => Twint
| ConsLong i => Twlong
| ConsUnit => Twunit
| ConsBool b => Twbool
end.

(* Type-checking of values *)
(* We type check it with weak type: wtype because it is 
   hard to get size and signedness from values *) 
Definition type_value (v : value) : wtype :=
match v with 
| Vunit => Twunit
| Vbool b => Twbool
| Vint i => Twint
| Vint64 i => Twlong
| Vloc p ofs => Twptr
end.

Section Trans_ctypes_btypes.

Variable trans_ctype_btype : Ctypes.type -> res BeeTypes.type.

Fixpoint trans_ctypes_btypes (ct : typelist) : res (list BeeTypes.type) :=
match ct with 
| Tnil => OK nil
| Tcons ct cts => do bt <- trans_ctype_btype ct;
                  do bts <- trans_ctypes_btypes cts;
                  OK (bt :: bts)
end.

End Trans_ctypes_btypes.

Definition trans_ctype_btype (ct : Ctypes.type) : res BeeTypes.type :=
match ct with 
| Tvoid => OK (Ptype Tunit)
| Ctypes.Tint sz s a => OK (BeeTypes.Ptype (Tint sz s a))
| Ctypes.Tlong s a => OK (BeeTypes.Ptype (Tlong s a))
| Tfloat _ _ => Error (msg "TYPE ERROR: Float is not supported in BeePL")
| Tpointer t a => match t with 
                  | Tvoid => OK (Reftype 1%positive (Bprim Tunit) a)
                  | Ctypes.Tint sz s a => OK (Reftype 1%positive (Bprim (Tint sz s a)) a)
                  | Ctypes.Tlong s a => OK (Reftype 1%positive (Bprim (Tlong s a)) a)
                  | _ => Error (msg "TYPE ERROR: Not supported in ref type")
                  end 
| Tarray t z a => Error (msg "TYPE ERROR: Array is not supported in BeePL")
| Tfunction ts t cc => Error (msg "TYPE ERROR: Cannot compute the effect, hence translation is not possible from ctype to btype in case of function")
| Tstruct x a => OK (Stype x a)
| Tunion x a => Error (msg "TYPE ERROR: Union is not supported in BeePL")
end.

Section Type_check_exprs. 

Variable type_check_expr : bcomposite_env -> ty_context -> store_context -> expr -> res (type * effect).

Fixpoint type_check_exprs (cenv : bcomposite_env) (Gamma : ty_context) (Sigma : store_context) (es : list expr) : res (list type * effect) :=
match es with 
| nil => OK (nil, nil)
| e :: es => do (te, efe) <- type_check_expr cenv Gamma Sigma e;
             do (tes, efes) <- type_check_exprs cenv Gamma Sigma es;
             OK (te :: tes, efe ++ efes)
end.

End Type_check_exprs.

Fixpoint type_check_expr (cenv : bcomposite_env) (Gamma : ty_context) (Sigma : store_context) (e : expr) : res (type * effect) :=
match e with 
| Val v t => OK (t, nil)
| Var x t => match (PTree.get x (extend_context Gamma x t)) with 
             | Some t' => if (eq_type t t') then OK(t, nil) else Error (msg "TYPE ERROR: Var type does not match") 
             | None => Error (msg "TYPE ERROR: Variable not found")
             end
| Const c t => OK (t, nil)
| App e es t => do (ft, efe) <- type_check_expr cenv Gamma Sigma e;
                do (ts, efs) <- type_check_exprs type_check_expr cenv Gamma Sigma es;
                match ft with 
                | Ftype ts1 ef rt1 => if eq_types eq_type ts ts1 && eq_type rt1 t
                                      then OK (rt1, efe ++ ef ++ efs) 
                                      else Error (msg "TYPE ERROR: Function declaration does not match the inferred type") 
                | _ => Error (msg "TYPE ERROR: Not a function type")
                end
| Prim b es t => match b with 
                 | Ref => match es with 
                          | e :: nil => do (te, ef) <- type_check_expr cenv Gamma Sigma e;
                                        match te with 
                                        | Ptype bt => if eq_type t (Reftype mem_ident (Bprim bt) (attr_of_primitive_type bt)) 
                                                      then OK (Reftype mem_ident (Bprim bt) (attr_of_primitive_type bt), (ef ++ (Alloc mem_ident :: nil)))
                                                      else Error (msg "TYPE ERROR: Reftype does not match the inferred type")
                                        | _ => Error (msg "TYPE ERROR: Only primitive types are allowed to be allocated in memory")
                                        end
                          |  _ => Error (msg "TYPE ERROR: Wrong number of arguments to Ref")
                          end
                 | Deref => match es with 
                            | e :: nil => do (te, ef) <- type_check_expr cenv Gamma Sigma e;
                                          match te with 
                                          | Reftype mem_ident (Bprim bt) a => if eq_type t (Ptype bt) 
                                                                              then OK (Ptype bt, (ef ++ (Read mem_ident :: nil)))
                                                                              else Error (msg "Dereftype does not match the inferred type")
                                          | _ => Error (msg "TYPE ERROR: Argument of dereferencing should be a ref type")
                                          end
                          |  _ => Error (msg "TYPE ERROR: Wrong number of arguments to Deref")
                          end
                 | Massgn => match es with 
                             | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                  match te1 with 
                                                  | Reftype mem_ident (Bprim bt) a => do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                                                      match te2 with 
                                                                                      | Ptype bt => if eq_type t (Ptype Tunit)
                                                                                                    then OK (Ptype Tunit, ef1 ++ ef2 ++ (Write mem_ident :: nil))
                                                                                                    else Error (msg "Massgntype does not match the inferred type")
                                                                                      | _ => Error (msg "TYPE ERROR: Only primitive types are allowed in memory assignment")
                                                                                      end 
                                                 | _ => Error (msg "TYPE ERROR: First argument of Massgn should be a reftype")
                                                 end
                            | _ => Error (msg "TYPE ERROR: Wrong number of arguments to Massgn")
                            end                                                         
                 | Uop o => match o with 
                            | Cop.Onotbool => match es with 
                                              | e :: nil => do (te, ef) <- type_check_expr cenv Gamma Sigma e;
                                                            if is_primbool te && eq_type t te
                                                            then OK (te, ef)
                                                            else Error (msg "TYPE ERROR: Wrong argument type to negation bool operator, it expects bool as argument")
                                              | _ => Error (msg "TYPE ERROR: Wrong number of arguments to Unary operator")
                                              end
                            | Cop.Onotint => match es with 
                                              | e :: nil => do (te, ef) <- type_check_expr cenv Gamma Sigma e;
                                                            if (is_primint te || is_primlong te) && eq_type t te
                                                            then OK (te, ef)
                                                            else Error (msg "TYPE ERROR: Wrong argument type to bitwise not operator, it expects int or long as argument")
                                              | _ => Error (msg "TYPE ERROR: Wrong number of arguments to Unary operator")
                                              end
                            | Cop.Oneg => match es with 
                                          | e :: nil => do (te, ef) <- type_check_expr cenv Gamma Sigma e;
                                                        if (is_primint te || is_primlong te) && eq_type t te
                                                        then OK (te, ef)
                                                        else Error (msg "TYPE ERROR: Wrong argument type to unary minus operator, it expects int or long as argument")
                                          | _ => Error (msg "TYPE ERROR: Wrong number of arguments to Unary operator")
                                          end
                            | Cop.Oabsfloat => Error (msg "TYPE ERROR: Floating-point absolute value operator is not supported in BeePL")
                            end 
                 | Bop o => match o with 
                            | Cop.Oadd => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                               do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                               if (eq_type te1 te2 && (is_primint te1 || is_primlong te1) && eq_type te1 t) 
                                                               then OK(te1, ef1 ++ ef2)
                                                               else Error (msg "TYPE ERROR: Wrong argument types to add operator, it expects int or long as argument")
                                          | _ => Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end 
                            | Cop.Osub => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                               do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                               if (eq_type te1 te2 && (is_primint te1 || is_primlong te1) && eq_type te1 t) 
                                                               then OK(te1, ef1 ++ ef2)
                                                               else Error (msg "TYPE ERROR: Wrong argument types to add operator, it expects int or long as argument") 
                                          | _ => Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.Omul => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                           do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                           if (eq_type te1 te2 && (is_primint te1 || is_primlong te1) && eq_type te1 t) 
                                                           then OK(te1, ef1 ++ ef2)
                                                           else Error (msg "TYPE ERROR: Wrong argument types to mul operator, it expects int or long as argument")
                                          | _ => Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end 
                            | Cop.Odiv => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                           do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                           if (eq_type te1 te2 && (is_primint32 te1 || is_primlong te1) && eq_type te1 t) 
                                                           then OK(te1, ef1 ++ ef2)
                                                           else Error (msg "TYPE ERROR: Wrong argument types to div operator, it expects int or long as argument")
                                          | _ => Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.Omod => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                           do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                           if (eq_type te1 te2 && (is_primint32 te1 || is_primlong te1) && eq_type te1 t) 
                                                           then OK(te1, ef1 ++ ef2)
                                                           else Error (msg "TYPE ERROR: Wrong argument types to mod operator, it expects int or long as argument") 
                                          | _ => Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.Oand => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                           do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                           if (eq_type te1 te2 && (is_primint te1 || is_primlong te1) && eq_type te1 t) 
                                                           then OK(te1, ef1 ++ ef2)
                                                           else Error (msg "TYPE ERROR: Wrong argument types to and operator, it expects bool as argument")
                                          | _ => Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.Oor => match es with 
                                         | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                           do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                           if (eq_type te1 te2 && (is_primint te1 || is_primlong te1) && eq_type te1 t) 
                                                           then OK(te1, ef1 ++ ef2)
                                                           else Error (msg "TYPE ERROR: Wrong argument types to or operator, it expects bool as argument")
                                         | _ => Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                         end
                            | Cop.Oxor => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                           do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                           if (eq_type te1 te2 && (is_primint te1 || is_primlong te1) && eq_type te1 t) 
                                                           then OK(te1, ef1 ++ ef2)
                                                           else Error (msg "TYPE ERROR: Wrong argument types to xor operator, it expects int or long as argument")
                                          | _ =>  Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.Oshl => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                           do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                           if (eq_type te1 te2 && (is_primint32 te1 || is_primlong te1) && eq_type te1 t) 
                                                           then OK(te1, ef1 ++ ef2)
                                                           else Error (msg "TYPE ERROR: Wrong argument types to shl operator, it expects int or long as argument")
                                          | _ =>  Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.Oshr => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                           do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                           if (eq_type te1 te2 && (is_primint32 te1 || is_primlong te1) && eq_type te1 t) 
                                                           then OK(te1, ef1 ++ ef2)
                                                           else Error (msg "TYPE ERROR: Wrong argument types to shr operator, it expects int or long as argument")
                                          | _ =>  Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.Oeq => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                               do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                               if (eq_type te1 te2 && (is_primint te1 || is_primlong te1 || is_primbool te2) && eq_type te1 t) 
                                                               then OK(Ptype Tbool, ef1 ++ ef2)
                                                               else Error (msg "TYPE ERROR: Wrong argument types to eq operator, it expects int or long as argument")
                                          | _ =>  Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.One => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                               do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                               if (eq_type te1 te2 && (is_primint te1 || is_primlong te1 || is_primbool te2) && eq_type te1 t) 
                                                               then OK(Ptype Tbool, ef1 ++ ef2)
                                                               else Error (msg "TYPE ERROR: Wrong argument types to ne operator, it expects int or long as argument")
                                          | _ =>  Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.Olt => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                               do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                               if (eq_type te1 te2 && (is_primint te1 || is_primlong te1) && eq_type (Ptype Tbool) t) 
                                                               then OK(Ptype Tbool, ef1 ++ ef2)
                                                               else Error (msg "TYPE ERROR: Wrong argument types to lt operator, it expects int or long as argument")
                                          | _ =>  Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.Ogt => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                               do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                               if (eq_type te1 te2 && (is_primint te1 || is_primlong te1) && eq_type te1 t) 
                                                               then OK(Ptype Tbool, ef1 ++ ef2)
                                                               else Error (msg "TYPE ERROR: Wrong argument types to gt operator, it expects int or long as argument")
                                          | _ =>  Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.Ole => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                               do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                               if (eq_type te1 te2 && (is_primint te1 || is_primlong te1) && eq_type te1 t) 
                                                               then OK(Ptype Tbool, ef1 ++ ef2)
                                                               else Error (msg "TYPE ERROR: Wrong argument types to le operator, it expects int or long as argument")
                                          | _ =>  Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.Oge => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                               do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                               if (eq_type te1 te2 && (is_primint te1 || is_primlong te1) && eq_type te1 t) 
                                                               then OK(Ptype Tbool, ef1 ++ ef2)
                                                               else Error (msg "TYPE ERROR: Wrong argument types to ge operator, it expects int or long as argument")
                                          | _ =>  Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            end
                 | Run h => Error (msg "TYPE ERROR: Run is not yet supported")
                 end
| Bind x t e1 e2 t' => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                       do (te2, ef2) <- type_check_expr cenv (extend_context Gamma x t) Sigma e2;
                       if eq_type te2 t'
                       then OK (te2, ef1 ++ ef2)
                       else Error (msg "TYPE ERROR: Type of bind does not match the inferred type")
| Cond e1 e2 e3 t =>  do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                      do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                      do (te3, ef3) <- type_check_expr cenv Gamma Sigma e3;
                      if is_primbool te1 && eq_type te2 te3 && eq_effect ef2 ef3 && eq_type t te2
                      then OK (te2, ef1 ++ ef2)
                      else Error (msg "TYPE ERROR: Type of cond does not match the inferred type")
| Unit t => OK (Ptype Tunit, nil)
| Addr l ofs t =>  match PTree.get l.(lname) Sigma with 
                   | Some (Reftype mem_ident bt a) => if eq_type t (Reftype mem_ident bt a)
                                              then OK (Reftype mem_ident bt a, nil)
                                              else Error (msg "Type of location does not match the inferred type")
                   | Some _ => Error (msg "TYPE ERROR: Wrong type inferred for location")
                   | None => Error (msg "TYPE ERROR: Location not found")
                   end
| Hexpr h e t =>  Error (msg "TYPE ERROR: Hexpr is not yet supported")
| Eapp ef ts es t => Error (msg "TYPE ERROR: We have no use case of builtin function as of now")
| Sfield e x t => do (te, ef) <- type_check_expr cenv Gamma Sigma e;
                  match te with 
                  | Stype id a => match cenv!id with 
                                  | Some co => do ct <- type_of_member a x (bmembers_cmembers co.(co_members));
                                               do bt <- trans_ctype_btype ct;
                                               if eq_type t bt 
                                               then OK (te, nil)
                                               else Error (msg "TYPE ERROR: Wrong type inferred for the struct field")
                                  | None => Error (msg "TYPE ERROR: Struct information not found in composite env")
                                  end
                  | _ => Error (msg "TYPE ERROR: Should be a struct type")
                  end
| For e1 e2 d e t =>   do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                       do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                       do (te, ef) <- type_check_expr cenv Gamma Sigma e;
                       if (eq_type te1 te2 
                           && eq_effect ef1 nil 
                           && eq_effect ef2 nil 
                           && ((is_primint te1) || (is_primlong te2))
                           && eq_type te t)
                       then OK(te, ef1 ++ ef2 ++ ef)
                       else Error (msg "TYPE ERROR: The range type should be unsigned int or long and the inferred type does not match")
                                                          
| Enone t => Error (msg "TYPE ERROR: Enone type checking not supported yet")
| Esome e t => Error (msg "TYPE ERROR: Esome type checking not supported yet")
| Match e pes t => Error (msg "TYPE ERROR: Match type checking not supported yet")
end.

Open Scope string_scope.

Fixpoint bind_vars (Gamma : ty_context) (l: list (ident * type)) : ty_context :=
match l with
| nil => Gamma
| (id, ty) :: l => bind_vars (PTree.set id ty Gamma) l
end.

Fixpoint bind_globdef (Gamma: ty_context) (l: list (ident * globdef fundef type)) : ty_context :=
match l with
| nil => Gamma
| (id, Gfun fd) :: l => bind_globdef (PTree.set id (type_of_fundef fd) Gamma) l
| (id, Gvar v) :: l => bind_globdef (PTree.set id v.(gvar_info) Gamma) l
end.

Definition type_check_function (cenv : bcomposite_env) (Gamma : ty_context) (Sigma : store_context) (fn : function) : res string :=
let Gamma' := bind_vars (bind_vars Gamma fn.(fn_args)) fn.(fn_vars) in
match type_check_expr cenv Gamma' Sigma fn.(fn_body) with 
| Error msg => Error msg
| OK tef => if eq_type fn.(fn_return) tef.1 && eq_effect fn.(fn_effect) tef.2
             then OK "SUCCESS: Function type checks!" 
             else Error (msg "TYPE ERROR: Type from function body does not match with the return type in the function declaration")
end.

Definition type_check_fundef (efenv : ef_env) (cenv : bcomposite_env) (Gamma : ty_context) (Sigma : store_context) (fn : BeePL.fundef) : res string :=
match fn with 
| Internal f => type_check_function cenv Gamma Sigma f 
| External ef ts t cc => match ef with 
                         | EF_external fn fs => do efs <- get_ef_type efenv (get_name_eapp ef);
                                                if eq_type t (get_rt_eapp ef) 
                                                   && eq_types eq_type ts (get_at_eapp ef) 
                                                   && eq_types eq_type ts (fst efs) 
                                                   && eq_type t (fst (snd efs))
                                                   && eq_effect (get_ef_eapp ef) (snd (snd efs)) 
                                                then OK "SUCCESS: Fundef type checks!" 
                                                else Error (msg "TYPE ERROR: Type of external function is not as expected")
                         end
end.

(* Fix me *)
Definition type_check_globvar (efenv : ef_env) (Gamma : ty_context) (Sigma : store_context) (gv : BeePL.globvar type) : res type :=
OK (gv.(gvar_info)).

Section Type_check_globdefs.

Variable type_check_globdef : ef_env -> bcomposite_env -> ty_context -> store_context -> BeePL.globdef BeePL.fundef BeeTypes.type -> res string.

Fixpoint type_check_globdefs (efenv : ef_env) (cenv : bcomposite_env) (Gamma : ty_context) (Sigma : store_context) (gds : list (BeePL.globdef BeePL.fundef BeeTypes.type)) : res string :=
match gds with 
| nil => OK "SUCCESS: Program type checks!"
| gd :: gds => do gds1 <- type_check_globdef efenv cenv Gamma Sigma gd;
               type_check_globdefs efenv cenv Gamma Sigma gds
end.
  
End Type_check_globdefs.

Definition type_check_globdef (efenv : ef_env) (cenv : bcomposite_env) (Gamma : ty_context) (Sigma : store_context)  (gd : BeePL.globdef BeePL.fundef BeeTypes.type) : res string :=
match gd with 
| AST.Gfun f => type_check_fundef efenv cenv Gamma Sigma f  
| Gvar g => do gt <- type_check_globvar efenv Gamma Sigma g;
            OK "SUCCESS: Program type checks!"
end.

(* Fix Store context: How to compute this? *) 
Definition type_check_program (p : BeePL.program) : res string :=
let Gamma := bind_globdef (PTree.empty _) p.(prog_defs) in
let cenv := p.(prog_comp_env) in 
type_check_globdefs type_check_globdef beepl_ef_env cenv Gamma empty_context (unzip2 (p.(prog_defs))).



