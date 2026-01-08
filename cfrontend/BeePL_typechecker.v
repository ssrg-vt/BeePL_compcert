Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Coq.Lists.List.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes Ctyping.
Require Import BeePL_aux BeePL BeePL_values BeeTypes BeePL_mem Errors Csyntaxdefs BeePL_notations.
Require Import BeePL_helper_functions.
From mathcomp Require Import all_ssreflect. 

Local Open Scope error_monad_scope.

(***** Type checker for BeePL *****)

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
| Voption o => Twot
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
                                                                                                      
Fixpoint type_check_expr (cenv : bcomposite_env) (Gamma : ty_context) (Sigma : store_context) (e : expr) {struct e} : res (type * effect) :=
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
                | Ftype ts1 ef rt1 => if check_fun_ptr_fun ts1 ts
                                      then OK (rt1, efe ++ ef ++ efs) 
                                      else Error (msg "TYPE ERROR: Function case does not match the inferred type") 
                | Ptrtype (Fptype ts1 ef rt1) => if check_fun_ptr_fun ts1 ts
                                                 then OK (rt1, efe ++ ef ++ efs) 
                                                 else Error (msg "TYPE ERROR: Function pointer case does not match the inferred type")

                | _ => Error (msg "TYPE ERROR: Not a function type")
                end
| Prim b es t => match b with 
                 | Ref => match es with 
                          | e :: nil => do (te, ef) <- type_check_expr cenv Gamma Sigma e;
                                        match te with 
                                        | Vtype bt => if eq_type t (Ptrtype (Reftype (Bprim bt) (attr_of_primitive_type bt))) 
                                                        then OK (Ptrtype (Reftype (Bprim bt) (attr_of_primitive_type bt)), (ef ++ (Alloc :: nil)))
                                                        else Error (msg "TYPE ERROR: Reftype does not match the inferred type")
                                        | _ => Error (msg "TYPE ERROR: Only primitive types are allowed to be allocated in memory")
                                        end
                          |  _ => Error (msg "TYPE ERROR: Wrong number of arguments to Ref")
                          end
                 | Deref => match es with 
                            | e :: nil => do (te, ef) <- type_check_expr cenv Gamma Sigma e;
                                          match te with 
                                          | Ptrtype pt => if eq_type t (get_data_type pt) 
                                                          then if (is_option_ptr_type pt == false) 
                                                               then OK (get_data_type pt, (ef ++ (Read :: nil)))
                                                               else Error (msg "Deref is not allowed on option type")
                                                          else Error (msg "Deref type does not match the inferred type")
                                          | _ => Error (msg "TYPE ERROR: Argument of dereferencing should be a ref type")
                                          end
                          |  _ => Error (msg "TYPE ERROR: Wrong number of arguments to Deref")
                          end
                 | Massgn => match es with 
                             | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                  match te1 with 
                                                  | Ptrtype pt => do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                                  let bt := get_data_type pt in
                                                                  match te2 with 
                                                                  | bt => if eq_type t Utype
                                                                          then if (is_option_ptr_type pt == false) 
                                                                               then OK (Utype, ef1 ++ ef2 ++ (Write :: nil))
                                                                               else Error (msg "Massgntype not allowed on option type")
                                                                          else Error (msg "Massgn type does not match the inferred type")
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
                                                               then OK(Vtype Tbool, ef1 ++ ef2)
                                                               else Error (msg "TYPE ERROR: Wrong argument types to eq operator, it expects int or long as argument")
                                          | _ =>  Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.One => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                               do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                               if (eq_type te1 te2 && (is_primint te1 || is_primlong te1 || is_primbool te2) && eq_type te1 t) 
                                                               then OK(Vtype Tbool, ef1 ++ ef2)
                                                               else Error (msg "TYPE ERROR: Wrong argument types to ne operator, it expects int or long as argument")
                                          | _ =>  Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.Olt => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                               do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                               if (eq_type te1 te2 && (is_primint te1 || is_primlong te1) && eq_type (Vtype Tbool) t) 
                                                               then OK(Vtype Tbool, ef1 ++ ef2)
                                                               else Error (msg "TYPE ERROR: Wrong argument types to lt operator, it expects int or long as argument")
                                          | _ =>  Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.Ogt => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                               do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                               if (eq_type te1 te2 && (is_primint te1 || is_primlong te1) && eq_type te1 t) 
                                                               then OK(Vtype Tbool, ef1 ++ ef2)
                                                               else Error (msg "TYPE ERROR: Wrong argument types to gt operator, it expects int or long as argument")
                                          | _ =>  Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.Ole => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                               do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                               if (eq_type te1 te2 && (is_primint te1 || is_primlong te1) && eq_type te1 t) 
                                                               then OK(Vtype Tbool, ef1 ++ ef2)
                                                               else Error (msg "TYPE ERROR: Wrong argument types to le operator, it expects int or long as argument")
                                          | _ =>  Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.Oge => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                               do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                               if (eq_type te1 te2 && (is_primint te1 || is_primlong te1) && eq_type te1 t) 
                                                               then OK(Vtype Tbool, ef1 ++ ef2)
                                                               else Error (msg "TYPE ERROR: Wrong argument types to ge operator, it expects int or long as argument")
                                          | _ =>  Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            end
                 | Cast t => match t with 
                             | Vtype vt => match es with 
                                           | e1 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                          match te1 with 
                                                          | Vtype vt1 => do rt <- allowed_cast vt1 vt;
                                                                         OK(Vtype rt, ef1)
                                                          | _ => Error (msg "TYPE ERROR: Wrong argument type to casting operator, it expects bool, int, or long")
                                                          end
                                           | _ => Error (msg "TYPE ERROR: Wrong number of arguments to Casting Operator")
                                           end 
                             | _ => Error (msg "TYPE ERROR: Casting is only allowed from one value type to another")
                             end
                 end
| Bind x t e1 e2 t' => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                       do (te2, ef2) <- type_check_expr cenv (extend_context Gamma x t) Sigma e2;
                       if eq_type te2 t'
                       then OK (te2, ef1 ++ ef2)
                       else Error (msg "TYPE ERROR: Type of bind does not match the inferred type")
| Cond e1 e2 e3 t =>  do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                      do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                      do (te3, ef3) <- type_check_expr cenv Gamma Sigma e3;
                      if is_primbool te1 && eq_type te2 te3 && eq_type t te2
                      then OK (te2, ef1 ++ ef2 ++ ef3)
                      else Error (msg "TYPE ERROR: Type of cond does not match the inferred type")
| Unit t => OK (Utype, nil)
| Addr l ofs t =>  match PTree.get l.(lname) Sigma with 
                   | Some (Ptrtype (Reftype bt a)) => if eq_type t (Ptrtype (Reftype bt a))
                                              then OK (Ptrtype (Reftype bt a), nil)
                                              else Error (msg "Type of location does not match the inferred type")
                   | Some _ => Error (msg "TYPE ERROR: Wrong type inferred for location")
                   | None => Error (msg "TYPE ERROR: Location not found")
                   end
(*| Eapp ef ts es t => Error (msg "TYPE ERROR: We have no use case of builtin function as of now")*)
| Sinit x ids es t => do (tes, efs) <- type_check_exprs type_check_expr cenv Gamma Sigma es;
                        match t with 
                        | Stype id a => match cenv!id with 
                                        | Some co => do cts <- type_of_members 
                                                               (combine (map Ctypes.attr_of_type (transBeePL_types transBeePL_type tes)) ids) 
                                                                            (bmembers_cmembers co.(co_members));
                                                     do bts <- trans_ctypes_btypes trans_ctype_btype cts;
                                                     if eq_types eq_type tes bts 
                                                     then OK(t, efs)
                                                     else Error (msg "TYPE ERROR: Wrong type inferred for the struct initialization")
                                       | None => Error (msg "TYPE ERROR: Struct fields not found in composite env")
                        end
                     | _ => Error (msg "TYPE ERROR: Struct created in BeePL should always be reftype")
                    end
| Sfield e x t => do (te, ef) <- type_check_expr cenv Gamma Sigma e;
                  match te with 
                  | Stype id a => match cenv!id with 
                                  | Some co => do ct <- type_of_member a x (bmembers_cmembers co.(co_members));
                                               do bt <- trans_ctype_btype ct;
                                               if eq_type t bt 
                                               then OK (bt, ef)
                                               else Error (msg "TYPE ERROR: Wrong type inferred for the struct field")
                                  | None => Error (msg "TYPE ERROR: The field accessed from the struct is not found in composite env")
                                  end
                  | Ptrtype (Reftype (Bstruct id a) _) => match cenv!id with 
                                             | Some co => do ct <- type_of_member a x (bmembers_cmembers co.(co_members));
                                               do bt <- trans_ctype_btype ct;
                                               if eq_type t bt 
                                               then OK (bt, ef)
                                               else Error (msg "TYPE ERROR: Wrong type inferred for the struct field")
                                             | None => Error (msg "TYPE ERROR: The field accessed from the struct is not found in composite env")
                                            end
                  | _ => Error (msg "TYPE ERROR: Should be a struct type")
                  end
| For e1 e2 d e t =>   do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                       do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                       do (te, ef) <- type_check_expr cenv Gamma Sigma e;
                       let fv1 := free_variables e1 in 
                       let fv2 := free_variables e2 in
                       let fv := free_variables e in 
                       if (eq_type te1 te2 
                           && eq_effect ef1 nil 
                           && eq_effect ef2 nil 
                           && ((is_primint te1) || (is_primlong te2))
                           && eq_type te t && disjoint_vars fv fv1 && disjoint_vars fv fv2)
                       then OK(te, ef1 ++ ef2 ++ ef)
                       else Error (msg "TYPE ERROR: The range type should be unsigned int or long and the inferred type does not match")
                                                          
| Enone t => match t with 
             | Ptrtype t' => if is_option_ptr_type t' 
                             then OK(t, nil) 
                             else Error (msg "TYPE ERROR: Type of Enone should be an option to ref type")
             | _ => Error (msg "TYPE ERROR: Type of Enone should be an option type")
             end
| Esome e t => do (te, ef) <- type_check_expr cenv Gamma Sigma e;
               match t with 
               | Ptrtype (Otype t') => if is_option_ptr_type t' && eq_type te (Ptrtype t') 
                               then OK(t, ef)
                               else Error (msg "TYPE ERROR: Type of Esome should be an option to ref type")
               | _ => Error (msg "TYPE ERROR: Type of Esome should be an option type")
               end
| Match e ps es t => let fvs :=  get_patterns_var ps in 
                     do (te, ef) <- type_check_expr cenv Gamma Sigma e;
                     do (tes, efs) <- type_check_exprs type_check_expr cenv (extends_context Gamma fvs (construct_list_type t (length fvs))) Sigma es;
                     match te with 
                     | Ptrtype t' => if is_option_ptr_type t'
                                     then if all_eq_types tes 
                                          then if eq_type t (hd tunit tes) 
                                               then OK(t, ef ++ efs)
                                               else Error (msg "TYPE ERROR: Inferref type of match does not match with expected type")
                                          else Error (msg "TYPE ERROR: All branches of match should be of same type")
                                     else Error (msg "TYPE ERROR: Type of Match expr should be an option type")
                     | Bytes => if all_eq_types tes && eq_type t (hd tunit tes) 
                                then OK(t, ef ++ efs)
                                else Error (msg "TYPE ERROR: Type of Match expr should be an option to ref type and all its elements should be of same type")
                     | _ => Error (msg "TYPE ERROR: Type of Match expr should be an option or bytes type")
                     end
| Ebytes es t => Error (msg "TYPE ERROR: Type checking of Bitstrings are not supported yet")
| Ainit a t es t' => do (ts, efs) <- type_check_exprs type_check_expr cenv Gamma Sigma es;
                     do aty <- get_array_elm_ty t;
                     if is_atype t 
                     then if is_atype t'
                          then if all_eq_type aty ts 
                               then OK (t', efs)   (* Should we consider write effect in array initialization? *)
                               else Error (msg "TYPE ERROR: Elements assigned to an array must match the array’s element type")
                          else Error (msg "TYPE ERROR: The return type of array initialization should be array type")
                     else Error (msg "TYPE ERROR: The type of array should be an array type")
| Aaccess a t n t' => do aty <- get_array_elm_ty t;   (* Index n is within the array bound is checked by the BeePL compiler *)
                      if is_atype t 
                      then if eq_type aty t' 
                           then OK (t', nil) (* Shoule we consider read effect in array access? *)
                           else Error (msg "TYPE ERROR: The type of array access should be the type of array element")
                      else Error (msg "TYPE ERROR: The type of array accessed should be an array type")
                     
end.

Open Scope string_scope.

Definition type_check_function (cenv : bcomposite_env) (Gamma : ty_context) (Sigma : store_context) (fn : function) : res string :=
let Gamma' := bind_vars (bind_vars Gamma fn.(fn_args)) fn.(fn_vars) in
match type_check_expr cenv Gamma' Sigma fn.(fn_body) with 
| Error msg => Error msg
| OK tef =>  if eq_type fn.(fn_return) tef.1 && eq_effect fn.(fn_effect) tef.2 
             then if is_ptrtype tef.1 == false 
                  then OK "SUCCESS: Function type checks!" 
                  else Error (msg "TYPE ERROR: Function declaration cannot return an address")
             else Error (msg "TYPE ERROR: Type from function body does not match with the return type in the function declaration")
end.

Definition type_check_fundef (efenv : ef_env) (cenv : bcomposite_env) (Gamma : ty_context) (Sigma : store_context) (fn : BeePL.fundef) : res string :=
match fn with 
| Internal f => type_check_function cenv Gamma Sigma f 
| External ef ts t cc => match ef with 
                         | EF_external fn fs => do efs <- get_ef_type efenv (get_name_eapp ef);
                                                if eq_type t (get_rt_eapp ef) 
                                                then if eq_types eq_type ts (get_at_eapp ef)
                                                     then if eq_types eq_type ts (fst efs) 
                                                          then if eq_type t (fst (snd efs))
                                                               then if eq_effect (get_ef_eapp ef) (snd (snd efs)) 
                                                                    then OK "SUCCESS: Fundef type checks!" 
                                                                    else Error (msg "TYPE ERROR: Effect of external function is not as expected")
                                                               else Error (msg "TYPE ERROR: Return type of external function is not as expected")
                                                          else Error (msg "TYPE ERROR: Argument types of external function is not as expected")
                                                      else Error (msg "TYPE ERROR: Argument types of external function is not as given in signature")
                                                else Error (msg "TYPE ERROR: Return type of external function is not as given in signature")
                                                
                         end
end.

Definition type_check_globvar (efenv : ef_env) (Gamma : ty_context) (Sigma : store_context) (gv : BeePL.globvar type) : res (type * effect) :=
do ef <- construct_ef_gvars gv.(gvar_init);
OK (gv.(gvar_info), ef).


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

(* Store context: Not needed in the executable type checker because location is never used by programmer, it only comes as intermediate results in semantics *) 
Definition type_check_program (p : BeePL.program) : res string :=
let sb := check_get_fundef_sec p.(prog_defs) in 
let defs := map (fun '(id, gd, _) => (id, gd)) p.(prog_defs) in
let Gamma := bind_globdef (PTree.empty _) defs in
let cenv := p.(prog_comp_env) in 
if sb then
type_check_globdefs type_check_globdef beepl_ef_env cenv Gamma empty_context (unzip2 defs)
else Error (msg "TYPE ERROR: Section attribute related to program type").
