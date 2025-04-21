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

Definition return_czero (t : Ctypes.type) : mon Values.val :=
match t with 
| Tvoid => error (msg "Tvoid not allowed")
| Ctypes.Tint sz s a => ret (Values.Vint (Int.repr 0))
| Ctypes.Tlong s a => ret (Values.Vlong (Int64.repr 0))
| Tfloat sz a => error (msg "Tfloat not allowed")
| Tpointer t a => error (msg "Tpointer not allowed")
| Tarray t z a => error (msg "Tarray not allowed")
| Tfunction ts t cc => error (msg "Tfunction not allowed")
| Tstruct h a => error (msg "Tstruct not allowed")
| Tunion h a => error (msg "Tunion not allowed")
end.

Definition default_expr := (Eval (Values.Vundef) Tvoid).

(*Fixpoint repeat_expr_up (x : ident) (er : Csyntax.expr) (e : Csyntax.expr) (fuel : nat) {struct fuel} : Csyntax.expr :=
match fuel with
| O => Eval (Values.Vint (Int.repr 0)) (Ctypes.Tint I32 Unsigned noattr)
| S n => Econdition (Ebinop Cop.Ole (Evar x (Ctypes.Tint I32 Unsigned noattr)) er (Ctypes.Tint I32 Unsigned noattr))
           (Ecomma e (Ecomma 
                        (Ebinop Cop.Oadd 
                           (Evar x (Ctypes.Tint I32 Unsigned noattr)) 
                           (Eval (Values.Vint (Int.repr 1)) (Ctypes.Tint I32 Unsigned noattr)) (Ctypes.Tint I32 Unsigned noattr))
                        (repeat_expr_up x er e n) (typeof e)) (typeof e))
           (Evar x (Ctypes.Tint I32 Unsigned noattr)) (typeof e)
end.

Fixpoint repeat_expr_down (x : ident) (er : Csyntax.expr) (e : Csyntax.expr) (fuel : nat) {struct fuel} : Csyntax.expr :=
match fuel with
| O => Eval (Values.Vint (Int.repr 0)) (Ctypes.Tint I32 Unsigned noattr)
| S n => Econdition (Ebinop Cop.Oge (Evar x (Ctypes.Tint I32 Unsigned noattr)) er (Ctypes.Tint I32 Unsigned noattr))
           (Ecomma e (Ecomma 
                        (Ebinop Cop.Osub 
                           (Evar x (Ctypes.Tint I32 Unsigned noattr)) 
                           (Eval (Values.Vint (Int.repr 1)) (Ctypes.Tint I32 Unsigned noattr)) (Ctypes.Tint I32 Unsigned noattr))
                        (repeat_expr_up x er e n) (typeof e)) (typeof e))
           (Evar x (Ctypes.Tint I32 Unsigned noattr)) (typeof e)
end.*)
      
Fixpoint transBeePL_expr_expr (e : BeePL.expr) : mon Csyntax.expr := 
match e with 
| Val v t => ret (Eval (trans_bvalue_cvalue v) (transBeePL_type t)) 
| Var x t => ret (Evar x (transBeePL_type t))
| Const c t => match c with 
               | ConsInt i => ret (Eval (Values.Vint i) (transBeePL_type t))
               | ConsLong i => ret (Eval (Values.Vlong i) (transBeePL_type t))
               | ConsUnit => ret (Eval (Values.Vint (Int.repr 0)) (transBeePL_type t)) 
               | ConsBool b => ret (if eqb b true 
                                    then (Eval (Values.Vint (Int.repr 1)) (transBeePL_type t)) 
                                    else (Eval (Values.Vint (Int.repr 0)) (transBeePL_type t)))
               end
| App e es t => do ce <- (transBeePL_expr_expr e); 
                do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                ret (Ecall ce ces (transBeePL_type t))
| Prim b es t => match b with 
                 | Ref => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                          let ct := (transBeePL_type t) in
                          do tv <- (gensym ct);
                          ret (Ecomma (Eassign (Evar tv ct) (hd default_expr (exprlist_list_expr ces)) ct) (Eaddrof (Evar tv ct) ct)
                              ct) (* Fix me *) 
                 | Deref => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                            let ct := (transBeePL_type t) in
                            ret (Evalof (hd default_expr (exprlist_list_expr ces)) 
                                ct)   
                 | Massgn => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                             let ct := (transBeePL_type t) in
                             ret (Eassign (hd default_expr (exprlist_list_expr ces))
                                    (hd default_expr (tl (exprlist_list_expr ces)))
                                 ct)
                 | Run h => ret (Eval (Values.Vundef) Tvoid) (* Fix me *)
                 | Uop o => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                            let ct := (transBeePL_type t) in
                            ret (Eunop o
                                (hd default_expr (exprlist_list_expr ces)) 
                                ct)
                 | Bop o => if is_bop_undef t o es 
                            then let ct := (transBeePL_type t) in
                                 do v <- return_czero ct;
                                 ret (Eval v ct)
                            else do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                                 let ct := (transBeePL_type t) in
                                 ret (Ebinop o
                                        (hd default_expr (exprlist_list_expr ces)) 
                                        (hd default_expr (tl (exprlist_list_expr ces)))
                                        ct)
                 end 
| Bind x t e e' t' => let ct := (transBeePL_type t) in
                      do ce <- (transBeePL_expr_expr e);
                      do ce' <- (transBeePL_expr_expr e');
                      let ct' := (transBeePL_type t') in
                      ret (Ecomma (Eassign (Evar x ct) ce ct) ce' ct') 
| Cond e e' e'' t => do ce <- (transBeePL_expr_expr e);
                     do ce' <- (transBeePL_expr_expr e');
                     do ce'' <- (transBeePL_expr_expr e'');
                     let ct := (transBeePL_type t) in
                     ret (Econdition ce ce' ce'' ct)  
| Unit t=> let ct := (transBeePL_type t) in
           ret (Eval (trans_bvalue_cvalue Vunit) ct) (* Fix me *)
| Addr l ofs t => let ct := transBeePL_type t in
                  ret (Eloc l.(lname) ofs l.(lbitfield) ct)
| Hexpr h e t => ret (Eval (Values.Vundef) Tvoid) (* FIX ME *)
| Eapp ef ts es t => let cef := befunction_to_cefunction ef in
                     let cts := (transBeePL_types transBeePL_type ts) in
                     let ct := (transBeePL_type t) in
                     do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                     ret (Ebuiltin cef cts ces ct)
| Sfield e x t => do ce <- transBeePL_expr_expr e;
                  let ct := transBeePL_type t in
                  ret (Efield (Evalof ce (transBeePL_type (typeof_expr e))) x ct)
| For x e1 e2 d e t => error (msg "For loop cannot be translated to another C expr")
| Enone t => let ct := transBeePL_type t in 
             error (msg "Enone translation not supported yet")
| Esome e t => let ct := transBeePL_type t in
               do ce <- transBeePL_expr_expr e;
               error (msg "Esome translation not supported yet")
| Match e pes t => do ce <- transBeePL_expr_expr e;
                   error (msg "Match translation not supported yet")
end.


Definition check_var_const (e : BeePL.expr) : bool :=
match e with 
| Var x t => true 
| Const c t => true 
| _ => false
end.

Fixpoint transBeePL_expr_st (e : BeePL.expr) : mon Csyntax.statement :=
match e with 
| Val v t => let vt := (transBeePL_type t) in
             ret (Sreturn (Some (Eval (trans_bvalue_cvalue v) vt))) 
(*| Valof e t => do ct <- (transBeePL_type t);
               do ce <- (transBeePL_expr_expr e);
               ret (Sreturn (Some (Evalof ce ct)))*)
| Var x t => let ct := (transBeePL_type t) in
             ret (Sreturn (Some (Evalof (Evar x ct) ct)))
| Const c t => let ct := (transBeePL_type t) in
               ret (Sreturn (Some (Evalof (match c with 
                                      | ConsInt i => Eval (Values.Vint i) ct
                                      | ConsLong i => Eval (Values.Vlong i) ct
                                      | ConsUnit => Eval (Values.Vint (Int.repr 0)) ct
                                      | ConsBool b => if eqb b true 
                                                      then Eval (Values.Vint (Int.repr 1)) ct
                                                      else Eval (Values.Vint (Int.repr 0)) ct
                                      end) ct)))
| App e es t => do ce <- (transBeePL_expr_expr e);
                do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                let ct := (transBeePL_type t) in
                ret (Sdo (Ecall ce ces ct))  
| Prim b es t => match b with 
                 | Ref => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                          let ct := (transBeePL_type t) in
                          do tv <- (gensym ct);
                          ret (Sdo (Ecomma (Eassign (Evar tv ct) (hd default_expr (exprlist_list_expr ces)) ct) 
                                   (Eaddrof (Evar tv ct) ct)
                              ct)) (* Fix me *)
                 | Deref => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                            let ct := (transBeePL_type t) in
                            ret (Sdo (Evalof (hd default_expr (exprlist_list_expr ces)) 
                                     ct))   
                 | Massgn => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                             let ct := (transBeePL_type t) in
                             ret (Sdo (Eassign (hd default_expr (exprlist_list_expr ces))
                                              (hd default_expr (tl (exprlist_list_expr ces)))
                                      ct)) 
                 | Run h => ret (Sdo (Eval (Values.Vundef) Tvoid)) (* Fix me *)
                 | Uop o => do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                            let ct := (transBeePL_type t) in 
                            ret (Sdo (Eunop o 
                                     (hd default_expr (exprlist_list_expr ces)) 
                                     ct)) 
                 | Bop o => if is_bop_undef t o es 
                            then let ct := (transBeePL_type t) in
                                 do v <- return_czero ct;
                                 ret (Sdo (Eval v ct))
                            else do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                                 let ct := (transBeePL_type t) in
                                 ret (Sdo (Ebinop o 
                                     (hd default_expr (exprlist_list_expr ces)) 
                                     (hd default_expr (tl (exprlist_list_expr ces)))
                                     ct))
                 end 
| Bind x t e e' t' => let ct := (transBeePL_type t) in
                      do ce' <- (transBeePL_expr_st e');
                      match e with 
                      | Prim Massgn es t => do ce <- (transBeePL_expr_expr e); ret (Ssequence (Sdo ce) ce') 
                      | For x e1 e2 d e3 t => do cs <- (transBeePL_expr_st e); ret (Ssequence cs ce')                 
                      | _ => do ce <- (transBeePL_expr_expr e);
                             ret (Ssequence (Sdo (Eassign (Evar x ct) ce Tvoid)) 
                                            (ce'))
                      end
| Cond e e' e'' t' => do ce <- (transBeePL_expr_expr e);
                      do ce' <- (transBeePL_expr_st e');
                      do ce'' <- (transBeePL_expr_st e'');
                      let ct' := (transBeePL_type t') in
                      ret (Sifthenelse ce ce' ce'')
                      (*if (check_var_const e' && check_var_const e'') (* check for expressions with side-effects *)
                      then ret (Sifthenelse ce ce' ce'')
                      else if (check_var_const e') then ret (Sifthenelse ce ce' ce'')
                                                   else if (check_var_const e'') 
                                                        then ret (Sifthenelse ce ce' (Sreturn (Some (Evalof ce'' ct'))))
                                                        else ret (Sifthenelse ce ce' (Sdo ce''))*)
| Unit t=> ret Sskip (*Sreturn (Some (Eval (Values.Vint (Int.repr 0)) (Ctypes.Tint I32 Unsigned noattr)))*) (* In case of unit, we return 0 *)
| Addr l ofs t => let ct := (transBeePL_type t) in
                  ret (Sdo (Eloc l.(lname) ofs l.(lbitfield) ct))                    
| Hexpr h e t => ret (Sdo (Eval (Values.Vundef) Tvoid)) (* FIX ME *)
| Eapp ef ts es t => let cef := befunction_to_cefunction ef in
                     let cts := (transBeePL_types transBeePL_type ts) in
                     let ct := (transBeePL_type t) in
                     do ces <- (transBeePL_expr_exprs transBeePL_expr_expr es);
                     ret (Sdo (Ebuiltin cef cts ces ct))
| Sfield e x t => do ce <- transBeePL_expr_expr e;
                  let ct := transBeePL_type t in
                  ret (Sdo (Evalof (Efield (Evalof ce (transBeePL_type (typeof_expr e))) x ct) ct))
| For x e1 e2 d e t => do ce1 <- transBeePL_expr_expr e1;
                       do ce2 <- transBeePL_expr_expr e2;
                       do ce3 <- transBeePL_expr_st e;
                       if negb (is_primunsigned_int_long (typeof_expr e1) (typeof_expr e2))
                       then error (msg "The type of range expr should be always unsigned int or long")
                       else if check_range_expr e1 e2 d 
                            then error (msg "The loop has crossed the limit of 8 * 1024 * 1024")
                            else match d with
                                 | Up => ret (Sfor (Sdo (Eassign (Evar x (Ctypes.Tint I32 Unsigned noattr)) ce1 (Ctypes.Tint I32 Unsigned noattr)))
                                                   (Ebinop Cop.Ole (Evalof (Evar x (Ctypes.Tint I32 Unsigned noattr)) (Ctypes.Tint I32 Unsigned noattr))
                                                    ce2 (Ctypes.Tint I32 Unsigned noattr))
                                                   (Sdo (Epostincr Cop.Incr (Evar x (Ctypes.Tint I32 Unsigned noattr)) (Ctypes.Tint I32 Unsigned noattr)))
                                                   ce3)
                                 | Down => ret (Sfor (Sdo (Eassign (Evar x (Ctypes.Tint I32 Unsigned noattr)) ce1 (Ctypes.Tint I32 Unsigned noattr)))
                                                  (Ebinop Cop.Oge (Evalof (Evar x (Ctypes.Tint I32 Unsigned noattr)) (Ctypes.Tint I32 Unsigned noattr))
                                                     ce2 (Ctypes.Tint I32 Unsigned noattr))
                                                  (Sdo (Epostincr Cop.Decr (Evar x (Ctypes.Tint I32 Unsigned noattr)) (Ctypes.Tint I32 Unsigned noattr)))
                                                  ce3)
                                end  
| Enone t => let ct := transBeePL_type t in 
             error (msg "Enone translation not supported yet")
| Esome e t => let ct := transBeePL_type t in
               do ce <- transBeePL_expr_expr e;
               error (msg "Esome translation not supported yet")
| Match e pes t => do ce <- transBeePL_expr_expr e;
                   error (msg "Match translation not supported yet")
end.

(* Translates the BeePL function declaration to C function *) 
Definition transBeePL_function_function (fd : BeePL.function) : res (Csyntax.function) :=
let crt := (transBeePL_type (fd.(BeePL.fn_return))) in
let pt := (transBeePL_types transBeePL_type (unzip2 (fd.(fn_args)))) in 
let vt := (transBeePL_types transBeePL_type (unzip2 (fd.(BeePL.fn_vars)))) in 
match (transBeePL_expr_st (fd.(BeePL.fn_body)) (initial_generator tt)) with 
                                                | Err msg => Error msg
                                                | Res fbody g i => OK {| fn_return := crt; 
                                                                         fn_callconv := cc_default; 
                                                                         fn_params := zip (unzip1 (fd.(fn_args)))
                                                                                   (from_typelist pt);
                                                                         fn_vars := zip (unzip1 (fd.(BeePL.fn_vars)))
                                                                                 (from_typelist vt);
                                                                         fn_body :=  fbody|}
end.
                        
            

Local Open Scope error_monad_scope.

Definition transBeePL_fundef_fundef (fd : BeePL.fundef) : res Csyntax.fundef :=
match fd with 
| Internal f => do tf <- transBeePL_function_function f;
                OK (Ctypes.Internal tf)
| External ef ts t cc => let cef := (befunction_to_cefunction ef) in
                         let cts := (transBeePL_types transBeePL_type ts) in 
                         let ct := (transBeePL_type t) in
                         OK (Ctypes.External cef cts ct cc)
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
Definition transBeePLglobvar_globvar (gv : BeePL.globvar type) : (AST.globvar Ctypes.type)  :=
let gvt := transBeePL_type (gv.(gvar_info)) in
{| AST.gvar_info := gvt; 
   AST.gvar_init := (gv.(gvar_init)); 
   AST.gvar_readonly := gv.(gvar_readonly); 
   AST.gvar_volatile :=  gv.(gvar_volatile)|}.

Definition transBeePL_globdef_globdef (gd : BeePL.globdef BeePL.fundef BeeTypes.type) : res (AST.globdef fundef Ctypes.type) :=
match gd with 
| AST.Gfun f => do cf <- transBeePL_fundef_fundef f;
            OK (AST.Gfun cf)
| Gvar g => let cg := transBeePLglobvar_globvar g in 
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
Definition BeePL_compcert (p : BeePL.program) : res (Ctypes.program function) :=
  do pds <- transBeePL_globdefs_globdefs (unzip2 (p.(prog_defs)));
  (make_program (map bcomposite_ccomposite_definition (prog_types p)) (zip (unzip1 p.(prog_defs)) pds) (prog_public p) (prog_main p)).
 (* OK {| Ctypes.prog_defs := zip (unzip1 p.(prog_defs)) pds;
        Ctypes.prog_public := prog_public p;
        Ctypes.prog_main := prog_main p;
        Ctypes.prog_types := map bcomposite_ccomposite_definition (prog_types p);
        Ctypes.prog_comp_env := bcomposite_composite_env (prog_comp_env p);
        Ctypes.prog_comp_env_eq := prog_comp_env_eq p |}.*)


