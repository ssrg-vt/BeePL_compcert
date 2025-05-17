Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Coq.Lists.List.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes Coqlib SimplExpr Csyntaxdefs BeePL_notations.
Require Import BeePL_aux BeePL BeeTypes Csyntax Errors SimplExpr BeePL_values DecimalString BeePL_Bytes_Struct BeePL_Check_Reserved_Struct BeePL_bpf.
Require Import BeePL_Wrapper_Pass.

Local Open Scope string_scope.
Local Open Scope gensym_monad_scope.

(**** BeePL Compiler *****)

Record bcompiler_ctx := { arg_ctx : list (ident * type);
                          benv : bcomposite_env; }.

Section transBeePL_exprs.

Variables transBeePL_expr_expr : BeePL.expr -> list (ident * BeeTypes.type * string) -> bcompiler_ctx -> 
mon (Csyntax.expr * list (ident * BeeTypes.type * string) * bcompiler_ctx).

Definition max_fresh : nat := 1000%nat.

(* Translates list of BeePL expressions to list of C expressions *)
Fixpoint transBeePL_expr_exprs (es : list BeePL.expr) (fn_ctx : list (ident * BeeTypes.type * string)) (bctx : bcompiler_ctx) : 
mon (Csyntax.exprlist * list (ident * BeeTypes.type * string) * bcompiler_ctx) :=
match es with 
| nil => ret (Enil, fn_ctx, bctx) 
| e :: es => do (ce, fn_ctx') <- transBeePL_expr_expr e fn_ctx bctx;
             do (ces, fn_ctx'') <- transBeePL_expr_exprs es (snd ce) fn_ctx';
             ret ((Econs (fst ce) (fst ces)), snd ces, fn_ctx'')
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

Definition default_expr := (Eval (Values.Vint (Int.repr 0)) Tvoid).

(* This function exists to handle creating fresh variables for converting Ref to
   CompCert C. 

   Ex) ref(4) => int __fresh; __fresh = 4; &__fresh; 
   
   FIXME: There really shouldn't be a limited number of fresh identifiers *)

Fixpoint fresh_ident (used : list ident) (n : nat) : mon (ident * string) :=
  let candidate_str := "__fresh__" ++ NilZero.string_of_uint (Nat.to_uint n) in
  let candidate := ident_of_string candidate_str in
  if existsb (fun id => Pos.eqb candidate id) used then
    match n with
    | O => error (msg "Ran out of fresh identifiers: all __fresh__n from 1000 to 0 are taken.")
    | S n' => fresh_ident used n'
    end
  else ret (candidate, candidate_str).

(* These are helpers to deal with fn_ctx in transBeePL_expr_expr and transBeePL_expr_st *)
Definition unzip_ident {A B C} (p : A * B * C) : A :=
  match p with
  | (x, _, _) => x
  end.

Definition unzip_str {A B C} (p : A * B * C) : B :=
match p with
| (_, y, _) => y
end.


Fixpoint lookup_string (id : ident) (is : list (ident * string)) : option string :=
  match is with
  | nil              => None                       (* should never happen by assumption *)
  | (id', s) :: rest =>
      if ident_eq id id' then Some s else lookup_string id rest
  end.

(* Go through each arg in args and find string in ident to string mapping *)
Fixpoint create_fn_ctx (args : list (ident * BeeTypes.type)) (is : list (ident * string)) : mon (list (ident * BeeTypes.type * string)) :=
  match args with
  | nil => ret nil
  | (id, ty) :: rest =>
      do triples <- create_fn_ctx rest is;
      match lookup_string id is with
      | Some str => ret ((id, ty, str) :: triples)
      | _        => let id_str := NilZero.string_of_uint (Nat.to_uint (Pos.to_nat id)) in
                    let full_msg := "COMPILER ERROR: ident " ++ id_str ++ " is missing from ident to string mapping" in
                    error (msg full_msg)
      end
  end.

Fixpoint merge_ident_string (fn_ctx : list (ident * BeeTypes.type * string)) (is : list (ident * string)) : list (ident * string) :=
  match fn_ctx with
  | nil => is
  | (id, _, s) :: rest =>
      match lookup_string id is with
      | Some _ => merge_ident_string rest is               (* already present, skip *)
      | None   => merge_ident_string rest ((id, s) :: is)  (* add new binding *)
      end
  end.

(* It will never be used, but we need for None case *)
Definition get_default_option_val (t : Ctypes.type) : mon Values.val :=
match t with  
| Tvoid =>  ret Values.Vundef
| Ctypes.Tint sz s a => ret (Values.Vint (Int.repr 0)) 
| Ctypes.Tlong s a => ret (Values.Vlong (Int64.repr 0))
| Tfloat sz a => error (msg "No default value for float")
| Tpointer t a => ret (Values.Vlong (Int64.repr 0)) 
| Tarray _ _ _ => error (msg "No default value for array")
| Tfunction _ _ _ => error (msg "No default value for function")
| Tstruct x a => ret (Values.Vlong (Int64.repr 0)) 
| Tunion _ _ => error (msg "No default value for function")
end.

Definition check_div (ces : exprlist) (v : Values.val) (t : Ctypes.type) : mon Csyntax.expr :=
match t with 
| Ctypes.Tint I32 Signed _ => ret (Econdition (Ebinop Cop.Oor (Ebinop Cop.Oeq (hd default_expr (tl (exprlist_list_expr ces)))
                                                                     (Eval (Values.Vint Int.zero) t) t)
                                                      (Ebinop Cop.Oand (Ebinop Cop.Oeq (hd default_expr (exprlist_list_expr ces))
                                                                                        (Eval (Values.Vint (Int.repr Int.min_signed)) t) t)
                                                                       (Ebinop Cop.Oeq (hd default_expr (tl (exprlist_list_expr ces)))
                                                                                        (Eval (Values.Vint Int.mone) t) t) t) t)
                                     (Eval v t)
                                     (Ebinop (Cop.Odiv) (hd default_expr (exprlist_list_expr ces)) 
                                                        (hd default_expr (tl (exprlist_list_expr ces))) t) t)
| Ctypes.Tint I32 Unsigned _ => ret (Econdition (Ebinop Cop.Oeq (hd default_expr (tl (exprlist_list_expr ces)))
                                                                     (Eval (Values.Vint Int.zero) t) t)
                                            (Eval v t)
                                            (Ebinop (Cop.Odiv) (hd default_expr (exprlist_list_expr ces)) 
                                                        (hd default_expr (tl (exprlist_list_expr ces))) t) t)
| Ctypes.Tlong Signed _ => ret (Econdition (Ebinop Cop.Oor (Ebinop Cop.Oeq (hd default_expr (tl (exprlist_list_expr ces)))
                                                                     (Eval (Values.Vlong Int64.zero) t) t)
                                                      (Ebinop Cop.Oand (Ebinop Cop.Oeq (hd default_expr (exprlist_list_expr ces))
                                                                                        (Eval (Values.Vlong (Int64.repr Int64.min_signed)) t) t)
                                                                       (Ebinop Cop.Oeq (hd default_expr (tl (exprlist_list_expr ces)))
                                                                                        (Eval (Values.Vlong Int64.mone) t) t) t) t)
                                     (Eval v t)
                                     (Ebinop (Cop.Odiv) (hd default_expr (exprlist_list_expr ces)) 
                                                        (hd default_expr (tl (exprlist_list_expr ces))) t) t)
| Ctypes.Tlong Unsigned _ => ret (Econdition (Ebinop Cop.Oeq (hd default_expr (tl (exprlist_list_expr ces)))
                                                                     (Eval (Values.Vlong Int64.zero) t) t)
                                            (Eval v t)
                                            (Ebinop (Cop.Odiv) (hd default_expr (exprlist_list_expr ces)) 
                                                        (hd default_expr (tl (exprlist_list_expr ces))) t) t)
| _ => error (msg "The type of argument of div should be int or long")
end.

Definition check_mod (ces : exprlist) (v : Values.val) (t : Ctypes.type) : mon Csyntax.expr :=
match t with 
| Ctypes.Tint I32 Signed _ => ret (Econdition (Ebinop Cop.Oor (Ebinop Cop.Oeq (hd default_expr (tl (exprlist_list_expr ces)))
                                                                     (Eval (Values.Vint Int.zero) t) t)
                                                      (Ebinop Cop.Oand (Ebinop Cop.Oeq (hd default_expr (exprlist_list_expr ces))
                                                                                        (Eval (Values.Vint (Int.repr Int.min_signed)) t) t)
                                                                       (Ebinop Cop.Oeq (hd default_expr (tl (exprlist_list_expr ces)))
                                                                                        (Eval (Values.Vint Int.mone) t) t) t) t)
                                     (Eval v t)
                                     (Ebinop (Cop.Omod) (hd default_expr (exprlist_list_expr ces)) 
                                                        (hd default_expr (tl (exprlist_list_expr ces))) t) t)
| Ctypes.Tint I32 Unsigned _ => ret (Econdition (Ebinop Cop.Oeq (hd default_expr (tl (exprlist_list_expr ces)))
                                                                     (Eval (Values.Vint Int.zero) t) t)
                                            (Eval v t)
                                            (Ebinop (Cop.Omod) (hd default_expr (exprlist_list_expr ces)) 
                                                        (hd default_expr (tl (exprlist_list_expr ces))) t) t)
| Ctypes.Tlong Signed _ => ret (Econdition (Ebinop Cop.Oor (Ebinop Cop.Oeq (hd default_expr (tl (exprlist_list_expr ces)))
                                                                     (Eval (Values.Vlong Int64.zero) t) t)
                                                      (Ebinop Cop.Oand (Ebinop Cop.Oeq (hd default_expr (exprlist_list_expr ces))
                                                                                        (Eval (Values.Vlong (Int64.repr Int64.min_signed)) t) t)
                                                                       (Ebinop Cop.Oeq (hd default_expr (tl (exprlist_list_expr ces)))
                                                                                        (Eval (Values.Vlong Int64.mone) t) t) t) t)
                                     (Eval v t)
                                     (Ebinop (Cop.Omod) (hd default_expr (exprlist_list_expr ces)) 
                                                        (hd default_expr (tl (exprlist_list_expr ces))) t) t)
| Ctypes.Tlong Unsigned _ => ret (Econdition (Ebinop Cop.Oeq (hd default_expr (tl (exprlist_list_expr ces)))
                                                                     (Eval (Values.Vlong Int64.zero) t) t)
                                            (Eval v t)
                                            (Ebinop (Cop.Omod) (hd default_expr (exprlist_list_expr ces)) 
                                                        (hd default_expr (tl (exprlist_list_expr ces))) t) t)
| _ => error (msg "The type of argument of div should be int or long")
end.

Definition check_shl (ces : exprlist) (v : Values.val) (t : Ctypes.type) : mon Csyntax.expr :=
match t with 
| Ctypes.Tint _ s _ => ret (Econdition (Ebinop Cop.Olt (hd default_expr (tl (exprlist_list_expr ces)))
                                                               (Eval (Values.Vint Int.iwordsize) t) t)
                                                      (Eval v t) 
                                                      (Ebinop (Cop.Oshl) (hd default_expr (exprlist_list_expr ces)) 
                                                                         (hd default_expr (tl (exprlist_list_expr ces))) t) t)
| Ctypes.Tlong _ _ => ret (Econdition (Ebinop Cop.Olt (hd default_expr (tl (exprlist_list_expr ces)))
                                                               (Eval (Values.Vlong Int64.iwordsize) t) t)
                                                      (Eval v t) 
                                                      (Ebinop (Cop.Oshl) (hd default_expr (exprlist_list_expr ces)) 
                                                                         (hd default_expr (tl (exprlist_list_expr ces))) t) t)
| _ => error (msg "COMPILER ERROR: The type of argument of shl should be int or long")
end.

Definition check_shr (ces : exprlist) (v : Values.val) (t : Ctypes.type) : mon Csyntax.expr :=
match t with 
| Ctypes.Tint _ s _ => ret (Econdition (Ebinop Cop.Olt (hd default_expr (tl (exprlist_list_expr ces)))
                                                               (Eval (Values.Vint Int.iwordsize) t) t)
                                                      (Eval v t) 
                                                      (Ebinop (Cop.Oshr) (hd default_expr (exprlist_list_expr ces)) 
                                                                         (hd default_expr (tl (exprlist_list_expr ces))) t) t)
| Ctypes.Tlong _ _ => ret (Econdition (Ebinop Cop.Olt (hd default_expr (tl (exprlist_list_expr ces)))
                                                               (Eval (Values.Vlong Int64.iwordsize) t) t)
                                                      (Eval v t) 
                                                      (Ebinop (Cop.Oshr) (hd default_expr (exprlist_list_expr ces)) 
                                                                         (hd default_expr (tl (exprlist_list_expr ces))) t) t)
| _ => error (msg "COMPILER ERROR: The type of argument of shr should be int or long")
end.

Fixpoint init_struct_fields (sid : ident) (fields : list (ident * Csyntax.expr)) (t : Ctypes.type) 
(t' : Ctypes.type) {struct fields} : mon Csyntax.statement :=
match fields with
| nil => ret Sskip
| (f, e) :: rest => let lhs := (Efield (Evalof (Ederef (Evalof (Evar sid t) t) t') t') f (typeof e)) in
                    let ff := (Sdo (Eassign lhs e (typeof e))) in
                    do rs <- (init_struct_fields sid rest t t');
                    ret (Ssequence ff rs)
end.

Fixpoint use_comma_rec (ces : list Csyntax.expr) : expr :=
match ces with 
| nil => default_expr
| ce :: ces => let ces' := (use_comma_rec ces) in
               (Ecomma ce ces' (Ctypes.Tpointer (Ctypes.Tint I8 Unsigned noattr) noattr))
end.

Fixpoint transBeePL_expr_expr (e : BeePL.expr) (fn_ctx : list (ident * BeeTypes.type * string)) (bctx : bcompiler_ctx) : 
mon (Csyntax.expr * (list (ident * BeeTypes.type * string)) * bcompiler_ctx) := 
match e with 
| Val v t => ret (Eval (trans_bvalue_cvalue v) (transBeePL_type t), fn_ctx, bctx) 
| Var x t => ret (Evar x (transBeePL_type t), fn_ctx, bctx)
| Const c t => match c with 
               | ConsInt i => ret (Eval (Values.Vint i) (transBeePL_type t), fn_ctx, bctx)
               | ConsLong i => ret (Eval (Values.Vlong i) (transBeePL_type t), fn_ctx, bctx)
               | ConsUnit => ret (Eval (Values.Vint (Int.repr 0)) (transBeePL_type t), fn_ctx, bctx) 
               | ConsBool b => ret (if eqb b true 
                                    then (Eval (Values.Vint (Int.repr 1)) (transBeePL_type t), fn_ctx, bctx) 
                                    else (Eval (Values.Vint (Int.repr 0)) (transBeePL_type t), fn_ctx, bctx))
               end
| App e es t => do (ce, bctx') <- (transBeePL_expr_expr e fn_ctx bctx); 
                do (ces, bctx'') <- (transBeePL_expr_exprs transBeePL_expr_expr es (snd ce) bctx');
                ret (Ecall (fst ce) (fst ces) (transBeePL_type t), snd ces, bctx'')
| Prim b es t => match b with 
                 | Ref => (* es: function arguments. If a function argument is Ref a fresh variable needs to be inserted prior to bind 
                         
                             let x = 3 in
                             let y = add(x, ref(4))

                             should become

                             int x = 3;
                             int __fresh; <- can be acomplished by adding a fresh variable to fn_ctx
                             int y = add(x, (__fresh = 4, &_fresh));
                           *)
                          do (ces, bctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es fn_ctx bctx);
                          let ct := (transBeePL_type t) in
                          do (i, str) <- (fresh_ident (List.map unzip_ident (snd ces)) max_fresh);

                          match es with
                          | e :: nil => 
                                        do pty <- ref_to_prim t;
                                        let cpty := (transBeePL_type pty) in
                                        let fn_ctx'' := (i, pty, str) :: (snd ces) in
                                        ret ((Ecomma (Eassign (Evar i cpty) 
                                                              (hd default_expr (exprlist_list_expr (fst ces))) 
                                                              (cpty)) 
                                                     (Eaddrof (Evar i ct) 
                                                              (ct))
                                                     (ct)), fn_ctx'', bctx')
                          | _ => error (msg "COMPILER ERROR: Ref should only have one expr in its expr list.")
                          end
                 | Deref => do (ces, bctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es fn_ctx bctx);
                            let ct := (transBeePL_type t) in
                            ret ((Ederef (hd default_expr (exprlist_list_expr (fst ces))) 
                                ct), snd ces, bctx')   
                 | Massgn => do (ces, bctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es fn_ctx bctx);
                                        let ct := (transBeePL_type t) in
                                        ret ((Eassign (Ederef (hd default_expr (exprlist_list_expr (fst ces))) 
                                                         (typeof (hd default_expr (exprlist_list_expr (fst ces)))))
                                                (hd default_expr (tl (exprlist_list_expr (fst ces))))
                                                ct), snd ces, bctx')
                 | Run h => ret ((Eval (Values.Vundef) Tvoid), fn_ctx, bctx)
                 | Uop o => do (ces, bctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es fn_ctx bctx);
                            let ct := (transBeePL_type t) in
                            ret ((Eunop o
                                (hd default_expr (exprlist_list_expr (fst ces))) 
                                ct), snd ces, bctx')
                 | Bop o => do v <- return_czero (transBeePL_type t);
                            do (ces, bctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es fn_ctx bctx);
                            match o with 
                            | Cop.Odiv => do rs <- (check_div (fst ces) v (transBeePL_type t));
                                          ret (rs, snd ces, bctx')
                                                                      
                            | Cop.Omod => do rs <- (check_mod (fst ces) v (transBeePL_type t));
                                          ret (rs, snd ces, bctx')
                            | Cop.Oshl => do rs <- check_shl (fst ces) v (transBeePL_type t);
                                          ret (rs, snd ces, bctx')
                             | Cop.Oshr => do rs <- check_shr (fst ces) v (transBeePL_type t);
                                           ret (rs, snd ces, bctx')
                            | _ => ret (Ebinop o
                                        (hd default_expr (exprlist_list_expr (fst ces))) 
                                        (hd default_expr (tl (exprlist_list_expr (fst ces))))
                                        (transBeePL_type t), snd ces, bctx')

                           end
end
| Bind x t e e' t' => let ct := (transBeePL_type t) in
                      do (ce, bctx') <- (transBeePL_expr_expr e fn_ctx bctx);
                      do (ce', bctx'') <- (transBeePL_expr_expr e' (snd ce) bctx');
                      let ct' := (transBeePL_type t') in
                      ret (Ecomma (Eassign (Evar x ct) (fst ce) ct) (fst ce') ct', snd ce', bctx'') 
| Cond e e' e'' t => do (ce, bctx') <- (transBeePL_expr_expr e fn_ctx bctx);
                     do (ce', bctx'') <- (transBeePL_expr_expr e' (snd ce) bctx');
                     do (ce'', bctx''') <- (transBeePL_expr_expr e'' (snd ce') bctx'');
                     let ct := (transBeePL_type t) in
                     ret (Econdition (fst ce) (fst ce') (fst ce'') ct, snd ce'', bctx''')  
| Unit t=> let ct := (transBeePL_type t) in
           ret (Eval (trans_bvalue_cvalue Vunit) ct, fn_ctx, bctx) (* Fix me *)
| Addr l ofs t => let ct := transBeePL_type t in
                  ret (Eloc l.(lname) ofs l.(lbitfield) ct, fn_ctx, bctx)
| Hexpr h e t => ret (Eval (Values.Vundef) Tvoid, fn_ctx, bctx) (* FIX ME *)
| Eapp ef ts es t => let cef := befunction_to_cefunction ef in
                     let cts := (transBeePL_types transBeePL_type ts) in
                     let ct := (transBeePL_type t) in
                     do (ces, bctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es fn_ctx bctx);
                     ret (Ebuiltin cef cts (fst ces) ct, snd ces, bctx')
| Sinit x ids es t => error (msg "COMPILER ERROR: Struct creation cannot be translated to another C epxr")
| Sfield e x t => do (ce, bctx') <- transBeePL_expr_expr e fn_ctx bctx;
                  let ct := transBeePL_type t in
                  ret (Efield (Evalof (fst ce) (transBeePL_type (typeof_expr e))) x ct, snd ce, bctx')
| For e1 e2 d e t => error (msg "COMPILER ERROR: For loop cannot be translated to another C expr")
| Enone t => match t with 
             | Ptrtype t' => if is_option_ptr_type t' 
                             then ret ((Ecast (Eval (Values.Vint (Int.repr 0)) tint) (tptr (transBeePL_type t))), fn_ctx, bctx)
                             else error (msg "COMPILER ERROR: Expression none should be a pointer option type")
             | _ => error (msg "COMPILER ERROR: Expression none should be a pointer type")
             end
| Esome e t => match t with 
             | Ptrtype t' => if is_option_ptr_type t' 
                             then transBeePL_expr_expr e fn_ctx bctx
                             else error (msg "COMPILER ERROR: Expression some should be a pointer option type")
             | _ => error (msg "COMPILER ERROR: Expression some should be a pointer type")
             end
| Match e ps es t => do (ce, bctx') <- transBeePL_expr_expr e fn_ctx bctx;
                     let te := typeof_expr e in
                     match te with 
                     | Ptrtype t' => 
                         if is_option_ptr_type t'  
                         then match ps, es with 
                              | nil, nil => error (msg "COMPILER ERROR: No pattern matching cases found")
                              | (Pnone :: Psome x :: nil), (e1 :: e2 :: nil) => 
                                  do (ce1, bctx1) <- transBeePL_expr_expr e1 fn_ctx bctx';
                                  do (ce2, bctx2) <- transBeePL_expr_expr e2 (snd ce1) bctx1;
                                  ret ((Econdition (Ebinop Cop.Oeq (fst ce) 
                                                       (Ecast (Eval (Values.Vint (Int.repr 0)) tint) (tptr (transBeePL_type t)))
                                                       (Ctypes.Tint Ctypes.I8 Ctypes.Unsigned noattr))
                                          (fst ce1)
                                          (fst ce2) (transBeePL_type t)), snd (ce2), bctx2)
                              | (Psome x :: Pnone :: nil), (e1 :: e2 :: nil) => 
                                  do (ce1, bctx1) <- transBeePL_expr_expr e1 fn_ctx bctx';
                                  do (ce2, bctx2) <- transBeePL_expr_expr e2 (snd ce1) bctx1;
                                  ret ((Econdition (Ebinop Cop.Oeq (fst ce) 
                                                       (Ecast (Eval (Values.Vint (Int.repr 0)) tint) (tptr (transBeePL_type t)))
                                                       (Ctypes.Tint Ctypes.I8 Ctypes.Unsigned noattr))
                                          (fst ce2)
                                          (fst ce1) (transBeePL_type t)), snd (ce2), bctx2)
                              | _, _ => error (msg "COMPILER ERROR: We support only two patterns as of now")
                              end
                          else error (msg "COMPILER ERROR: Match can be only performed on option type")
                     | Bytes => ret (fst ce, snd ce, bctx')
                     | _ => error (msg "COMPILER ERROR: Match can be only performed on ptr type or bytes type")
                     end
| Ebytes es t => do (ces, bctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es fn_ctx bctx); 
                 error (msg "COMPILER ERROR: Bitstring translation is not supported yet")
end.

Definition check_var_const (e : BeePL.expr) : bool :=
match e with 
| Var x t => true 
| Const c t => true 
| _ => false
end.

Fixpoint assign_array_cast (a : ident) (sz : Z) (ts : list Ctypes.type) (ces : list Csyntax.expr) : mon Csyntax.statement :=
match ces, ts with 
| nil, nil => ret Sskip
| ce1 :: ce2 :: ces1, t1 :: t2 :: ts1 => 
  do rs <- assign_array_cast a sz ts1 ces1;
  ret (Ssequence (Sdo (Eassign (Ederef (Ecast (Evalof (Evar a (tarray tschar sz)) (tarray tschar sz)) (tptr t1)) t1)
                                                        ce1 t1))
                 (Ssequence (Sdo (Eassign (Ederef (Ecast (Ebinop Cop.Oadd (Evalof (Evar a (tarray tschar sz)) (tarray tschar sz))
                                                                          (Esizeof t1 t2) t2) (tptr t2)) t2)
                                     ce2 t2)) rs))
| _, _ => error (msg "COMPILER ERROR: The length of type list and expression list should be same in bitstring")
end.  

(* struct xdp_md_wrapper xdp_md_wrapper;
    xdp_md_wrapper.data.start = (\* char)ctx->data;
    xdp_md_wrapper.data.end = (\* char)ctx->data_end; *)
Definition set_ebpf_struct_bee_struct (beei : ident) (t : Ctypes.type) (fdata : ident) (t' : Ctypes.type) :=
           (Ssequence (Sdo (Eassign (Efield (Evalof (Efield (Evalof (Evar beei t) t)
                                                            _data_bee (Tstruct bytes_t noattr)) (Tstruct bytes_t noattr)) (* bees.data *)
                                             bytes_start (tptr tuchar)) (* bees.data.start *)
                                    (Ecast (Evalof (Efield (Evalof (Ederef (Evalof (Evar fdata t') t') t') t') _data tulong) tulong) (tptr tuchar)) (tptr tuchar))) (* (star char)ctx->data *) 
                      (Sdo (Eassign (Efield (Evalof (Efield (Evalof (Evar beei t) t)
                                                            _data_bee (Tstruct bytes_t noattr)) (Tstruct bytes_t noattr)) (* bees.data *)
                                             bytes_end (tptr tuchar)) (* bees.data.end *)
                                    (Ecast (Evalof (Efield (Evalof (Ederef (Evalof (Evar fdata t') t') t') t') _data_end tulong) tulong) (tptr tuchar)) (tptr tuchar)))). (* (star char)ctx->data_end *)

(* if (xdp_md_wrapper.data.start + sizeof(struct ethhdr) > xdp_md_wrapper.data.end) then ee else se *)
Definition bound_check (input : ident) (t : Ctypes.type) (t' : Ctypes.type) (ee se : Csyntax.statement) := 
(Sifthenelse (Ebinop Cop.Ogt
                     (Ebinop Cop.Oadd
                       (Efield (Evalof (Efield (Evalof (Evar input t) t)
                                               _data_bee (Tstruct bytes_t noattr)) (Tstruct bytes_t noattr))
                               bytes_start (tptr tuchar)) 
                       (Esizeof t' tulong) (tptr tuchar)) (* xdp_md_bee.data.start + sizeof(struct ethhdr) *)
                     (Efield (Evalof (Efield (Evalof (Evar input t) t) 
                                             _data_bee (Tstruct bytes_t noattr)) (Tstruct bytes_t noattr)) 
                               bytes_end (tptr tuchar)) tint) (* xdp_md_bee.data.end *)
             ee 
             se).

Definition set_temp_for_copy (temp : ident) (t : Ctypes.type) (from: ident) (t' : Ctypes.type) : Csyntax.statement :=
(Sdo (Eassign (Evar temp t) (Ecast (Evalof (Efield (Evalof (Efield (Evalof (Evar from t') t') _data_bee
                                           (Tstruct bytes_t noattr)) 
                                            (Tstruct bytes_t noattr)) bytes_start
                                                      (tptr tuchar)) (tptr tuchar)) t) t)).

Fixpoint copy_buffer (to : ident) (sto : ident) (t : Ctypes.type) (xts : list (ident * Ctypes.type)) (from : ident) : Csyntax.statement :=
match xts with 
| nil => Sskip
| x :: xs => let bs :=  copy_buffer to sto t xs from in
             (Ssequence (Sdo (Eassign (Efield (Evalof (Evar to (Tstruct sto noattr))
                                       (Tstruct sto noattr)) (fst x) (snd x))
                 (Evalof (Efield (Evalof (Ederef (Evalof (Evar from (tptr (Tstruct sto noattr)))
                                                  (tptr (Tstruct sto noattr)))
                         (Tstruct sto noattr)) (Tstruct sto noattr))
                     (fst x) (snd x)) (snd x)) (snd x))) bs)
end.

Definition incr_data_ptr (wv : ident) (s : ident) (bv : ident) : Csyntax.statement :=
(Sdo (Eassign (Efield (Evalof (Efield (Evalof
                             (Evar wv (Tstruct s noattr))
                             (Tstruct s noattr)) _data_bee
                           (Tstruct bytes_t noattr))
                         (Tstruct bytes_t noattr)) bytes_start (tptr tuchar))
                     (Ebinop Cop.Oadd (Evalof (Efield (Evalof (Efield (Evalof
                                 (Evar wv (Tstruct s noattr))
                                 (Tstruct s noattr)) _data_bee
                               (Tstruct bytes_t noattr))
                             (Tstruct bytes_t noattr)) bytes_start (tptr tuchar))
                         (tptr tuchar))
                       (Esizeof (Tstruct bv noattr) tulong)
                       (tptr tuchar)) (tptr tuchar))).


Fixpoint transBeePL_expr_st (cenv : bcomposite_env) (e : BeePL.expr ) (ctx : list (ident * BeeTypes.type * string)) (bctx : bcompiler_ctx) : 
mon (Csyntax.statement * list (ident * BeeTypes.type * string) * bcompiler_ctx) :=
match e with 
| Val v t => let vt := (transBeePL_type t) in
             ret (Sreturn (Some (Eval (trans_bvalue_cvalue v) vt)), ctx, bctx) 
| Var x t => let ct := (transBeePL_type t) in
             ret (Sreturn (Some (Evalof (Evar x ct) ct)), ctx, bctx)
| Const c t => let ct := (transBeePL_type t) in
               ret (Sreturn (Some (Evalof (match c with 
                                      | ConsInt i => Eval (Values.Vint i) ct
                                      | ConsLong i => Eval (Values.Vlong i) ct
                                      | ConsUnit => Eval (Values.Vint (Int.repr 0)) ct
                                      | ConsBool b => if eqb b true 
                                                      then Eval (Values.Vint (Int.repr 1)) ct
                                                      else Eval (Values.Vint (Int.repr 0)) ct
                                      end) ct)), ctx, bctx)
| App e es t => do (ce, ctx') <- (transBeePL_expr_expr e ctx bctx);
                do (ces, ctx'') <- (transBeePL_expr_exprs transBeePL_expr_expr es (snd ce) ctx');
                let ct := (transBeePL_type t) in
                ret (Sdo (Ecall (fst ce) (fst ces) ct), snd ces, ctx'')  
| Prim b es t => match b with 
                 | Ref => (* TODO: figure out how to recude duplicate code between here and transBeePL_expr_st *)
                          do (ces, ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es ctx bctx);
                          let ct := (transBeePL_type t) in
                          do (i, str) <- (fresh_ident (List.map unzip_ident (snd ces)) max_fresh);
                          match es with
                          | e :: nil => do pty <- ref_to_prim t;
                                        let cpty := (transBeePL_type pty) in        
                                        let ctx'' := (i, pty, str) :: (snd ces) in
                                        ret (Ssequence (Sdo (Eassign (Evar i cpty)
                                                                     (hd default_expr (exprlist_list_expr (fst ces)))
                                                                     (cpty)))
                                                       (Sdo (Eaddrof (Evar i ct) 
                                                                     (ct))), ctx'', ctx')
                          | _ => error (msg "COMPILER ERROR: Ref should only have one expr in its expr list.")
                          end
                 | Deref => do (ces, ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es ctx bctx);
                            let ct := (transBeePL_type t) in
                            ret (Sreturn (Some (Ederef (hd default_expr (exprlist_list_expr (fst ces))) 
                                     ct)), snd ces, ctx')   
                 | Massgn => do (ces, fn_ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es ctx bctx);
                                        let ct := (transBeePL_type t) in
                                        ret (Sdo (Eassign (Ederef (hd default_expr (exprlist_list_expr (fst ces))) 
                                                             (typeof (hd default_expr (exprlist_list_expr (fst ces))))) 
                                                (hd default_expr (tl (exprlist_list_expr (fst ces))))
                                                ct), snd ces, fn_ctx')
                 | Run h => ret (Sdo (Eval (Values.Vundef) Tvoid), ctx, bctx)
                 | Uop o => do (ces, ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es ctx bctx);
                            let ct := (transBeePL_type t) in 
                            ret (Sreturn (Some (Eunop o 
                                     (hd default_expr (exprlist_list_expr (fst ces))) 
                                     ct)), snd ces, ctx') 
                 | Bop o => do v <- return_czero (transBeePL_type t);
                            do (ces, fn_ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es ctx bctx);
                            match o with 
                            | Cop.Odiv => do rs <- (check_div (fst ces) v (transBeePL_type t));
                                          ret (Sreturn (Some rs), snd ces, fn_ctx')
                                                                      
                            | Cop.Omod => do rs <- (check_div (fst ces) v (transBeePL_type t));
                                          ret (Sreturn (Some rs), snd ces, fn_ctx')
                            | Cop.Oshl => do rs <- check_shl (fst ces) v (transBeePL_type t);
                                          ret (Sreturn (Some rs), snd ces, fn_ctx')
                             | Cop.Oshr => do rs <- check_shr (fst ces) v (transBeePL_type t);
                                           ret (Sreturn (Some rs), snd ces, fn_ctx')
                            | _ => ret (Sreturn (Some (Ebinop o
                                        (hd default_expr (exprlist_list_expr (fst ces))) 
                                        (hd default_expr (tl (exprlist_list_expr (fst ces))))
                                        (transBeePL_type t))), snd ces, fn_ctx')

                           end
                 end 
| Bind x t e e' t' => let ct := (transBeePL_type t) in
                      do (ce', ctx') <- (transBeePL_expr_st cenv e' ctx bctx);
                      match e with 
                      | Prim Massgn es t => do (ce, ctx'') <- (transBeePL_expr_st cenv e (snd ce') ctx'); ret (Ssequence (fst ce) (fst ce'), snd ce, ctx'') 
                      | For e1 e2 d e3 t => do (cs, ctx'') <- (transBeePL_expr_st cenv e (snd ce') ctx'); ret (Ssequence (fst cs) (fst ce'), snd cs, ctx'')  
                      | Sinit sx ids es t =>  do (cs, ctx'') <- (transBeePL_expr_st cenv e (snd ce') ctx'); ret (Ssequence (fst cs) (fst ce'), snd cs, ctx'') 
                      | Bind x1 t1 e1 e1' t1' =>  do (cs, ctx'') <- (transBeePL_expr_st cenv e (snd ce') ctx'); ret (Ssequence (fst cs) (fst ce'), snd cs, ctx'') 
                      | _ => do (ce, ctx'') <- (transBeePL_expr_expr e (snd ce') ctx');
                                    ret (Ssequence (Sdo (Eassign (Evar x ct) (fst ce) Tvoid)) 
                                           (fst ce'), snd ce, ctx'')

                      end
| Cond e e' e'' t' => do (ce, ctx') <- (transBeePL_expr_expr e ctx bctx);
                      do (ce', ctx'') <- (transBeePL_expr_st cenv e' (snd ce) ctx');
                      do (ce'', ctx''') <- (transBeePL_expr_st cenv e'' (snd ce') ctx'');
                      let ct' := (transBeePL_type t') in
                      ret (Sifthenelse (fst ce) (fst ce') (fst ce''), snd ce'', ctx''')
                      (*if (check_var_const e' && check_var_const e'') (* check for expressions with side-effects *)
                      then ret (Sifthenelse ce ce' ce'')
                      else if (check_var_const e') then ret (Sifthenelse ce ce' ce'')
                                                   else if (check_var_const e'') 
                                                        then ret (Sifthenelse ce ce' (Sreturn (Some (Evalof ce'' ct'))))
                                                        else ret (Sifthenelse ce ce' (Sdo ce''))*)
| Unit t=> ret (Sskip, ctx, bctx) (*Sreturn (Some (Eval (Values.Vint (Int.repr 0)) (Ctypes.Tint I32 Unsigned noattr)))*) (* In case of unit, we return 0 *)
| Addr l ofs t => let ct := (transBeePL_type t) in
                  ret (Sdo (Eloc l.(lname) ofs l.(lbitfield) ct), ctx, bctx)                    
| Hexpr h e t => ret (Sdo (Eval (Values.Vundef) Tvoid), ctx, bctx) (* FIX ME *)
| Eapp ef ts es t => let cef := befunction_to_cefunction ef in
                     let cts := (transBeePL_types transBeePL_type ts) in
                     let ct := (transBeePL_type t) in
                     do (ces, ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es ctx bctx);
                     ret (Sdo (Ebuiltin cef cts (fst ces) ct), snd ces, ctx')
| Sinit sx ids es t => do (ces, ctx') <- transBeePL_expr_exprs transBeePL_expr_expr es ctx bctx;
                         do (temp, strl) <- (fresh_ident (List.map unzip_ident (snd ces)) max_fresh);
                         do pty <- ref_to_prim t;
                         let ctx'' := (temp, pty, strl) :: snd ces in
                         do rs <- init_struct_fields sx (zip ids (exprlist_list_expr (fst ces))) (transBeePL_type t) (transBeePL_type pty);
                         ret (Ssequence (Sdo (Eassign (Evar sx (transBeePL_type t)) 
                                                                         (Eaddrof (Evar temp (transBeePL_type pty)) (transBeePL_type t)) (transBeePL_type t)))
                                                            rs, ctx'', ctx')
| Sfield e x t => do (ce, ctx') <- transBeePL_expr_expr e ctx bctx;
                  let ct := transBeePL_type t in
                  ret (Sdo (Evalof (Efield (Evalof (fst ce) (transBeePL_type (typeof_expr e))) x ct) ct), snd ce, ctx')
| For e1 e2 d e t => do (ce1, bctx1) <- transBeePL_expr_expr e1 ctx bctx;
                     do (low, strl) <- (fresh_ident (List.map unzip_ident (snd ce1)) max_fresh);
                     let ctx2 := (low, typeof_expr e1, strl) :: snd ce1 in
                     do (ce2, bctx2) <- transBeePL_expr_expr e2 ctx2 bctx1;
                     do (high, strh) <- (fresh_ident (List.map unzip_ident (snd ce2)) max_fresh);
                     let ctx4 := (high, typeof_expr e2, strh) :: snd ce2 in
                     do (ce3, bctx3) <- transBeePL_expr_st cenv e ctx4 bctx2;
                     do (i, stri) <- (fresh_ident (List.map unzip_ident ctx4) max_fresh);
                     let ctx6 := (i, typeof_expr e1, stri) :: snd ce3 in
                     match d with 
                     | Up => ret (Ssequence (Ssequence (Sdo (Eassign (Evar low (typeof (fst ce1))) (fst ce1) (typeof (fst ce1))))
                                                       (Sdo (Eassign (Evar high (typeof (fst ce2))) (fst ce2) (typeof (fst ce2)))))
                                            (Sifthenelse (Ebinop Cop.Ole (Evar low (typeof (fst ce1))) (Evar high (typeof (fst ce2))) (typeof (fst ce1)))
                                                         (Sfor (Sdo (Eassign (Evar i (typeof (fst ce1))) (Evar low (typeof (fst ce1))) (typeof (fst ce1))))
                                                               (Ebinop Cop.Ole (Evalof (Evar i (typeof (fst ce2))) (typeof (fst ce2))) 
                                                                                       (Evar high (typeof (fst ce2))) (typeof (fst ce2)))
                                                               (Sdo (Epostincr Cop.Incr (Evar i (typeof (fst ce2))) (typeof (fst ce2))))
                                                          (fst ce3))
                                                         Sskip), ctx6, bctx3)
                     | Down => ret (Ssequence (Ssequence (Sdo (Eassign (Evar low (typeof (fst ce1))) (fst ce1) (typeof (fst ce1))))
                                                         (Sdo (Eassign (Evar high (typeof (fst ce2))) (fst ce2) (typeof (fst ce2)))))
                                              (Sifthenelse (Ebinop Cop.Oge (Evar low (typeof (fst ce1))) (Evar high (typeof (fst ce2))) (typeof (fst ce1)))
                                                           (Sfor (Sdo (Eassign (Evar i (typeof (fst ce1))) (Evar low (typeof (fst ce1))) (typeof (fst ce1))))
                                                                 (Ebinop Cop.Oge (Evalof (Evar i (typeof (fst ce2))) (typeof (fst ce2))) 
                                                                                          (Evar high (typeof (fst ce2))) (typeof (fst ce2)))
                                                                 (Sdo (Epostincr Cop.Decr (Evar i (typeof (fst ce2))) (typeof (fst ce2))))
                                                            (fst ce3))
                                                            Sskip), ctx6, bctx3)
                     end
| Enone t => match t with 
             | Ptrtype t' => if is_option_ptr_type t' 
                           then ret (Sdo ((Ecast (Eval (Values.Vint (Int.repr 0)) tint) (tptr (transBeePL_type t)))), ctx, bctx)
                           else error (msg "COMPILER ERROR: Option type of None should contain a pointer in BeePL")
             | _ => error (msg "COMPILER ERROR: None should be of Option type")
             end
| Esome e t => match t with 
               | Ptrtype t' => if is_option_ptr_type t' 
                               then transBeePL_expr_st cenv e ctx bctx
                               else error (msg "COMPILER ERROR: Option type of Some should contain a pointer in BeePL")
               | _ => error (msg "COMPILER ERROR: Some should be of Option type")
              end
| Match e ps es t => do (ce, bctx') <- transBeePL_expr_expr e ctx bctx;
                     let te := typeof_expr e in
                     match te with 
                     | Ptrtype t' => 
                         if is_option_ptr_type t' 
                         then match ps, es with 
                              | nil, nil => error (msg "COMPILER ERROR: No pattern matching cases found")
                              | (Pnone :: Psome x :: nil), (e1 :: e2 :: nil) => 
                                  do (ce1, bctx1) <- transBeePL_expr_st cenv e1 ctx bctx';
                                  do (ce2, bctx2) <- transBeePL_expr_st cenv e2 (snd ce1) bctx1;
                                  ret ((Sifthenelse (Ebinop Cop.Oeq (fst ce) 
                                                       (Ecast (Eval (Values.Vint (Int.repr 0)) tint) (tptr (transBeePL_type t)))
                                                       (Ctypes.Tint Ctypes.I8 Ctypes.Unsigned noattr))
                                          (fst ce1)
                                          (fst ce2)), snd (ce2), bctx2)
                              | (Psome x :: Pnone :: nil), (e1 :: e2 :: nil) => 
                                  do (ce1, bctx1) <- transBeePL_expr_st cenv e1 ctx bctx';
                                  do (ce2, bctx2) <- transBeePL_expr_st cenv e2 (snd ce1) bctx1;
                                  ret ((Sifthenelse (Ebinop Cop.Oeq (fst ce) 
                                                       (Ecast (Eval (Values.Vint (Int.repr 0)) tint) (tptr (transBeePL_type t)))
                                                       (Ctypes.Tint Ctypes.I8 Ctypes.Unsigned noattr))
                                          (fst ce2)
                                          (fst ce1)), snd (ce1), bctx2)
                              | _, _ => error (msg "COMPILER ERROR: We support only two patterns as of now")
                              end
                          else error (msg "COMPILER ERROR: Match can be only performed on option type containing types other than ref")
                     | Bytes => match ps, es with 
                                | (Pbytes x (Stype s noattr) xts :: p2), (e1 :: e2 :: nil) => 
                                    let cxts := zip (unzip1 xts) (from_typelist (transBeePL_types transBeePL_type (unzip2 xts))) in 
                                    do (ce1, bctx1) <- transBeePL_expr_st cenv e1 (snd ce) bctx';
                                    do (ce2, bctx2) <- transBeePL_expr_st cenv e2 (snd ce1) bctx1;
                                    match bctx.(arg_ctx) with 
                                    | (argi, (Ptrtype (Sptype istruct noattr))) :: nil =>
                                        do (i, str) <- (fresh_ident (List.map unzip_ident (snd ce)) max_fresh);
                                        let ctx'' := (i, Stype istruct noattr, str) :: snd ce in
                                        do (i', str') <- (fresh_ident (List.map unzip_ident ctx'') max_fresh);
                                        let ctx''' := (i', Ptrtype (Sptype s noattr), str') :: ctx'' in
                                        match transform_ctx_ebpf_ctx bctx.(arg_ctx) with 
                                        | OK narg =>
                                        match narg with 
                                        | (argi', (Tpointer (Tstruct istruct' noattr) {|attr_volatile := false;attr_alignas := None|})) :: nil =>
                                          ret (Ssequence (set_ebpf_struct_bee_struct i (transBeePL_type (Stype istruct noattr)) argi' (tptr (Tstruct istruct' noattr)))
                                                            (bound_check i (transBeePL_type (Stype istruct noattr)) (Tstruct s noattr) (fst ce2)
                                                              (Ssequence (set_temp_for_copy i' (tptr (Tstruct s noattr)) i (transBeePL_type (Stype istruct noattr)))
                                                                (Ssequence (copy_buffer x s (tptr (Tstruct s noattr)) cxts i')
                                                                   (Ssequence (incr_data_ptr i istruct s) (fst ce1))))),  
                                              ctx''', bctx2) 
                                        | _ => error (msg "COMPILER ERROR: eBPF program supports only one argument")
                                        end
                                       | Error msg => error (msg)
                                       end
                                    | _ => error (msg "COMPILER ERROR: For now we assume this match is used in only eBPF programs where first argument 
                                                       is some eBPF context ")
                                    end
                                | _, _ => error (msg "COMPILER ERROR: Match on bytes only pattern match on Pbytes pattern")
                                end
                     | _ =>  error (msg "COMPILER ERROR: Match can be only performed on option and bytes type")
                     end
| Ebytes es t => do (ces, ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es ctx bctx); 
                 error (msg "COMPILER ERROR: Bitstring translation is not supported yet")
                 (*do (i, str) <- (fresh_ident (List.map unzip_ident ctx') max_fresh);
                 let ctx'' := (i, trint8u, str) :: ctx' in
                 let sz := sizeof_types cenv (map typeof_expr es) in 
                 let tcs := map typeof (exprlist_list_expr ces) in 
                 do rs <- assign_array_cast i sz tcs (exprlist_list_expr ces);
                 ret (Ssequence (Sdo (Evar i (tarray tschar sz)))
                                 rs, ctx'')*)
                 (*ret (Sdo (Ecast (hd default_expr (exprlist_list_expr ces)) (Ctypes.Tpointer (Ctypes.Tint I8 Unsigned noattr) noattr)), ctx')*)
     
                                
end.

(* Translates the BeePL function declaration to C function *)  
Definition transBeePL_function_function (cenv : bcomposite_env) (fd : BeePL.function) (is : list (ident * string)) (bctx : bcompiler_ctx) : 
res (Csyntax.function * list (ident * string) * bcompiler_ctx) :=
if fd.(is_ebpf) then 
  (let crt := (transBeePL_type (fd.(BeePL.fn_return))) in
  (* When using Ref a fresh variable is created which must be added to BeePL.fn_vars and ident_to_string *)
  (* fn_ctx is fn_vars (ident * type) plus the corresponding string from is (ident * string) *)
  match (create_fn_ctx (BeePL.fn_vars fd) is (initial_generator tt)) with
  | Err msg => Error msg
  | Res fn_ctx g i =>
  
  match (transBeePL_expr_st cenv (BeePL.fn_body fd) fn_ctx bctx (initial_generator tt)) with 
  | Err msg => Error msg
  | Res (fbody, fn_ctx') g i => 
  
  let vt := (transBeePL_types transBeePL_type (List.map unzip_str (snd fbody))) in 
  
  (* Pull out any ident * string pairs that were added to fn_ctx during transBeePL_expr_st *)
  let is' := merge_ident_string (snd fbody) is in
  (* convert the beepl context as argument to ebpf context *)
  match (transform_ctx_ebpf_ctx (zip (unzip1 (fd.(fn_args))) (unzip2 (fd.(fn_args))))) with
  | Error msg => Error msg
  | OK params => 
  OK ({| fn_return := crt; 
         fn_callconv := cc_default; 
         fn_params := params;
         fn_vars := zip (List.map unzip_ident (snd fbody)) (from_typelist vt);
         fn_body :=  fst fbody |}, is', fn_ctx')
  end
  end
  end)
else
  (let crt := (transBeePL_type (fd.(BeePL.fn_return))) in
  let pt := (transBeePL_types transBeePL_type (unzip2 (fd.(fn_args)))) in 
  
  (* When using Ref a fresh variable is created which must be added to BeePL.fn_vars and ident_to_string *)
  (* fn_ctx is fn_vars (ident * type) plus the corresponding string from is (ident * string) *)
  match (create_fn_ctx (BeePL.fn_vars fd) is (initial_generator tt)) with
  | Err msg => Error msg
  | Res fn_ctx g i =>
  
  match (transBeePL_expr_st cenv (BeePL.fn_body fd) fn_ctx bctx (initial_generator tt)) with 
  | Err msg => Error msg
  | Res (fbody, fn_ctx') g i => 
  
  let vt := (transBeePL_types transBeePL_type (List.map unzip_str (snd fbody))) in 
  
  (* Pull out any ident * string pairs that were added to fn_ctx during transBeePL_expr_st *)
  let is' := merge_ident_string (snd fbody) is in
  OK ({| fn_return := crt; 
         fn_callconv := cc_default; 
         fn_params := zip (unzip1 (fd.(fn_args))) (from_typelist pt);
         fn_vars := zip (List.map unzip_ident (snd fbody)) (from_typelist vt);
         fn_body :=  fst fbody|}, is', fn_ctx')
  end
  end).
                        
            

Local Open Scope error_monad_scope.

Definition transBeePL_fundef_fundef (cenv : bcomposite_env) (fd : BeePL.fundef) (is : list (ident * string)) (bctx : bcompiler_ctx) : 
res (Csyntax.fundef * list (ident * string) * bcompiler_ctx) :=
match fd with 
| Internal f => do (tf, is') <- transBeePL_function_function cenv f is bctx;
                OK (Ctypes.Internal (fst tf), snd tf, is')
| External ef ts t cc => let cef := (befunction_to_cefunction ef) in
                         let cts := (transBeePL_types transBeePL_type ts) in 
                         let ct := (transBeePL_type t) in
                         OK ((Ctypes.External cef cts ct cc), is, bctx)
end.

(* Translates the value that is assigned to global variable to C global variable data *)

(*Definition transBeePL_init_data_init_data (g : BeePL.init_data) : AST.init_data :=
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
end. *)

(* Translates BeePL global variable to C global variable *)
Definition transBeePLglobvar_globvar (gv : BeePL.globvar type) : 
(AST.globvar Ctypes.type * list composite_definition) :=
let gvt := transBeePL_type (gv.(gvar_info)) in
       ({| AST.gvar_info := gvt; 
           AST.gvar_init := (gv.(gvar_init)); 
           AST.gvar_readonly := gv.(gvar_readonly); 
           AST.gvar_volatile :=  gv.(gvar_volatile)|}, nil).

Definition transBeePL_globdef_globdef (cenv : bcomposite_env) (gd : BeePL.globdef BeePL.fundef BeeTypes.type) (is : list (ident * string)) (bctx : bcompiler_ctx) : 
res ((AST.globdef fundef Ctypes.type) * list (ident * string) * list composite_definition * bcompiler_ctx) :=
match gd with 
| AST.Gfun f => do (cf, is') <- transBeePL_fundef_fundef cenv f is bctx;
                OK ((AST.Gfun (fst cf)), snd cf, nil, is')
| AST.Gvar g => let cg := transBeePLglobvar_globvar g in
                OK ((AST.Gvar (fst cg)), is, (snd cg), bctx)
end.

Fixpoint transBeePL_globdefs_globdefs (cenv : bcomposite_env) (gds : list (BeePL.globdef BeePL.fundef BeeTypes.type)) (is : list (ident * string)) (bctx : bcompiler_ctx) : 
res (list (AST.globdef fundef Ctypes.type) * list (ident * string) * list composite_definition * bcompiler_ctx) :=
match gds with 
| nil => OK (nil, is, nil, bctx)
| d :: ds => do (gd, is') <-  transBeePL_globdef_globdef cenv d is bctx; 
             do (gds, is'') <- transBeePL_globdefs_globdefs cenv ds (snd (fst gd)) is';
             OK ((fst (fst gd) :: fst (fst gds)), (snd (fst gds)), (snd gd ++ snd gds)%list, is'')
end.

(* Missing list of public functions *) 
Definition BeePL_compcert (p : BeePL.program) : res (Csyntax.program * list (ident * string)) :=
  let bctx := {| arg_ctx := get_args_ebpf_gbdefs (unzip2 p.(prog_defs)); benv := p.(prog_comp_env) |} in 
  do cp <- check_struct_from_program p;
  do (pds, is') <- transBeePL_globdefs_globdefs (prog_comp_env(p)) (unzip2 (p.(prog_defs))) (p.(prog_ident_to_string)) bctx;
  let ncs := get_bcs_from_globdefs (unzip2 (p.(prog_defs))) in (* adds bytes_t in composite *)
  let cs := (map bcomposite_ccomposite_definition p.(prog_types)) in 
  let mcs := (ncs ++ snd pds ++ wrapper_beepl_struct_ebpf_struct cs)%list in
  do cprog <- make_program mcs (zip (unzip1 p.(prog_defs)) (fst (fst pds))) (prog_public p) (prog_main p);
  OK (cprog, snd (fst pds)).
