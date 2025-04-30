Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Coq.Lists.List.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes Coqlib SimplExpr Csyntaxdefs BeePL_notations.
Require Import BeePL_aux BeePL BeeTypes Csyntax Errors SimplExpr BeePL_values DecimalString BeePL_Option_Struct BeePL_Check_Reserved_Struct.

Local Open Scope string_scope.
Local Open Scope gensym_monad_scope.
(**** BeePL Compiler *****)
Section transBeePL_exprs.

Variables transBeePL_expr_expr : BeePL.expr -> list (ident * BeeTypes.type * string) -> mon (Csyntax.expr * list (ident * BeeTypes.type * string)).

Definition max_fresh : nat := 1000%nat.

(* Translates list of BeePL expressions to list of C expressions *)
Fixpoint transBeePL_expr_exprs (es : list BeePL.expr) (fn_ctx : list (ident * BeeTypes.type * string)) : mon (Csyntax.exprlist * list (ident * BeeTypes.type * string)) :=
match es with 
| nil => ret (Enil, fn_ctx) 
| e :: es => do (ce, fn_ctx') <- transBeePL_expr_expr e fn_ctx;
             do (ces, fn_ctx'') <- transBeePL_expr_exprs es fn_ctx';
             ret ((Econs ce ces), fn_ctx'')
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

(* Used for extracting the correct type for a Ref's fresh variable *)
Definition ref_to_prim (ty : type) : mon type :=
  match ty with
  | Reftype _ (Bprim pt) _ => ret (Ptype pt)
  | Reftype _ (Bstruct s a) _ => ret (Stype s a)
  | _ => error (msg "ref_to_prim: expected only reftype")
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

Fixpoint transBeePL_expr_expr (e : BeePL.expr) (fn_ctx : list (ident * BeeTypes.type * string)) : mon (Csyntax.expr * (list (ident * BeeTypes.type * string))) := 
match e with 
| Val v t => ret (Eval (trans_bvalue_cvalue v) (transBeePL_type t), fn_ctx) 
| Var x t => ret (Evar x (transBeePL_type t), fn_ctx)
| Const c t => match c with 
               | ConsInt i => ret (Eval (Values.Vint i) (transBeePL_type t), fn_ctx)
               | ConsLong i => ret (Eval (Values.Vlong i) (transBeePL_type t), fn_ctx)
               | ConsUnit => ret (Eval (Values.Vint (Int.repr 0)) (transBeePL_type t), fn_ctx) 
               | ConsBool b => ret (if eqb b true 
                                    then (Eval (Values.Vint (Int.repr 1)) (transBeePL_type t), fn_ctx) 
                                    else (Eval (Values.Vint (Int.repr 0)) (transBeePL_type t), fn_ctx))
               end
| App e es t => do (ce, fn_ctx') <- (transBeePL_expr_expr e fn_ctx); 
                do (ces, fn_ctx'') <- (transBeePL_expr_exprs transBeePL_expr_expr es fn_ctx');
                ret (Ecall ce ces (transBeePL_type t), fn_ctx'')
| Prim b es t => match b with 
                 | Ref => (* es: function arguments. If a function argument is Ref a fresh variable needs to be inserted prior to bind 
                         
                             let x = 3 in
                             let y = add(x, ref(4))

                             should become

                             int x = 3;
                             int __fresh; <- can be acomplished by adding a fresh variable to fn_ctx
                             int y = add(x, (__fresh = 4, &_fresh));
                           *)
                          do (ces, fn_ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es fn_ctx);
                          let ct := (transBeePL_type t) in
                          do (i, str) <- (fresh_ident (List.map unzip_ident fn_ctx') max_fresh);

                          match es with
                          | e :: nil => do pty <- ref_to_prim t;
                                        let cpty := (transBeePL_type pty) in
                                        let fn_ctx'' := (i, pty, str) :: fn_ctx' in
                                        ret ((Ecomma (Eassign (Evar i cpty) 
                                                              (hd default_expr (exprlist_list_expr ces)) 
                                                              (cpty)) 
                                                     (Eaddrof (Evar i ct) 
                                                              (ct))
                                                     (ct)), fn_ctx'')
                          | _ => error (msg "COMPILER ERROR: Ref should only have one expr in its expr list.")
                          end
                 | Deref => do (ces, fn_ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es fn_ctx);
                            let ct := (transBeePL_type t) in
                            ret ((Ederef (hd default_expr (exprlist_list_expr ces)) 
                                ct), fn_ctx')   
                 | Massgn => do (ces, fn_ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es fn_ctx);
                                        let ct := (transBeePL_type t) in
                                        ret ((Eassign (Ederef (hd default_expr (exprlist_list_expr ces)) 
                                                         (typeof (hd default_expr (exprlist_list_expr ces))))
                                                (hd default_expr (tl (exprlist_list_expr ces)))
                                                ct), fn_ctx')
                 | Run h => ret ((Eval (Values.Vundef) Tvoid), fn_ctx)
                 | Uop o => do (ces, fn_ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es fn_ctx);
                            let ct := (transBeePL_type t) in
                            ret ((Eunop o
                                (hd default_expr (exprlist_list_expr ces)) 
                                ct), fn_ctx')
                 | Bop o => do v <- return_czero (transBeePL_type t);
                            do (ces, fn_ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es fn_ctx);
                            match o with 
                            | Cop.Odiv => do rs <- (check_div ces v (transBeePL_type t));
                                          ret (rs, fn_ctx')
                                                                      
                            | Cop.Omod => do rs <- (check_mod ces v (transBeePL_type t));
                                          ret (rs, fn_ctx')
                            | Cop.Oshl => do rs <- check_shl ces v (transBeePL_type t);
                                          ret (rs, fn_ctx')
                             | Cop.Oshr => do rs <- check_shr ces v (transBeePL_type t);
                                           ret (rs, fn_ctx')
                            | _ => ret (Ebinop o
                                        (hd default_expr (exprlist_list_expr ces)) 
                                        (hd default_expr (tl (exprlist_list_expr ces)))
                                        (transBeePL_type t), fn_ctx')

                           end
end
| Bind x t e e' t' => let ct := (transBeePL_type t) in
                      do (ce, fn_ctx') <- (transBeePL_expr_expr e fn_ctx);
                      do (ce', fn_ctx'') <- (transBeePL_expr_expr e' fn_ctx');
                      let ct' := (transBeePL_type t') in
                      ret (Ecomma (Eassign (Evar x ct) ce ct) ce' ct', fn_ctx'') 
| Cond e e' e'' t => do (ce, fn_ctx') <- (transBeePL_expr_expr e fn_ctx);
                     do (ce', fn_ctx'') <- (transBeePL_expr_expr e' fn_ctx');
                     do (ce'', fn_ctx''') <- (transBeePL_expr_expr e'' fn_ctx'');
                     let ct := (transBeePL_type t) in
                     ret (Econdition ce ce' ce'' ct, fn_ctx''')  
| Unit t=> let ct := (transBeePL_type t) in
           ret (Eval (trans_bvalue_cvalue Vunit) ct, fn_ctx) (* Fix me *)
| Addr l ofs t => let ct := transBeePL_type t in
                  ret (Eloc l.(lname) ofs l.(lbitfield) ct, fn_ctx)
| Hexpr h e t => ret (Eval (Values.Vundef) Tvoid, fn_ctx) (* FIX ME *)
| Eapp ef ts es t => let cef := befunction_to_cefunction ef in
                     let cts := (transBeePL_types transBeePL_type ts) in
                     let ct := (transBeePL_type t) in
                     do (ces, fn_ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es fn_ctx);
                     ret (Ebuiltin cef cts ces ct, fn_ctx')
| Screate x ids es t => error (msg "COMPILER ERROR: Struct creation cannot be translated to another C epxr")
| Sfield e x t => do (ce, fn_ctx') <- transBeePL_expr_expr e fn_ctx;
                  let ct := transBeePL_type t in
                  ret (Efield (Evalof ce (transBeePL_type (typeof_expr e))) x ct, fn_ctx')
| For e1 e2 d e t => error (msg "COMPILER ERROR: For loop cannot be translated to another C expr")
| Enone t => match t with 
             | Otype t' => if is_reftype t'
                           then ret ((Ecast (Eval (Values.Vint (Int.repr 0)) tint) (tptr (transBeePL_type t))), fn_ctx)
                           else error (msg "COMPILER ERROR: Option type of None should contain a pointer in BeePL")
             | _ => error (msg "COMPILER ERROR: None should be of Option type")
             end
| Esome e t => match t with 
               | Otype t' => if is_reftype t'
                             then transBeePL_expr_expr e fn_ctx
                             else error (msg "COMPILER ERROR: Option type of Some should contain a pointer in BeePL")
               | _ => error (msg "COMPILER ERROR: Some should be of Option type")
              end
| Match e ps es t => if is_reftype t
                     then do ce <- transBeePL_expr_expr e fn_ctx;
                          match ps, es with 
                          | nil, nil => error (msg "COMPILER ERROR: No pattern matching cases found")
                          | (Pnone :: Psome x :: nil), (e1 :: e2 :: nil) => 
                             do ce1 <- transBeePL_expr_expr e1 fn_ctx;
                             do ce2 <- transBeePL_expr_expr e2 (snd ce1);
                             ret ((Econdition (Ebinop Cop.Oeq (fst ce) 
                                                (Ecast (Eval (Values.Vint (Int.repr 0)) tint) (tptr (transBeePL_type t)))
                                               (Ctypes.Tint Ctypes.I8 Ctypes.Unsigned noattr))
                                  (fst ce1)
                                  (fst ce2) (transBeePL_type t)), snd (ce2))
                          | (Psome x :: Pnone :: nil), (e1 :: e2 :: nil) => 
                             do ce1 <- transBeePL_expr_expr e1 fn_ctx;
                             do ce2 <- transBeePL_expr_expr e2 (snd ce1);
                             ret ((Econdition (Ebinop Cop.Oeq (fst ce) 
                                                (Ecast (Eval (Values.Vint (Int.repr 0)) tint) (tptr (transBeePL_type t)))
                                               (Ctypes.Tint Ctypes.I8 Ctypes.Unsigned noattr))
                                  (fst ce2)
                                  (fst ce1) (transBeePL_type t)), snd (ce1))
                          | _, _ => error (msg "COMPILER ERROR: We support only two patterns as of now")
                        end
                   else error (msg "COMPILER ERROR: The return type of matching should be a pointer")
end.


Definition check_var_const (e : BeePL.expr) : bool :=
match e with 
| Var x t => true 
| Const c t => true 
| _ => false
end.

Fixpoint transBeePL_expr_st (e : BeePL.expr ) (ctx : list (ident * BeeTypes.type * string)) : mon (Csyntax.statement * list (ident * BeeTypes.type * string)) :=
match e with 
| Val v t => let vt := (transBeePL_type t) in
             ret (Sreturn (Some (Eval (trans_bvalue_cvalue v) vt)), ctx) 
| Var x t => let ct := (transBeePL_type t) in
             ret (Sreturn (Some (Evalof (Evar x ct) ct)), ctx)
| Const c t => let ct := (transBeePL_type t) in
               ret (Sreturn (Some (Evalof (match c with 
                                      | ConsInt i => Eval (Values.Vint i) ct
                                      | ConsLong i => Eval (Values.Vlong i) ct
                                      | ConsUnit => Eval (Values.Vint (Int.repr 0)) ct
                                      | ConsBool b => if eqb b true 
                                                      then Eval (Values.Vint (Int.repr 1)) ct
                                                      else Eval (Values.Vint (Int.repr 0)) ct
                                      end) ct)), ctx)
| App e es t => do (ce, ctx') <- (transBeePL_expr_expr e ctx);
                do (ces, ctx'') <- (transBeePL_expr_exprs transBeePL_expr_expr es ctx');
                let ct := (transBeePL_type t) in
                ret (Sdo (Ecall ce ces ct), ctx'')  
| Prim b es t => match b with 
                 | Ref => (* TODO: figure out how to recude duplicate code between here and transBeePL_expr_st *)
                          do (ces, ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es ctx);
                          let ct := (transBeePL_type t) in
                          do (i, str) <- (fresh_ident (List.map unzip_ident ctx') max_fresh);
                          match es with
                          | e :: nil => do pty <- ref_to_prim t;
                                        let cpty := (transBeePL_type pty) in        
                                        let ctx'' := (i, pty, str) :: ctx' in
                                        ret (Ssequence (Sdo (Eassign (Evar i cpty)
                                                                     (hd default_expr (exprlist_list_expr ces))
                                                                     (cpty)))
                                                       (Sdo (Eaddrof (Evar i ct) 
                                                                     (ct))), ctx'')
                          | _ => error (msg "COMPILER ERROR: Ref should only have one expr in its expr list.")
                          end
                 | Deref => do (ces, ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es ctx);
                            let ct := (transBeePL_type t) in
                            ret (Sreturn (Some (Ederef (hd default_expr (exprlist_list_expr ces)) 
                                     ct)), ctx')   
                 | Massgn => do (ces, fn_ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es ctx);
                                        let ct := (transBeePL_type t) in
                                        ret (Sdo (Eassign (Ederef (hd default_expr (exprlist_list_expr ces)) 
                                                             (typeof (hd default_expr (exprlist_list_expr ces)))) 
                                                (hd default_expr (tl (exprlist_list_expr ces)))
                                                ct), fn_ctx')
                 | Run h => ret (Sdo (Eval (Values.Vundef) Tvoid), ctx)
                 | Uop o => do (ces, ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es ctx);
                            let ct := (transBeePL_type t) in 
                            ret (Sdo (Eunop o 
                                     (hd default_expr (exprlist_list_expr ces)) 
                                     ct), ctx') 
                 | Bop o => do v <- return_czero (transBeePL_type t);
                            do (ces, fn_ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es ctx);
                            match o with 
                            | Cop.Odiv => do rs <- (check_div ces v (transBeePL_type t));
                                          ret (Sdo rs, fn_ctx')
                                                                      
                            | Cop.Omod => do rs <- (check_div ces v (transBeePL_type t));
                                          ret (Sdo rs, fn_ctx')
                            | Cop.Oshl => do rs <- check_shl ces v (transBeePL_type t);
                                          ret (Sdo rs, fn_ctx')
                             | Cop.Oshr => do rs <- check_shr ces v (transBeePL_type t);
                                           ret (Sdo rs, fn_ctx')
                            | _ => ret (Sdo (Ebinop o
                                        (hd default_expr (exprlist_list_expr ces)) 
                                        (hd default_expr (tl (exprlist_list_expr ces)))
                                        (transBeePL_type t)), fn_ctx')

                           end
                 end 
| Bind x t e e' t' => let ct := (transBeePL_type t) in
                      do (ce', ctx') <- (transBeePL_expr_st e' ctx);
                      match e with 
                      | Prim Massgn es t => do (ce, ctx'') <- (transBeePL_expr_expr e ctx'); ret (Ssequence (Sdo ce) ce', ctx'') 
                      | For e1 e2 d e3 t => do (cs, ctx'') <- (transBeePL_expr_st e ctx'); ret (Ssequence cs ce', ctx'')  
                      | Screate sx ids es t =>  do (cs, ctx'') <- (transBeePL_expr_st e ctx'); ret (Ssequence cs ce', ctx'')                                                                        
                      | _ =>  do (ce, ctx'') <- (transBeePL_expr_expr e ctx');
                                    ret (Ssequence (Sdo (Eassign (Evar x ct) ce Tvoid)) 
                                           (ce'), ctx'')
                      end
| Cond e e' e'' t' => do (ce, ctx') <- (transBeePL_expr_expr e ctx);
                      do (ce', ctx'') <- (transBeePL_expr_st e' ctx');
                      do (ce'', ctx''') <- (transBeePL_expr_st e'' ctx'');
                      let ct' := (transBeePL_type t') in
                      ret (Sifthenelse ce ce' ce'', ctx''')
                      (*if (check_var_const e' && check_var_const e'') (* check for expressions with side-effects *)
                      then ret (Sifthenelse ce ce' ce'')
                      else if (check_var_const e') then ret (Sifthenelse ce ce' ce'')
                                                   else if (check_var_const e'') 
                                                        then ret (Sifthenelse ce ce' (Sreturn (Some (Evalof ce'' ct'))))
                                                        else ret (Sifthenelse ce ce' (Sdo ce''))*)
| Unit t=> ret (Sskip, ctx) (*Sreturn (Some (Eval (Values.Vint (Int.repr 0)) (Ctypes.Tint I32 Unsigned noattr)))*) (* In case of unit, we return 0 *)
| Addr l ofs t => let ct := (transBeePL_type t) in
                  ret (Sdo (Eloc l.(lname) ofs l.(lbitfield) ct), ctx)                    
| Hexpr h e t => ret (Sdo (Eval (Values.Vundef) Tvoid), ctx) (* FIX ME *)
| Eapp ef ts es t => let cef := befunction_to_cefunction ef in
                     let cts := (transBeePL_types transBeePL_type ts) in
                     let ct := (transBeePL_type t) in
                     do (ces, ctx') <- (transBeePL_expr_exprs transBeePL_expr_expr es ctx);
                     ret (Sdo (Ebuiltin cef cts ces ct), ctx')
| Screate sx ids es t => do (ces, ctx') <- transBeePL_expr_exprs transBeePL_expr_expr es ctx;
                         do (temp, strl) <- (fresh_ident (List.map unzip_ident ctx') max_fresh);
                         do pty <- ref_to_prim t;
                         let ctx'' := (temp, pty, strl) :: ctx' in
                         do rs <- init_struct_fields sx (zip ids (exprlist_list_expr ces)) (transBeePL_type t) (transBeePL_type pty);
                         ret (Ssequence (Sdo (Eassign (Evar sx (transBeePL_type t)) 
                                                                         (Eaddrof (Evar temp (transBeePL_type pty)) (transBeePL_type t)) (transBeePL_type t)))
                                                            rs, ctx'')
| Sfield e x t => do (ce, ctx') <- transBeePL_expr_expr e ctx;
                  let ct := transBeePL_type t in
                  ret (Sdo (Evalof (Efield (Evalof ce (transBeePL_type (typeof_expr e))) x ct) ct), ctx')
| For e1 e2 d e t => do (ce1, ctx1) <- transBeePL_expr_expr e1 ctx;
                     do (low, strl) <- (fresh_ident (List.map unzip_ident ctx1) max_fresh);
                     let ctx2 := (low, typeof_expr e1, strl) :: ctx1 in
                     do (ce2, ctx3) <- transBeePL_expr_expr e2 ctx2;
                     do (high, strh) <- (fresh_ident (List.map unzip_ident ctx3) max_fresh);
                     let ctx4 := (high, typeof_expr e2, strh) :: ctx3 in
                     do (ce3, ctx5) <- transBeePL_expr_st e ctx4;
                     do (i, stri) <- (fresh_ident (List.map unzip_ident ctx4) max_fresh);
                     let ctx6 := (i, typeof_expr e1, stri) :: ctx5 in
                     match d with 
                     | Up => ret (Ssequence (Ssequence (Sdo (Eassign (Evar low (typeof ce1)) ce1 (typeof ce1)))
                                                       (Sdo (Eassign (Evar high (typeof ce2)) ce2 (typeof ce2))))
                                            (Sifthenelse (Ebinop Cop.Ole (Evar low (typeof ce1)) (Evar high (typeof ce2)) (typeof ce1))
                                                         (Sfor (Sdo (Eassign (Evar i (typeof ce1)) (Evar low (typeof ce1)) (typeof ce1)))
                                                               (Ebinop Cop.Ole (Evalof (Evar i (typeof ce2)) (typeof ce2)) (Evar high (typeof ce2)) (typeof ce2))
                                                               (Sdo (Epostincr Cop.Incr (Evar i (typeof ce2)) (typeof ce2)))
                                                          ce3)
                                                         Sskip), ctx6)
                     | Down => ret (Ssequence (Ssequence (Sdo (Eassign (Evar low (typeof ce1)) ce1 (typeof ce1)))
                                                         (Sdo (Eassign (Evar high (typeof ce2)) ce2 (typeof ce2))))
                                              (Sifthenelse (Ebinop Cop.Oge (Evar low (typeof ce1)) (Evar high (typeof ce2)) (typeof ce1))
                                                           (Sfor (Sdo (Eassign (Evar i (typeof ce1)) (Evar low (typeof ce1)) (typeof ce1)))
                                                                 (Ebinop Cop.Oge (Evalof (Evar i (typeof ce2)) (typeof ce2)) (Evar high (typeof ce2)) (typeof ce2))
                                                                 (Sdo (Epostincr Cop.Decr (Evar i (typeof ce2)) (typeof ce2)))
                                                            ce3)
                                                            Sskip), ctx6)
                     end
| Enone t => match t with 
             | Otype t' => if is_reftype t'
                           then ret (Sdo ((Ecast (Eval (Values.Vint (Int.repr 0)) tint) (tptr (transBeePL_type t)))), ctx)
                           else error (msg "COMPILER ERROR: Option type of None should contain a pointer in BeePL")
             | _ => error (msg "COMPILER ERROR: None should be of Option type")
             end
| Esome e t => match t with 
               | Otype t' => if is_reftype t'
                             then transBeePL_expr_st e ctx
                             else error (msg "COMPILER ERROR: Option type of Some should contain a pointer in BeePL")
               | _ => error (msg "COMPILER ERROR: Some should be of Option type")
              end
| Match e ps es t => do ce <- transBeePL_expr_expr e ctx;
                     match ps, es with 
                     | nil, nil => error (msg "COMPILER ERROR: No pattern matching cases found")
                     | (Pnone :: Psome x :: nil), (e1 :: e2 :: nil) => 
                       do ce1 <- transBeePL_expr_st e1 ctx;
                       do ce2 <- transBeePL_expr_st e2 (snd ce1);
                       ret ((Sifthenelse (Ebinop Cop.Oeq (fst ce) 
                                          (Ecast (Eval (Values.Vint (Int.repr 0)) tint) (tptr (transBeePL_type t)))
                                          (Ctypes.Tint Ctypes.I8 Ctypes.Unsigned noattr))
                                  (fst ce1)
                                  (fst ce2)), snd (ce2))
                    | (Psome x :: Pnone :: nil), (e1 :: e2 :: nil) => 
                      do ce1 <- transBeePL_expr_st e1 ctx;
                      do ce2 <- transBeePL_expr_st e2 (snd ce1);
                      ret ((Sifthenelse (Ebinop Cop.Oeq (fst ce) 
                                                (Ecast (Eval (Values.Vint (Int.repr 0)) tint) (tptr (transBeePL_type t)))
                                               (Ctypes.Tint Ctypes.I8 Ctypes.Unsigned noattr))
                                  (fst ce2)
                                  (fst ce1)), snd (ce1))
                    | _, _ => error (msg "COMPILER ERROR: We support only two patterns as of now")
                    end
end.


(* Translates the BeePL function declaration to C function *) 
Definition transBeePL_function_function (fd : BeePL.function) (is : list (ident * string)) : res (Csyntax.function * list (ident * string)) :=
  let crt := (transBeePL_type (fd.(BeePL.fn_return))) in
  let pt := (transBeePL_types transBeePL_type (unzip2 (fd.(fn_args)))) in 
  
  (* When using Ref a fresh variable is created which must be added to BeePL.fn_vars and ident_to_string *)
  (* fn_ctx is fn_vars (ident * type) plus the corresponding string from is (ident * string) *)
  match (create_fn_ctx (BeePL.fn_vars fd) is (initial_generator tt)) with
  | Err msg => Error msg
  | Res fn_ctx g i =>
  
  match (transBeePL_expr_st (BeePL.fn_body fd) fn_ctx (initial_generator tt)) with 
  | Err msg => Error msg
  | Res (fbody, fn_ctx') g i => 
  
  let vt := (transBeePL_types transBeePL_type (List.map unzip_str fn_ctx')) in 
  
  (* Pull out any ident * string pairs that were added to fn_ctx during transBeePL_expr_st *)
  let is' := merge_ident_string fn_ctx' is in
  OK ({| fn_return := crt; 
         fn_callconv := cc_default; 
         fn_params := zip (unzip1 (fd.(fn_args))) (from_typelist pt);
         fn_vars := zip (List.map unzip_ident fn_ctx') (from_typelist vt);
         fn_body :=  fbody|}, is')
  end
end.
                        
            

Local Open Scope error_monad_scope.

Definition transBeePL_fundef_fundef (fd : BeePL.fundef) (is : list (ident * string)) : res (Csyntax.fundef * list (ident * string)) :=
match fd with 
| Internal f => do (tf, is') <- transBeePL_function_function f is;
                OK (Ctypes.Internal tf, is')
| External ef ts t cc => let cef := (befunction_to_cefunction ef) in
                         let cts := (transBeePL_types transBeePL_type ts) in 
                         let ct := (transBeePL_type t) in
                         OK ((Ctypes.External cef cts ct cc), is)
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

Definition transBeePL_globdef_globdef (gd : BeePL.globdef BeePL.fundef BeeTypes.type) (is : list (ident * string)) : res ((AST.globdef fundef Ctypes.type) * list (ident * string)) :=
match gd with 
| AST.Gfun f => do (cf, is') <- transBeePL_fundef_fundef f is;
                OK ((AST.Gfun cf), is')
| AST.Gvar g => let cg := transBeePLglobvar_globvar g in
                OK ((AST.Gvar cg), is)
end.

Fixpoint transBeePL_globdefs_globdefs (gds : list (BeePL.globdef BeePL.fundef BeeTypes.type)) (is : list (ident * string)) : res (list (AST.globdef fundef Ctypes.type) * list (ident * string)) :=
match gds with 
| nil => OK (nil, is)
| d :: ds => do (gd, is') <-  transBeePL_globdef_globdef d is; 
             do (gds, is'') <- transBeePL_globdefs_globdefs ds is';
             OK ((gd :: gds), is'')
end.

(* Missing compositie information and list of public functions *) 
Definition BeePL_compcert (p : BeePL.program) : res (Csyntax.program * list (ident * string)) :=
  do (pds, is') <- transBeePL_globdefs_globdefs (unzip2 (p.(prog_defs))) (p.(prog_ident_to_string));
  do cprog <- make_program (map bcomposite_ccomposite_definition p.(prog_types)) (zip (unzip1 p.(prog_defs)) pds) (prog_public p) (prog_main p);
  OK (cprog, is').
