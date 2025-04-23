Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values. 
From Coq Require Import String ZArith.
From compcert Require Import Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(*  extern int add(int, int* );
 *     
 *  int main(void) {
 *    int a = 1;
 *    int b = 2;
 *    int c = add(a, &b);
 *    return c;
 *  } 
 *
 *)


Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _a : ident := $"a".
Definition _b : ident := $"b".
Definition _c : ident := $"c".
Definition _add : ident := $"add".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ((_a, "a") :: 
                                                      (_b, "b") :: 
                                                      (_c, "c") ::
                                                      (_add, "add") :: 
                                                      (_main, "main") :: nil).

Definition prim_expr : BeePL.expr := Prim (Ref) 
                                          (Var _b (Ptype (BeeTypes.Tint I32 Signed dattr)) :: nil)
                                          (Reftype _b (Bprim (Tint Ctypes.I32 Ctypes.Signed dattr)) dattr).

Definition test : BeePL.expr := (App (Var _add (Ftype (Ptype (BeeTypes.Tint I32 Signed dattr) ::
                                                       Reftype _b (Bprim (Tint Ctypes.I32 Ctypes.Signed dattr)) dattr :: nil) (* args type signature *)
                                                      (nil) (* effect *)
                                                      (Ptype (BeeTypes.Tint I32 Signed dattr)))) (* return type *)
                                     (Var _a (Ptype (BeeTypes.Tint I32 Signed dattr)) :: 
                                      Prim (Ref) 
                                           (Var _b (Ptype (BeeTypes.Tint I32 Signed dattr)) :: nil)
                                           (Reftype _b (Bprim (Tint Ctypes.I32 Ctypes.Signed dattr)) dattr) :: nil)
                                     (Ptype (BeeTypes.Tint I32 Signed dattr))).

Definition f_external_call : BeePL.function := {| 
                                   fn_return := (Ptype (BeeTypes.Tint I32 Signed dattr));
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_a, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Signed dattr)) :: 
                                               (_b, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Signed dattr)) :: 
                                               (_c, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Signed dattr)) :: nil);
                                   fn_body := Bind 
                                                (_a) 
                                                (Ptype (BeeTypes.Tint I32 Signed dattr))
                                                (Const (ConsInt (Int.repr 1)) (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                (Bind 
                                                   (_b) 
                                                   (Ptype (BeeTypes.Tint I32 Signed dattr))
                                                   (Const (ConsInt (Int.repr 2)) (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                   (Bind 
                                                      (_c) 
                                                      (Ptype (BeeTypes.Tint I32 Signed dattr))
                                                      (App (Var _add (Ftype (Ptype (BeeTypes.Tint I32 Signed dattr) ::
                                                                             Reftype _b (Bprim (Tint Ctypes.I32 Ctypes.Signed dattr)) dattr :: nil) (* args type signature *)
                                                                            (nil) (* effect *)
                                                                            (Ptype (BeeTypes.Tint I32 Signed dattr)))) (* return type *)
                                                           (Var _a (Ptype (BeeTypes.Tint I32 Signed dattr)) :: 
                                                            Prim (Ref) 
                                                                 (Var _b (Ptype (BeeTypes.Tint I32 Signed dattr)) :: nil)
                                                                 (Reftype _b (Bprim (Tint Ctypes.I32 Ctypes.Signed dattr)) dattr) :: nil)
                                                           (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                      (Var _c (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                      (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                   (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                (Ptype (BeeTypes.Tint I32 Signed dattr)) |}.

Definition add_external_function : BeePL.external_function
   := EF_external "add" 
      {| bsig_args := (Ptype (BeeTypes.Tint I32 Signed dattr) :: 
                       Reftype _a (Bprim (Tint Ctypes.I32 Ctypes.Signed dattr)) dattr :: nil);
         bsig_ef := nil;
         bsig_res := Ptype (BeeTypes.Tint I32 Signed dattr);
         bsig_cc := cc_default
      |}.

Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_add, AST.Gfun(BeePL.External (add_external_function)
                                     (Ptype (BeeTypes.Tint I32 Signed dattr) :: 
                                      Reftype _a (Bprim (Tint Ctypes.I32 Ctypes.Signed dattr)) dattr :: nil)
                                     (Ptype (BeeTypes.Tint I32 Signed dattr))
                                     (cc_default))) :: 
      (_main, AST.Gfun(BeePL.Internal (f_external_call))):: nil.

Definition public_idents : list ident := (_main :: nil).
