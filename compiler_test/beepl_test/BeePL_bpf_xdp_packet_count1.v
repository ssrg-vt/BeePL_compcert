Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_notations BeePL_bpf. 
From Coq Require Import String ZArith.
From compcert Require Import Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(* #include <linux/bpf.h>
#include <bpf/bpf_helpers.h>

int counter = 0;

SEC("xdp")
int packet_count(void *ctx) {
    counter++;
    return *counter;
}

char LICENSE[] SEC("license") = "Dual BSD/GPL";*)


(*Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _counter : ident := $"counter".
Definition _r : ident := $"r".
Definition _val : ident := $"val".
Definition _ctx : ident := $"ctx".
Definition _xdp_packet_count : ident := $"xdp_packet_count".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ident_to_string_xdp_md ++
                                                      ((_val, "val") ::
                                                       (_ctx, "ctx") ::
                                                       (_counter, "counter") ::
                                                       (_r, "r") ::
                                                       (_xdp_packet_count, "xdp_packet_count") :: 
                                                       (_main, "main") :: nil).

Definition v_val := {|
  gvar_info := tint32u;
  gvar_init := (Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_counter := {|
  gvar_info := trint32u;
  gvar_init := (Init_addrof _val Ptrofs.zero :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_xdp_packet_count : BeePL.function := {| 
                                   fn_return := tint32s;
                                   fn_effect := Read mem_ident :: Write mem_ident :: Read mem_ident :: nil;
                                   fn_callconv := cc_default;
                                   fn_args := (_ctx, tpstruct _xdp_md) :: nil ;
                                   fn_vars := ((_r, tint32s) :: 
                                                nil);
                                   fn_body := Bind _r tint32s
                                                (Prim Massgn (Var _counter trint32s ::
                                                                (Prim (Bop Cop.Oadd) 
                                                                   (Prim Deref (Var _counter trint32s :: nil) tint32s ::
                                                                      cint (Int.repr 1) tint32s :: nil) tint32s) :: nil) tunit)
                                                (Prim Deref (Var _counter trint32s :: nil) tint32s) tint32s;
                                   is_ebpf := true |}.

Definition bcomposites : list bcomposite_definition := bcomposites_xdp_md.

Definition global_definitions : list (ident * AST.globdef BeePL.fundef type * option string) 
   := (_val, Gvar v_val, None) :: 
      (_counter, Gvar v_counter, None) :: 
      (_xdp_packet_count, AST.Gfun(BeePL.Internal (f_xdp_packet_count)), None) :: nil.

Definition public_idents : list ident := (_xdp_packet_count :: _counter :: _val :: nil).

Lemma bcomposite_correct :
  wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; constructor. 
Qed.

(*Definition example1 : BeePL.program := @mkbprogram bcomposites 
                                                   global_definitions 
                                                   public_idents 
                                                   _main 
                                                   bcomposite_correct
                                                   ident_to_string.

Compute (type_check_expr example1.(prog_comp_env) 
                         (bind_vars (bind_vars empty_context f_xdp_packet_count.(fn_args)) f_xdp_packet_count.(fn_vars)) empty_context f_xdp_packet_count.(fn_body)).*)


Compute (type_check_program example1). *) (* Type checks! *)
