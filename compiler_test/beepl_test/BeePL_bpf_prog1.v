Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_notations. 
From Coq Require Import String ZArith.
From compcert Require Import Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(* https://eunomia.dev/en/tutorials/1-helloworld/
/* SPDX-License-Identifier: (LGPL-2.1 OR BSD-2-Clause) */
#define BPF_NO_GLOBAL_DATA
#include <linux/bpf.h>
#include <bpf/bpf_helpers.h>
#include <bpf/bpf_tracing.h>

typedef unsigned int u32;
typedef int pid_t;
const pid_t pid_filter = 0;

char LICENSE[] SEC("license") = "Dual BSD/GPL";

SEC("tp/syscalls/sys_enter_write")
int handle_tp(void *ctx)
{
 pid_t pid = bpf_get_current_pid_tgid() >> 32;
 if (pid_filter && pid != pid_filter)
  return 0;
 bpf_printk("BPF triggered sys_enter_write from PID %d.\n", pid);
 return 0;
} *)

Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _bpf_get_current_pid_tgid : ident := $"bpf_get_current_pid_tgid".
Definition _pid : ident := $"pid".
Definition _pid_filter : ident := $"pid_filter".
Definition _handle_tp : ident := $"handle_tp".

Definition ident_to_string : list (ident * string) := ((_pid_filter, "pid_filter") ::
                                                       (_bpf_get_current_pid_tgid, "bpf_get_current_pid_tgid") :: 
                                                       (_handle_tp, "handle_tp") :: 
                                                       (_pid, "pid") :: nil).

Definition bpf_external_function : BeePL.external_function
   := EF_external "bpf_get_current_pid_tgid" 
      {| bsig_args := nil;
         bsig_ef := nil;
         bsig_res := tint32u;
         bsig_cc := cc_default
      |}.

Definition v_pid_filer := {|
  gvar_info := tint32u;
  gvar_init := (Init_int32 (Int.repr 5) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_bpf_prog : BeePL.function := {| 
                                   fn_return := tint32u;
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil ;
                                   fn_vars := ((_pid, tint32u) :: 
                                                nil);
                                   fn_body := Bind 
                                                (_pid) tint32u
                                                (Prim (Bop Cop.Shr) 
                                                          ((App (Var _bpf_get_current_pid_tgid (tfun nil nil tint32u)) nil tint32u) ::
                                                           (cint (Int.repr 32) tint32u) :: nil) tint32u) 
                                                (Cond (Bop Cop.neq
                                                (Prim (Bop Cop.Oand) (Var _ts tlongu :: clong (Int64.repr 0xFFFFFFFF) tlongu :: nil) tlongu)
                                              tlongu|}.

Definition bcomposites : list bcomposite_definition :=
(Bcomposite _pt_regs Struct
   (Member_plain _ebx tlongs :: 
    Member_plain _ecx tlongs ::
    Member_plain _edx tlongs ::
    Member_plain _esi tlongs ::
    Member_plain _edi tlongs ::
    Member_plain _ebp tlongs ::
    Member_plain _eax tlongs ::
    Member_plain _xds tint32s ::
    Member_plain _xes tint32s ::
    Member_plain _xfs tint32s ::
    Member_plain _xgs tint32s ::
    Member_plain _orig_eax tlongs ::
    Member_plain _eip tlongs ::
    Member_plain _xcs tint32s ::
    Member_plain _eflags tlongs ::
    Member_plain _esp tlongs ::
    Member_plain _xss tint32s :: nil)
    noattr :: nil).


Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_bpf_ktime_get_ns, AST.Gfun(BeePL.External (bpf_external_function)
                                     nil tlongu (cc_default))) :: 
      (_bpf_prog, AST.Gfun(BeePL.Internal (f_bpf_prog))) :: nil.

Definition public_idents : list ident := (_bpf_prog :: nil).

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


Compute (type_check_program example1).*) (* Type checks *)
