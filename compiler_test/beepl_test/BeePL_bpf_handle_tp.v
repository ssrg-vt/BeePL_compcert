Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_notations BeePL_bpf Maps. 
From Coq Require Import String ZArith.
From compcert Require Import Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(*
/* SPDX-License-Identifier: (LGPL-2.1 OR BSD-2-Clause) */
#define BPF_NO_GLOBAL_DATA
#include <linux/bpf.h>
#include <bpf/bpf_helpers.h>
#include <bpf/bpf_tracing.h>

const long pid_filter = 0;

char LICENSE[] SEC("license") = "Dual BSD/GPL";

SEC("tp/syscalls/sys_enter_write")
int handle_tp(void *ctx)
{
 long pid = bpf_get_current_pid_tgid() >> 32;
 if (pid_filter && pid != pid_filter)
  return 0;
 bpf_printk("BPF triggered sys_enter_write from PID %d.\n", pid);
 return 0;
} *)

(*Definition _pid_filter : ident := $"pid_filter".
Definition _pid : ident := $"pid".
Definition _t : ident := $"t".
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition _handle_tp : ident := $"handle_tp".

Definition ident_to_string : list (ident * string) := ident_to_string_hf ++ ident_to_string_trace_entry ++ 
                                                      ident_to_string_trace_event_raw_sys_enter ++
                                                      ((_ctx, "ctx") :: (___stringlit_1, "__stringlit_1") ::
                                                       (_pid_filter, "pid_filter") ::
                                                       (_pid, "pid") :: (_t, "t") :: 
                                                       (_handle_tp, "handle_tp") :: nil).

Definition v___stringlit_1 := {|
  gvar_info := tbarray tint8s 4 noattr;
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 108) ::  Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_pid_filter := {|
  gvar_info := tlongu;
  gvar_init := (Init_int64 (Int64.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_handle_tp : BeePL.function := {| 
                                   fn_return := tint32s;
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := (_ctx, tpstruct _trace_event_raw_sys_enter) :: nil ;
                                   fn_vars := ((_pid, tlongu) :: (_t, tlongu) :: 
                                                nil);
                                   fn_body := Bind 
                                                (_pid) tlongu
                                                (Prim (Bop Cop.Oshr) 
                                                   (App (Var bpf_get_current_pid_tgid (tfun nil nil tlongu)) nil tlongu ::
                                                    Const (ConsLong (Int64.repr 32)) tlongu :: nil) tlongu)
                                                (Cond (Var _pid_filter tlongu)
                                                      (Cond (Prim (Bop Cop.One) 
                                                                  (Var _pid_filter tlongu :: Var _pid tlongu :: nil) tlongu)
                                                             (cint (Int.repr 0) tint32s)
                                                             (Bind _t tlongu
                                                               (App (Var bpf_printk (tfun (trint8s :: tint32s :: nil) (Io :: nil) tint32s))
                                                                  (Var ___stringlit_1 (tbarray tint8s 3 noattr) ::
                                                                   Var _pid tlongu :: nil) tint32s)
                                                               (cint (Int.repr 0) tint32s) tint32s) tint32s)
                                                         (cint (Int.repr 0) tint32s) tint32s) tint32s
                                                 ;
                                   is_ebpf := true |}.

Definition bcomposites : list bcomposite_definition := bcomposites_trace_entry ++ bcomposites_trace_event_raw_sys_enter.

Definition global_definitions : list (ident * AST.globdef BeePL.fundef type * option string) 
   :=  (_pid_filter, Gvar v_pid_filter, None) :: (___stringlit_1, Gvar v___stringlit_1, None) ::
       (bpf_get_current_pid_tgid, AST.Gfun(BeePL.External bpf_get_current_pid_tgid_ef
                                     nil tlongu
                                     (cc_default)), None) :: 
       (bpf_printk, AST.Gfun(BeePL.External bpf_printk_ef
                                     (trint8s :: tint32s :: nil) tint32s
                                     {|cc_vararg:=(Some (Z.of_nat 1)); cc_unproto:=false; cc_structret:=false|}), None) ::
       (_handle_tp, AST.Gfun(BeePL.Internal (f_handle_tp)), None) :: nil.


Definition public_idents : list ident := (_handle_tp :: nil).

Lemma bcomposite_correct :
  wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; constructor. 
Qed.*)

(*Definition example1 : BeePL.program := @mkbprogram bcomposites 
                                                   global_definitions 
                                                   public_idents 
                                                   _handle_tp 
                                                   bcomposite_correct
                                                   ident_to_string.

Compute (type_check_expr example1.(prog_comp_env) 
                         (bind_vars (bind_vars empty_context f_handle_tp.(fn_args)) f_handle_tp.(fn_vars)) empty_context f_handle_tp.(fn_body)).

Compute (type_check_program example1). *) (* Does not type checks *)


