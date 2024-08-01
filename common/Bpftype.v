(* This file defines the spec/information/signature that needs to be ensured for various helper functions. *)
(* https://github.com/torvalds/linux/blob/master/include/linux/bpf_verifier.h *)
(* https://github.com/torvalds/linux/blob/c91a7dee0555f6f9d3702d86312382e4c4729d0a/include/linux/bpf.h *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.

Inductive base_bpf_return_type : Type := 
| RET_INTEGER : base_bpf_return_type  (* function return integer *)
| RET_VOID : base_bpf_return_type (* function doesn't return anything *)
| RET_PTR_TO_MAP_VALUE : base_bpf_return_type (* function returns a pointer to map elem value *)
| RET_PTR_TO_SOCKET : base_bpf_return_type (* function returns a pointer to a socket *)
| RET_PTR_TO_TCP_SOCK : base_bpf_return_type (* function returns a pointer to a tcp_sock *)
| RET_PTR_TO_SOCK_COMMON : base_bpf_return_type (* function returns a pointer to a sock_common *)
| RET_PTR_TO_MEM : base_bpf_return_type (* function returns a pointer a memory *)
| RET_PTR_TO_MEM_OR_BTF_ID : base_bpf_return_type (* function returns a pointer to a valid memory or a btf_id *)
| RET_PTR_TO_BTF_ID : base_bpf_return_type (* function returns a pointer to a btf_id *)
| RET_PTR_TO_MAP_VALUE_OR_NULL : bool -> base_bpf_return_type
| RET_NULL : base_bpf_return_type.

Definition check_ptr_map_null (t : base_bpf_return_type) : base_bpf_return_type :=
    match t with 
        | RET_PTR_TO_MAP_VALUE_OR_NULL true => RET_NULL
        | RET_PTR_TO_MAP_VALUE_OR_NULL false => RET_PTR_TO_MAP_VALUE
        | _ => RET_NULL
    end.

