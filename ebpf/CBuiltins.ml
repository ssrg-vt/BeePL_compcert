open C

let builtins = {
  builtin_typedefs = [];
  builtin_functions = [];
}

let asm_mem_argument arg = Printf.sprintf "0(%s)" arg

let va_list_scalar = false
let va_list_type = TPtr(TVoid [], [])  (* to check! *)
let size_va_list = if Archi.ptr64 then 8 else 4
