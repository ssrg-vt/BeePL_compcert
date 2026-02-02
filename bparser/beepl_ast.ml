type effect = 
  | Divergence 
  | Read  
  | Write 
  | Alloc 
  | Io

type ptype = 
  | Tbool
  | Tuint8
  | Tint8
  | Tuint16
  | Tint16
  | Tuint32
  | Tint32
  | Tulong
  | Tlong

type btype =
  | Bprim of ptype 
  | Bstruct of string
  | Barray of ptype * int

type ptrtype =
  | Reftype of btype
  | Otype of ptrtype

type typ = 
  | Utype
  | Vtype of ptype 
  | Ptr of ptrtype
  | Stype of string  (* struct type name *)
  | Atype of typ * int  (* array type with fixed size *)
  | Ftype of typ list * effect list * typ * bool  (* function type: args, effects, return type, is_variadic *)
  | Bytes

type const = 
  | Cunit 
  | Cbool of bool
  | Cint32 of int32
  | Clong of int64
  | Cstring of string

type uop = 
  | Onotbool 
  | Onotint
  | Oneg 
  | UOverloadTilde  (* internal temporary form from parser *)

type bop =
  | Oadd
  | Osub
  | Omul
  | Odiv
  | Omod
  | Oand
  | Oor
  | Oxor
  | Oshl
  | Oshr
  | Oeq 
  | One
  | Olt
  | Ogt 
  | Ole
  | Oge
  

type builtin = 
  | Uop of uop 
  | Bop of bop
  | Cast of typ
  | Ref
  | Deref 
  | Massgn

type dir = Up | Down

type pattern = 
  | Psome of string 
  | Pnone 
  | Pbytes of string * typ * (string * typ) list

(** The type of the abstract syntax tree (AST). *)
type expr =
  | Var of string
  | Const of const
  | App of expr * expr list
  | Prim of builtin * expr list
  | Let of string * typ * expr * expr
  | If of expr * expr * expr
  | For of expr * expr * dir * expr  
  | Sinit of string * string list * expr list  
  | Fget of expr * string
  | Ainit of string * expr list
  | Aaccess of string * int 
  | Match of expr * pattern list * expr list
  | Esome of expr 
  | Enone of typ

type fundecl =
  | Tfundecl of string * typ * effect list * (string * typ) list * (string * typ) list * expr

type toplevel =
  | Internal of fundecl * string option  (* section *)
  | EBPFInternal of fundecl * string option
  | StructDecl of string * (string * typ) list * string option
  | GlobalLet of string * typ * expr * string option  (* section *)


type program = toplevel list

let rec collect_vars (e : expr) : (string * typ) list =
  match e with
  | Var _ -> []
  | Const _ -> []
  | App (e1, args) ->
    (* Collect variables from the function and its arguments *)
    collect_vars e1 @ List.flatten (List.map collect_vars args)
  | Prim (_, args) ->
    (* Collect variables from the arguments of the primitive operation *) 
    List.flatten (List.map collect_vars args)
  | Let (id, ty, e1, e2) ->
      (* Collect variables from both subexpressions and prepend current binding *)
      (id, ty) :: (collect_vars e1 @ collect_vars e2)
  | If (e1, e2, e3) ->
      collect_vars e1 @ collect_vars e2 @ collect_vars e3
  | For (e1, e2, d, e3) ->
      collect_vars e1 @ collect_vars e2 @ collect_vars e3
  | Sinit (struct_name, fnames, exprs) ->
      List.flatten (List.map collect_vars exprs)
  | Fget (e, field_name) ->
      collect_vars e
  | Ainit (id, exprs) ->
      List.flatten (List.map collect_vars exprs)
  | Aaccess (arr_name, index) ->
      []  (* Array access does not introduce new variables *)
  | Match (e, patterns, exprs) ->
      collect_vars e @ List.flatten (List.map collect_vars exprs)
  | Esome e1 ->
      collect_vars e1
  | Enone t -> []
