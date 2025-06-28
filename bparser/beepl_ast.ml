type effect = 
  | Divergence 
  | Read of string 
  | Write of string 
  | Alloc of string 
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
  | Reftype of string * btype

type typ = 
  | Utype
  | Vtype of ptype 
  | Ptr of ptrtype
  | Ftype of typ list * effect list * typ

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

type builtin = 
  | Uop of uop 

(** The type of the abstract syntax tree (AST). *)
type expr =
  | Var of string
  | Const of const
  | App of expr * expr list
  | Prim of builtin * expr list
  | Let of string * typ * expr * expr
  | If of expr * expr * expr

type fundecl =
  | Tfundecl of string * typ * effect list * (string * typ) list * (string * typ) list * expr

type toplevel =
  | Internal of fundecl * string option  (* section *)
  | EBPFInternal of fundecl * string option
  | StructDecl of string * (string * typ) list
  | GlobalLet of string * typ * expr


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

