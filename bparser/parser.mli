
(* The type of tokens. *)

type token = 
  | WRITE
  | VUNIT
  | VLONG of (Int64.int)
  | VLOC of (positive,int)
  | VINT of (int)
  | VBOOL of (bool)
  | VAR
  | VAL
  | UP
  | UOP
  | UNSIGNED
  | UNIT
  | UNION
  | TYPES_FIELD
  | TUNIT
  | TRUE
  | TLONG
  | TINT
  | TBOOL
  | STYPE
  | STRUCT
  | SIGNED
  | SFIELD
  | SEMICOLON
  | RUN
  | RPAREN
  | REFTYPE
  | REF
  | READ
  | RBRACK
  | RBRACE
  | PUBLIC_FIELD
  | PTYPE
  | PSOME
  | PRIM
  | POSITIVE of (BinNums.positive)
  | PNONE
  | PANIC
  | OXOR
  | OTYPE
  | OSUB
  | OSHR
  | OSHL
  | OOR
  | ONOTINT
  | ONOTBOOL
  | ONEG
  | ONE
  | OMUL
  | OMOD
  | OLT
  | OLE
  | OGT
  | OGE
  | OEQ
  | ODIV
  | OAND
  | OADD
  | OABSFLOAT
  | MEMBER_PLAIN
  | MEMBER_BITFIELD
  | MATCH
  | MASSGN
  | MAIN_FIELD
  | LPAREN
  | LNAME
  | LBRACK
  | LBRACE
  | LBITFIELD
  | INT64 of (Int64.int)
  | INT of (Int.int)
  | IDENT of (string)
  | IBOOL
  | I8
  | I32
  | I16
  | HSTATE
  | HEXPR
  | FTYPE
  | FOR
  | FALSE
  | ESOME
  | EOF
  | ENONE
  | EF_EXTERNAL
  | EAPP
  | DOWN
  | DOT
  | DIVERGENCE
  | DEREF
  | DEFS_FIELD
  | CO_SU
  | CO_SIZEOF
  | CO_RANK
  | CO_MEMBERS
  | CO_ATTR
  | CO_ALIGNOF
  | COQZ of (coq_Z)
  | CONSUNIT
  | CONST
  | CONSLONG of (Int64.int)
  | CONSINT of (int)
  | CONSBOOL of (bool)
  | COND
  | COMPENV_FIELD
  | COMMA
  | COLON
  | BSIG_RES
  | BSIG_EF
  | BSIG_CC
  | BSIG_ARGS
  | BOP
  | BITFIELD of (Ctypes.bitfield)
  | BIND
  | BCOMPOSITE
  | ATTR_VOLATILE
  | ATTR_ALIGNAS
  | ARROW
  | APP
  | ALLOC
  | ADDR

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val program: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (BeePL.program)
