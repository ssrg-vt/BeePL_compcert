
module MenhirBasics = struct
  
  exception Error
  
  let _eRR =
    fun _s ->
      raise Error
  
  type token = 
    | WRITE
    | VUNIT
    | VLONG of (
# 52 "bparser/parser.mly"
       (Int64.int)
# 17 "bparser/parser.ml"
  )
    | VLOC of (
# 55 "bparser/parser.mly"
       (positive,int)
# 22 "bparser/parser.ml"
  )
    | VINT of (
# 51 "bparser/parser.mly"
       (int)
# 27 "bparser/parser.ml"
  )
    | VBOOL of (
# 50 "bparser/parser.mly"
       (bool)
# 32 "bparser/parser.ml"
  )
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
    | POSITIVE of (
# 53 "bparser/parser.mly"
       (BinNums.positive)
# 66 "bparser/parser.ml"
  )
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
    | INT64 of (
# 18 "bparser/parser.mly"
       (Int64.int)
# 104 "bparser/parser.ml"
  )
    | INT of (
# 17 "bparser/parser.mly"
       (Int.int)
# 109 "bparser/parser.ml"
  )
    | IDENT of (
# 19 "bparser/parser.mly"
       (string)
# 114 "bparser/parser.ml"
  )
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
    | COQZ of (
# 20 "bparser/parser.mly"
       (coq_Z)
# 144 "bparser/parser.ml"
  )
    | CONSUNIT
    | CONST
    | CONSLONG of (
# 45 "bparser/parser.mly"
       (Int64.int)
# 151 "bparser/parser.ml"
  )
    | CONSINT of (
# 44 "bparser/parser.mly"
       (int)
# 156 "bparser/parser.ml"
  )
    | CONSBOOL of (
# 43 "bparser/parser.mly"
       (bool)
# 161 "bparser/parser.ml"
  )
    | COND
    | COMPENV_FIELD
    | COMMA
    | COLON
    | BSIG_RES
    | BSIG_EF
    | BSIG_CC
    | BSIG_ARGS
    | BOP
    | BITFIELD of (
# 54 "bparser/parser.mly"
       (Ctypes.bitfield)
# 175 "bparser/parser.ml"
  )
    | BIND
    | BCOMPOSITE
    | ATTR_VOLATILE
    | ATTR_ALIGNAS
    | ARROW
    | APP
    | ALLOC
    | ADDR
  
end

include MenhirBasics

# 2 "bparser/parser.mly"
  
open BeePL
open BeeTypes
open Ctypes
open Camlcoq
open BeePL_values
open Integers
open AST
open BinInt
open BinNums
open Ctypes
open Datatypes
open Integers

# 205 "bparser/parser.ml"

type ('s, 'r) _menhir_state

and _menhir_box_program = 
  | MenhirBox_program of (
# 90 "bparser/parser.mly"
       (BeePL.program)
# 213 "bparser/parser.ml"
) [@@unboxed]

let _menhir_action_1 =
  fun _1 ->
    (
# 95 "bparser/parser.mly"
                      ( _1 )
# 221 "bparser/parser.ml"
     : (
# 90 "bparser/parser.mly"
       (BeePL.program)
# 225 "bparser/parser.ml"
    ))

let _menhir_action_2 =
  fun _10 _2 _4 _6 _8 ->
    (
# 105 "bparser/parser.mly"
  (
    {
      prog_defs = _2;
      prog_public = _4;
      prog_main = _6;
      prog_types = _8;
      prog_comp_env = _10;
    }
  )
# 241 "bparser/parser.ml"
     : (
# 66 "bparser/parser.mly"
      (BeePL.program)
# 245 "bparser/parser.ml"
    ))

let _menhir_print_token : token -> string =
  fun _tok ->
    match _tok with
    | ADDR ->
        "ADDR"
    | ALLOC ->
        "ALLOC"
    | APP ->
        "APP"
    | ARROW ->
        "ARROW"
    | ATTR_ALIGNAS ->
        "ATTR_ALIGNAS"
    | ATTR_VOLATILE ->
        "ATTR_VOLATILE"
    | BCOMPOSITE ->
        "BCOMPOSITE"
    | BIND ->
        "BIND"
    | BITFIELD _ ->
        "BITFIELD"
    | BOP ->
        "BOP"
    | BSIG_ARGS ->
        "BSIG_ARGS"
    | BSIG_CC ->
        "BSIG_CC"
    | BSIG_EF ->
        "BSIG_EF"
    | BSIG_RES ->
        "BSIG_RES"
    | COLON ->
        "COLON"
    | COMMA ->
        "COMMA"
    | COMPENV_FIELD ->
        "COMPENV_FIELD"
    | COND ->
        "COND"
    | CONSBOOL _ ->
        "CONSBOOL"
    | CONSINT _ ->
        "CONSINT"
    | CONSLONG _ ->
        "CONSLONG"
    | CONST ->
        "CONST"
    | CONSUNIT ->
        "CONSUNIT"
    | COQZ _ ->
        "COQZ"
    | CO_ALIGNOF ->
        "CO_ALIGNOF"
    | CO_ATTR ->
        "CO_ATTR"
    | CO_MEMBERS ->
        "CO_MEMBERS"
    | CO_RANK ->
        "CO_RANK"
    | CO_SIZEOF ->
        "CO_SIZEOF"
    | CO_SU ->
        "CO_SU"
    | DEFS_FIELD ->
        "DEFS_FIELD"
    | DEREF ->
        "DEREF"
    | DIVERGENCE ->
        "DIVERGENCE"
    | DOT ->
        "DOT"
    | DOWN ->
        "DOWN"
    | EAPP ->
        "EAPP"
    | EF_EXTERNAL ->
        "EF_EXTERNAL"
    | ENONE ->
        "ENONE"
    | EOF ->
        "EOF"
    | ESOME ->
        "ESOME"
    | FALSE ->
        "FALSE"
    | FOR ->
        "FOR"
    | FTYPE ->
        "FTYPE"
    | HEXPR ->
        "HEXPR"
    | HSTATE ->
        "HSTATE"
    | I16 ->
        "I16"
    | I32 ->
        "I32"
    | I8 ->
        "I8"
    | IBOOL ->
        "IBOOL"
    | IDENT _ ->
        "IDENT"
    | INT _ ->
        "INT"
    | INT64 _ ->
        "INT64"
    | LBITFIELD ->
        "LBITFIELD"
    | LBRACE ->
        "LBRACE"
    | LBRACK ->
        "LBRACK"
    | LNAME ->
        "LNAME"
    | LPAREN ->
        "LPAREN"
    | MAIN_FIELD ->
        "MAIN_FIELD"
    | MASSGN ->
        "MASSGN"
    | MATCH ->
        "MATCH"
    | MEMBER_BITFIELD ->
        "MEMBER_BITFIELD"
    | MEMBER_PLAIN ->
        "MEMBER_PLAIN"
    | OABSFLOAT ->
        "OABSFLOAT"
    | OADD ->
        "OADD"
    | OAND ->
        "OAND"
    | ODIV ->
        "ODIV"
    | OEQ ->
        "OEQ"
    | OGE ->
        "OGE"
    | OGT ->
        "OGT"
    | OLE ->
        "OLE"
    | OLT ->
        "OLT"
    | OMOD ->
        "OMOD"
    | OMUL ->
        "OMUL"
    | ONE ->
        "ONE"
    | ONEG ->
        "ONEG"
    | ONOTBOOL ->
        "ONOTBOOL"
    | ONOTINT ->
        "ONOTINT"
    | OOR ->
        "OOR"
    | OSHL ->
        "OSHL"
    | OSHR ->
        "OSHR"
    | OSUB ->
        "OSUB"
    | OTYPE ->
        "OTYPE"
    | OXOR ->
        "OXOR"
    | PANIC ->
        "PANIC"
    | PNONE ->
        "PNONE"
    | POSITIVE _ ->
        "POSITIVE"
    | PRIM ->
        "PRIM"
    | PSOME ->
        "PSOME"
    | PTYPE ->
        "PTYPE"
    | PUBLIC_FIELD ->
        "PUBLIC_FIELD"
    | RBRACE ->
        "RBRACE"
    | RBRACK ->
        "RBRACK"
    | READ ->
        "READ"
    | REF ->
        "REF"
    | REFTYPE ->
        "REFTYPE"
    | RPAREN ->
        "RPAREN"
    | RUN ->
        "RUN"
    | SEMICOLON ->
        "SEMICOLON"
    | SFIELD ->
        "SFIELD"
    | SIGNED ->
        "SIGNED"
    | STRUCT ->
        "STRUCT"
    | STYPE ->
        "STYPE"
    | TBOOL ->
        "TBOOL"
    | TINT ->
        "TINT"
    | TLONG ->
        "TLONG"
    | TRUE ->
        "TRUE"
    | TUNIT ->
        "TUNIT"
    | TYPES_FIELD ->
        "TYPES_FIELD"
    | UNION ->
        "UNION"
    | UNIT ->
        "UNIT"
    | UNSIGNED ->
        "UNSIGNED"
    | UOP ->
        "UOP"
    | UP ->
        "UP"
    | VAL ->
        "VAL"
    | VAR ->
        "VAR"
    | VBOOL _ ->
        "VBOOL"
    | VINT _ ->
        "VINT"
    | VLOC _ ->
        "VLOC"
    | VLONG _ ->
        "VLONG"
    | VUNIT ->
        "VUNIT"
    | WRITE ->
        "WRITE"

let _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

include struct
  
  [@@@ocaml.warning "-4-37"]
  
  let _menhir_run_00 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | DEFS_FIELD ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | SEMICOLON ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  (match (_tok : MenhirBasics.token) with
                  | PUBLIC_FIELD ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      (match (_tok : MenhirBasics.token) with
                      | SEMICOLON ->
                          let _tok = _menhir_lexer _menhir_lexbuf in
                          (match (_tok : MenhirBasics.token) with
                          | MAIN_FIELD ->
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              (match (_tok : MenhirBasics.token) with
                              | SEMICOLON ->
                                  let _tok = _menhir_lexer _menhir_lexbuf in
                                  (match (_tok : MenhirBasics.token) with
                                  | TYPES_FIELD ->
                                      let _tok = _menhir_lexer _menhir_lexbuf in
                                      (match (_tok : MenhirBasics.token) with
                                      | SEMICOLON ->
                                          let _tok = _menhir_lexer _menhir_lexbuf in
                                          (match (_tok : MenhirBasics.token) with
                                          | COMPENV_FIELD ->
                                              let _tok = _menhir_lexer _menhir_lexbuf in
                                              (match (_tok : MenhirBasics.token) with
                                              | RBRACE ->
                                                  let _tok = _menhir_lexer _menhir_lexbuf in
                                                  let (_10, _8, _6, _4, _2) = ((), (), (), (), ()) in
                                                  let _v = _menhir_action_2 _10 _2 _4 _6 _8 in
                                                  (match (_tok : MenhirBasics.token) with
                                                  | EOF ->
                                                      let _1 = _v in
                                                      let _v = _menhir_action_1 _1 in
                                                      MenhirBox_program _v
                                                  | _ ->
                                                      _eRR ())
                                              | _ ->
                                                  _eRR ())
                                          | _ ->
                                              _eRR ())
                                      | _ ->
                                          _eRR ())
                                  | _ ->
                                      _eRR ())
                              | _ ->
                                  _eRR ())
                          | _ ->
                              _eRR ())
                      | _ ->
                          _eRR ())
                  | _ ->
                      _eRR ())
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
end

let program =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_program v = _menhir_run_00 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
