/*menhir --ocamlc "ocamlc -g" --explain bparser/parser.mly*/
%{
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
%}

%token <Int.int> INT
%token <Int64.int> INT64
%token <string> IDENT
%token <coq_Z> COQZ
%token PANIC DIVERGENCE READ WRITE ALLOC HSTATE
%token I8 I16 I32 IBOOL SIGNED UNSIGNED
%token TUNIT TBOOL TINT TLONG
%token ATTR_VOLATILE ATTR_ALIGNAS
%token TRUE FALSE

%token DOT COLON COMMA SEMICOLON ARROW LPAREN RPAREN LBRACK RBRACK LBRACE RBRACE
%token EOF

%token DEFS_FIELD PUBLIC_FIELD MAIN_FIELD TYPES_FIELD COMPENV_FIELD

%token PTYPE REFTYPE FTYPE STYPE OTYPE

%token MEMBER_PLAIN MEMBER_BITFIELD BCOMPOSITE
%token CO_SU CO_MEMBERS CO_ATTR CO_SIZEOF CO_ALIGNOF CO_RANK
%token STRUCT UNION

%token REF DEREF MASSGN UOP BOP RUN
%token PNONE PSOME 
%token ONOTBOOL ONOTINT ONEG OABSFLOAT 
%token OADD OSUB OMUL ODIV OMOD OAND OOR OXOR OSHL OSHR OEQ ONE OLT OGT  OLE OGE

%token <bool> CONSBOOL
%token <int> CONSINT
%token <Int64.int> CONSLONG
%token CONSUNIT
%token UP
%token DOWN
%token VUNIT
%token <bool>VBOOL
%token <int>VINT
%token <Int64.int> VLONG
%token <BinNums.positive> POSITIVE
%token <Ctypes.bitfield> BITFIELD
%token <positive,int> VLOC

%token LNAME LBITFIELD 

/* token for expr */
%token VAL VAR CONST APP PRIM BIND COND UNIT ADDR HEXPR EAPP SFIELD 
%token FOR ENONE ESOME MATCH
%token BSIG_ARGS BSIG_EF BSIG_RES BSIG_CC EF_EXTERNAL

/* token for function decl */
%token FN_RETURN FN_EFFECT FN_CALLCONV FN_ARGS FN_VARS FN_BODY
%token INTERNAL EXTERNAL

/* token for program */
%token PROG_DEFS PROG_PUBLIC PROG_MAIN PROG_COMPENV PROG_IDENT_TO_STRING

/* Specify types */
%type <BeePL.program> program_content
%type <BeeTypes.effect_label> effect_label
%type <BeeTypes.effect> effect
%type <Ctypes.insize> intsize
%type <Ctypes.signedness> signedness
%type <BeeTypes.primitive_type> primitive_type
%type <BeeTypes.basic_type> basic_type
%type <BeeTypes.coq_type> coq_type
%type <BeeTypes.coq_type_list> coq_type_list
%type <BeeTypes.bmember> bmember
%type <BeeTypes.bcomposite> bcomposite
%type <BeeTypes.bcomposite_definition> bcomposite_definition
%type <Ctypes> struct_or_union
%type <BeePL.builtin> builtin
%type <Cop.unary_operation> unary_operation
%type <Cop.binary_operation> binary_operation
%type <BeePL_values.constant> constant
%type <BeePL_values.dir> dir
%type <BeePL_values.value> value
%type <BeePL_values.linfo> linfo
%type <BeePL.bsignature> bsignature
%type <BeePL.external_function> external_function
%type <BeePL.coq_function> coq_function
%type <BeePL.fundef> fundef
%type <AST.calling_convention> CALLING_CONVENTION

/* Start symbol */
%start <BeePL.program> program

%%

program:
  program_content EOF { $1 }

program_content:
  LBRACE
    DEFS_FIELD SEMICOLON
    PUBLIC_FIELD SEMICOLON
    MAIN_FIELD SEMICOLON
    TYPES_FIELD SEMICOLON
    COMPENV_FIELD
  RBRACE
  {
    {
      prog_defs = $2;
      prog_public = $4;
      prog_main = $6;
      prog_types = $8;
      prog_comp_env = $10;
    }
  }

effect_label:
  | PANIC { Panic }
  | DIVERGENCE { Divergence }
  | READ IDENT { Read $2 }
  | WRITE IDENT { Write $2 }
  | ALLOC IDENT { Alloc $2 }
  | HSTATE IDENT { Hstate $2 }

effect:
  | effect_label {$1}
  | effect_label COMMA effect {$1 :: $3}

primitive_type:
  | TUNIT { Tunit }
  | TBOOL { Tbool }
  | TINT LPAREN intsize COMMA signedness COMMA attr RPAREN { Tint ($3, $5, $7) }
  | TLONG LPAREN signedness COMMA attr RPAREN { Tlong ($3, $5) }

intsize:
  | I8 { I8 }
  | I16 { I16 }
  | I32 { I32 }
  | IBOOL { IBOOL }

signedness:
  | SIGNED { Signed }
  | UNSIGNED { Unsigned }

attr:
  LBRACE
    ATTR_VOLATILE SEMICOLON
    ATTR_ALIGNAS 
  RBRACE
  {
    {
      attr_volatile = $2;
      attr_alignas = $4;
    }
  }

  basic_type:
  | primitive_type { $1 }

  coq_type:
  | PTYPE LPAREN primitive_type RPAREN {Ptype ($3)}
  | REFTYPE LPAREN IDENT COMMA basic_type COMMA attr RPAREN {Rtype ($3, $5, $7)}
  | FTYPE LPAREN list_coq_type COMMA effect COMMA list_coq_type RPAREN {Ftype ($3, $5, $7)}
  | STYPE LPAREN IDENT COMMA attr RPAREN {Stype ($3, $5)}
  | OTYPE coq_type {Otype $2}

list_coq_type:
  | LBRACK coq_type_list RBRACK { $2 }

coq_type_list:
  | coq_type                           { [$1] }
  | coq_type COMMA coq_type_list       { $1 :: $3 }

bmember:
  | MEMBER_PLAIN LPAREN IDENT COMMA coq_type RPAREN {Bmember_plain ($3, $5)}
  | MEMBER_BITFIELD LPAREN IDENT COMMA intsize COMMA signedness COMMA attr COMMA COQZ RPAREN {Bmember_bitfield ($3, $5, $7, $9, $11)}

list_bmemeber: 
  | LBRACK bmember_list RBRACK {$2}

bmember_list:
  | bmember                           { [$1] }
  | bmember COMMA bmember_list       { $1 :: $3 }

bcomposite:
  LBRACE
    CO_SU SEMICOLON CO_MEMBERS SEMICOLON CO_ATTR 
    SEMICOLON CO_SIZEOF SEMICOLON CO_ALIGNOF SEMICOLON CO_RANK
  RBRACE
  {
    {
      co_su = $2;
      co_members = $4;
      co_attr = $6;
      co_sizeof = $8;
      co_alignof = $10;
      co_rank = $12;
    }
  }

struct_or_union:
  | STRUCT { Struct }
  | UNION { Union }


bcomposite_definition:
  | BCOMPOSITE LBRACE IDENT COMMA struct_or_union COMMA bmember_list COMMA attr RBRACE
      { Bcomposite($3, $5, $7, $9) }

bcomposite_definition_list:
  | bcomposite_definition { [$1] }
  | bcomposite_definition COMMA bcomposite_definition_list { $1 :: $3 }

/*** Languge ***/
unary_operation: 
  | ONOTBOOL { Onotbool}
  | ONOTINT { Onotint }
  | ONEG { Oneg }
  | OABSFLOAT { Oabsfloat }

binary_operation:
  | OADD { Oadd }
  | OSUB { Osub }
  | OMUL { Omul }
  | ODIV { Odiv }
  | OMOD { Omod }
  | OAND { Oand }
  | OOR { Oor }
  | OXOR { Oxor }
  | OSHL { Oshl }
  | OSHR { Oshr }
  | OEQ { Oeq }
  | ONE { One }
  | OLT { Olt }
  | OGT { Ogt }
  | OLE { Ole }
  | OGE { Oge }

builtin:
  | REF { Ref }
  | DEREF { Deref }  
  | MASSGN { Massgn }
  | UOP unary_operation { Uop $2}
  | BOP binary_operation { Bop $2 }
  | RUN { Run }

pattern:
  | PNONE { Pnone }
  | PSOME IDENT { Psome $2 }

value:
  | VUNIT { Vunit }
  | VBOOL LPAREN TRUE RPAREN { Vbool $3 }
  | VBOOL LPAREN FALSE RPAREN { Vbool $3 }
  | VINT LPAREN INT RPAREN { Vint $3 }
  | VLONG LPAREN INT64 RPAREN { Vint64 $3 }
  | VLOC LPAREN POSITIVE COMMA INT RPAREN { Vloc ($3, $5) }

constant:
  | CONSBOOL TRUE { ConsBool $2 }
  | CONSBOOL FALSE { ConsBool $2 }
  | CONSINT INT { ConsInt $2 }
  | CONSLONG INT64 { ConsLong $2 }
  | CONSUNIT { ConsUnit }

dir:
  | UP { Up }
  | DOWN { Down }

linfo:
  LBRACE
    LNAME SEMICOLON
    LBITFIELD 
  RBRACE
  {
    {
      lname = $2;
      lbitfield = $4;
    }
  }

  bsignature:
    LBRACE
      BSIG_ARGS SEMICOLON
      BSIG_EF SEMICOLON
      BSIG_RES SEMICOLON
      BSIG_CC
    RBRACE
    {
      {
        bsig_args = $2;
        bsig_ef = $4;
        bsig_res = $6;
        bsig_cc = $8;
      }
    }

  external_function:
    | EF_EXTERNAL LPAREN IDENT COMMA bsignature RPAREN { EF_external ($2, $4) }
  


  expr:
    | VAL LPAREN value COMMA coq_type RPAREN { Val ($3, $5) }
    | VAR LPAREN IDENT COMMA coq_type RPAREN { Var ($3, $5) }
    | CONST LPAREN constant COMMA coq_type RPAREN { Const ($3, $5) }
    | APP LPAREN expr COMMA expr_list COMMA coq_type RPAREN { App ($3, $5, $7) }
    | PRIM LPAREN builtin COMMA expr_list COMMA coq_type RPAREN { Prim ($3, $5, $7) }
    | BIND LPAREN IDENT COMMA coq_type COMMA expr COMMA expr COMMA coq_type RPAREN { Bind ($3, $5, $7, $9, $11) }
    | COND LPAREN expr COMMA expr COMMA expr COMMA coq_type RPAREN { Cond ($3, $5, $7, $9) }
    | UNIT LPAREN coq_type RPAREN { Unit $3 }
    | ADDR LPAREN linfo COMMA INT COMMA coq_type RPAREN { Addr ($3, $5, $7) }
    | EAPP LPAREN external_function COMMA coq_type_list COMMA expr_list COMMA coq_type RPAREN { Eapp ($3, $5, $7, $9) }  
    | SFIELD LPAREN expr COMMA IDENT COMMA coq_type RPAREN { Sfield ($3, $5, $7) }
    | FOR LPAREN IDENT COMMA expr COMMA expr COMMA dir COMMA expr COMMA coq_type RPAREN { For ($3, $5, $7, $9, $11) }
    | ENONE LPAREN coq_type RPAREN { Enone $3 }
    | ESOME LPAREN expr COMMA coq_type RPAREN { Esome ($3, $5) }
    | MATCH LPAREN expr COMMA pattern COMMA expr_list COMMA coq_type RPAREN { Match ($3, $5, $7, $9) }

  expr_list:
  | expr { [$1] }
  | expr COMMA expr_list { $1 :: $3 }

  coq_function:
    LBRACE
      FN_RETURN SEMICOLON
      FN_EFFECT SEMICOLON
      FN_CALLCONV SEMICOLON
      FN_ARGS SEMICOLON
      FN_VARS SEMICOLON
      FN_BODY
    RBRACE
    {
      {
        fn_return = $2;
        fn_effect = $4;
        fn_callconv = $6;
        fn_args = $8;
        fn_vars = $10;
        fn_body = $12;
      }
    }

    fundef:
    | INTERNAL LPAREN coq_function RPAREN { Internal ($3) }
    | EXTERNAL LPAREN external_function COMMA coq_type_list COMMA coq_type COMMA CALLING_CONVENTION RPAREN { External ($3,$5, $7, $9) }

    program:
      LBRACE
        PROG_DEFS SEMICOLON
        PROG_PUBLIC SEMICOLON
        PROG_MAIN SEMICOLON
        PROG_COMPENV SEMICOLON
        PROG_IDENT_TO_STRING
      RBRACE
      {
        {
          prog_defs = $2;
          prog_public = $4;
          prog_main = $6;
          prog_comp_env = $8;
          prog_ident_to_string = $10;
        }
      }