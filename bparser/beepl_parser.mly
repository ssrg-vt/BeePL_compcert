%{
open Beepl_ast
%}

%token <string> IDENT
%token <int32> INT32
%token <int64> INT64
%token <bool> BOOL
%token INT8TYPE UINT8TYPE
%token INT16TYPE UINT16TYPE 
%token BOOLTYPE INT32TYPE UINT32TYPE ULONGTYPE LONGTYPE
%token TRUE FALSE UNIT
%token FUNC LET IN IF THEN ELSE HASHEBPF
%token LPAREN RPAREN COLON COMMA EQ
%token LBRACE RBRACE
%token IO DIVERGENCE READ WRITE ALLOC EMPTYBRACKETS
%token EOF

%start <Beepl_ast.program> prog

%%

prog:
  | f = fundecl EOF                { [Internal f] }
  | HASHEBPF f = fundecl EOF       { [EBPFInternal f] }

fundecl:
  | FUNC id = IDENT LPAREN args = separated_list(COMMA, arg) RPAREN
    COLON ret = typ COMMA effects = effect_list LBRACE body = expr RBRACE
    {
      Tfundecl(id, ret, effects, args, [], body)
    }

effect_list:
  | EMPTYBRACKETS { [] }
  | separated_nonempty_list(COMMA, effect) { $1 }

arg:
  | t = typ id = IDENT { (id, t) }

effect:
  | DIVERGENCE { Divergence }
  | READ id = IDENT { Read id }
  | WRITE id = IDENT { Write id }
  | ALLOC id = IDENT { Alloc id }
  | IO { Io }

typ:
  | BOOLTYPE  { Vtype Tbool }
  | UINT8TYPE { Vtype Tuint8 }
  | INT8TYPE  { Vtype Tint8 }
  | UINT16TYPE { Vtype Tuint16 }
  | INT16TYPE { Vtype Tint16 }
  | UINT32TYPE { Vtype Tuint32 }
  | INT32TYPE { Vtype Tint32 }
  | ULONGTYPE { Vtype Tulong }
  | LONGTYPE  { Vtype Tlong }
  | UNIT      { Utype }

const:
  | TRUE    { Cbool true }
  | FALSE   { Cbool false }
  | UNIT    { Cunit }
  | i = INT32 { Cint32 i }
  | l = INT64 { Clong l }

expr:
  | id = IDENT { Var id }
  | c = const  { Const c }
  | LET id = IDENT COLON t = typ EQ e1 = expr IN e2 = expr
    { Let(id, t, e1, e2) }
  | IF e1 = expr THEN e2 = expr ELSE e3 = expr
    { If(e1, e2, e3) }


