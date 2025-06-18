%{
open Beepl_ast
%}

%token <string> IDENT
%token <int32> INT32
%token <int64> INT64
%token <bool> BOOL
%token BOOLTYPE INT32TYPE LONGTYPE
%token TRUE FALSE UNIT
%token FUNC LET IN IF THEN ELSE
%token LPAREN RPAREN COLON COMMA EQ
%token LBRACE RBRACE
%token IO
%token EOF

%start <Beepl_ast.program> prog

%%

prog:
  | f = fundecl EOF { [Internal f] }

fundecl:
  | FUNC id = IDENT LPAREN args = separated_list(COMMA, arg) RPAREN
    COLON ret = typ COMMA IO LBRACE body = expr RBRACE
    {
      (* variable declarations left empty, is_ebpf = false *)
      Tfundecl(id, ret, Io, args, [], body, false)
    }

arg:
  | t = typ id = IDENT { (id, t) }

typ:
  | BOOLTYPE  { Vtype Tbool }
  | INT32TYPE { Vtype Tint32 }
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
