%{
open Ast
%}

/* Token declarations */
%token <string> IDENT
%token <string> INT32
%token LET FUNC IN REF
%token UNIT LPAREN RPAREN
%token EQUAL COLON ARROW BANG ASSIGN UNDERSCORE
%token EOF

/* Precedence and associativity */
%nonassoc IN
%right ASSIGN
%nonassoc BANG
%nonassoc REF
%right ARROW

/* Entry point */
%start <Ast.program> program

%%

program:
  | tl = list(toplevel) EOF { tl }
  ;

toplevel:
  | LET p = pattern t = option(type_annot) EQUAL e = expr
    { TLLet (p, t, e) }
  | FUNC name = IDENT params = list(param) ret_type = option(type_annot) EQUAL body = expr
    { TLFunc (name, params, ret_type, body) }
  | e = expr
    { TLExpr e }
  ;

param:
  | LPAREN name = IDENT t = option(type_annot) RPAREN
    { (name, t) }
  | UNIT
    { ("", None) }
  ;

pattern:
  | UNIT                        { PUnit }
  | UNDERSCORE
    { PWildcard }
  | id = IDENT
    { PIdent id }
  | LPAREN p = pattern t = type_annot RPAREN
    { PAnnot (p, t) }
  ;

type_annot:
  | COLON t = typ { t }
  ;

typ:
  | id = IDENT                 { TName id }
  | REF t = typ                { TRef t }
  | t  = typ  REF                 { TRef t }
  | t1 = typ ARROW t2 = typ
      {
        (match t2 with
         | TArrow (args, ret) -> TArrow (t1 :: args, ret)
         | _                  -> TArrow ([t1], t2))
      }
  | LPAREN t = typ RPAREN      { t }
;

expr:
  | LET p = pattern t = option(type_annot) EQUAL e1 = expr IN e2 = expr
    { ELet (p, t, e1, e2) }
  | e1 = expr ASSIGN e2 = expr
    { EAssign (e1, e2) }
  | e = app_expr
    { e }
  ;


app_expr:
  | e = simple_expr
    { e }
  | f = app_expr a = simple_expr
    { match f with
      | EApply (func, args) -> EApply (func, args @ [a])
      | _ -> EApply (f, [a])
    }
  ;

simple_expr:
  | UNIT                         { EUnit }
  | i = INT32                    { EInt32 i }
  | id = IDENT                   { EVar id }
  | BANG  e = simple_expr        { EDeref e }
  | REF   e = simple_expr        { ERef   e }
  | LPAREN e = expr RPAREN       { e }
;

%%
