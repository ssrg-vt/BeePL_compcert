val parse_and_transform_bpl : string -> BeePL.program

val string_globals : (string, string) Hashtbl.t

val transform_expr : Beepl_ast_typechecker.tyenv -> Beepl_ast.expr -> BeePL.expr

