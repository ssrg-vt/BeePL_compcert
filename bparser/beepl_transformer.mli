val parse_bpl_ast : string -> Beepl_ast.program

val transform_program : Beepl_ast.program -> BeePL.program

val parse_and_transform_bpl : string -> BeePL.program

val string_globals : (string, string) Hashtbl.t

val transform_expr : Beepl_ast_typechecker.efenv -> Beepl_ast_typechecker.Senv.t -> Beepl_ast_typechecker.tyenv -> Beepl_ast.expr -> BeePL.expr

