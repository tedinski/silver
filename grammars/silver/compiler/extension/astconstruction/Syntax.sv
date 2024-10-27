grammar silver:compiler:extension:astconstruction;

imports silver:langutil:pp;

imports silver:compiler:definition:core;
imports silver:compiler:definition:env;
imports silver:compiler:definition:type:syntax;
imports silver:compiler:modification:list;
imports silver:compiler:extension:patternmatching;

exports silver:langutil:reflect:concretesyntax;

concrete production quoteAST
top::Expr ::= 'AST' '{' ast::AST_c '}'
layout {silver:langutil:reflect:concretesyntax:WhiteSpace}
{
  top.unparse = s"AST {${ast.unparse}}";
  forwards to translate(reflect(ast.ast));
}

concrete production quoteASTPattern
top::Pattern ::= 'AST' '{' ast::AST_c '}'
layout {silver:langutil:reflect:concretesyntax:WhiteSpace}
{
  top.unparse = s"AST {${ast.unparse}}";
  forwards to translatePattern(reflect(ast.ast));
}

concrete production antiquoteAST_c
top::AST_c ::= '$' '{' e::Expr '}'
layout {silver:compiler:definition:core:WhiteSpace}
{
  top.unparse = s"$${${e.unparse}}";
  top.ast = antiquoteAST(^e);
  top.errors := [];
}

concrete production varAST_c
top::AST_c ::= n::QName_t
{
  top.unparse = n.lexeme;
  top.ast = antiquotePatternAST(varPattern(name(n.lexeme)));
  top.errors :=
    if indexOf(":", n.lexeme) != -1
    then [errFromOrigin(n, "Pattern variable name must be unqualified")]
    else [];
}

concrete production wildAST_c
top::AST_c ::= '_'
{
  top.unparse = "_";
  top.ast = antiquotePatternAST(wildcPattern('_'));
  top.errors := [];
}

abstract production antiquoteAST
top::AST ::= e::Expr
{
  top.translation =
    errorExpr([err(top.givenLocation, "${} should only occur inside AST { } expression")]);
  top.patternTranslation =
    errorPattern([err(top.givenLocation, "${} should only occur inside AST { } expression")]);
  forwards to error("forward shouldn't be needed here");
}

abstract production antiquotePatternAST
top::AST ::= p::Pattern
{
  top.translation =
    errorExpr([err(top.givenLocation, "Variable and wildcard patterns should only occur inside AST { } pattern")]);
  top.patternTranslation =
    errorPattern([err(top.givenLocation, "Variable and wildcard patterns should only occur inside AST { } pattern")]);
  forwards to error("forward shouldn't be needed here");
}
