grammar silver:compiler:definition:concrete_syntax;

monoid attribute syntaxAst :: [SyntaxDcl];
monoid attribute parserSpecs :: [ParserSpec];

attribute syntaxAst, parserSpecs occurs on File, AGDcls, AGDcl;
flowtype syntaxAst {decorate} on File, AGDcls, AGDcl;
flowtype parserSpecs {decorate} on File, AGDcls, AGDcl;
propagate syntaxAst, parserSpecs on File, AGDcls;

aspect default production
top::AGDcl ::=
{
  propagate syntaxAst, parserSpecs;
}

aspect production appendAGDcl
top::AGDcl ::= ag1::AGDcl ag2::AGDcl
{
  propagate syntaxAst, parserSpecs;
}
