grammar silver:langutil:reflect:serialize;

-- It is somewhat unfortunate that this grammar needs to live under silver:langutil,
-- due to the dependency on silver:langutil:reflect:concretesyntax.

imports silver:reflect;
imports silver:langutil;
imports silver:langutil:reflect:concretesyntax;
imports silver:langutil:pp;

fun serialize Either<String String> ::= x::a = reflect(x).serialize;

parser astParser :: AST_c {
  silver:langutil:reflect:concretesyntax;
}

function deserializeAST
Either<String AST> ::= fileName::String text::String
{
  local result::ParseResult<AST_c> = astParser(text, fileName);
  local parseTree::AST_c = result.parseTree;

  return
    if !result.parseSuccess
    then left(result.parseErrors)
    else if !null(parseTree.errors)
    then left(messagesToString(parseTree.errors))
    else right(parseTree.ast);
}

fun deserialize runtimeTypeable a => Either<String a> ::= fileName::String text::String =
  bind(deserializeAST(fileName, text), reify);
