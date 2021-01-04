grammar silver:reflect:util;

import silver:langutil;

function reflect
AST ::= x::a
{
  return error("Foreign function");
} foreign {
  "java" : return "(common.Reflection.reflect((originCtx!=null)?originCtx.rulesAsSilverList():null, %x%))";
}

function reflectTypeName
Maybe<String> ::= x::a
{
  return error("Foreign function");
} foreign {
  "java" : return "(common.Reflection.reflectTypeName(%x%))";
}

function nativeToString
String ::= x::a
{
  return error("Foreign function");
} foreign {
  "java" : return "(new common.StringCatter(%x%.toString()))";
}

function applyAST
Either<String AST> ::= fn::AST args::[Maybe<AST>] namedArgs::[Pair<String Maybe<AST>>]
{
  return error("Foreign function");
} foreign {
  "java" : return "(common.Reflection.applyAST(originCtx, %fn%, %args%, %namedArgs%))";
}
