grammar silver:reflect;

function reflect
AST ::= x::a
{
  return error("Foreign function");
} foreign {
  "java" : return "(common.Reflection.reflect((originCtx!=null)?originCtx.rulesAsSilverList():null, %x%))";
}

function reify
runtimeTypeable a => Either<String a> ::= x::AST
{
  return error("Foreign function");
} foreign {
  "java" : return "common.Reflection.reifyChecked((originCtx!=null)?originCtx.rulesAsSilverList():null, %@0@%, (silver.core.NAST)%x%)";
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

fun reifyUnchecked runtimeTypeable a => a ::= x::AST =
  case reify(x) of
  | left(msg) -> error(msg)
  | right(a) -> a
  end;

-- TODO: We could add lazy versions of these, if needed.

@{-
 - Reflectively access an inherited attribute from a tree by name.
 - Note that this deeply forces the result if it is a term, and catches any errors thrown in evaluation.
 -}
function getInherited
runtimeTypeable a => Either<String a> ::= x::Decorated b with i  attr::String
{
  return error("Foreign function");
} foreign {
  "java" : return "common.Reflection.getInherited(%@0@%, %x%, %attr%.toString())";
}

@{-
 - Reflectively access a synthesized attribute from a tree by name.
 - Note that this deeply forces the result if it is a term, and catches any errors thrown in evaluation.
 -}
function getSynthesized
runtimeTypeable a => Either<String a> ::= x::b  attr::String
{
  return error("Foreign function");
} foreign {
  "java" : return "common.Reflection.getSynthesized(%@0@%, %x%, %attr%.toString())";
}

-- Textual serialization and deserialization is implemented in silver:langutil:reflect:serialize
-- to avoid a dependency on langutil here.

function serializeBytes
Either<String ByteArray> ::= x::a
{
  return error("Not impl");
} foreign {
  "java" : return "common.Reflection.nativeSerialize(%x%)";
}

function deserializeBytes
runtimeTypeable a => Either<String a> ::= x::ByteArray
{
  return error("Not impl");
} foreign {
  "java" : return "common.Reflection.nativeDeserialize(%@0@%, %x%)";
}
