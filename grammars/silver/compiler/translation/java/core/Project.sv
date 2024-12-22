grammar silver:compiler:translation:java:core;

imports silver:compiler:translation:java:type;

imports silver:compiler:definition:core;
imports silver:compiler:definition:type:syntax;

imports silver:compiler:definition:env;
imports silver:compiler:definition:type;
imports silver:compiler:definition:flow:env;
imports silver:compiler:definition:flow:ast;

imports silver:compiler:analysis:uniqueness;
imports silver:compiler:analysis:typechecking:core only finalType;

fun makeName String ::= str::String = substitute(":", ".", str);
fun makeIdName String ::= str::String = substitute(":", "_", str);

fun makeProdName String ::= s::String genFilesUnescapedDown::[String] =
  substituteLast(".", ".P", makeName(s), genFilesUnescapedDown);

fun makeNTName String ::= s::String genFilesUnescapedDown::[String] =
  substituteLast(".", ".N", makeName(s), genFilesUnescapedDown);

fun makeAnnoName String ::= s::String genFilesUnescapedDown::[String] =
  substituteLast(".", ".A", makeName(s), genFilesUnescapedDown);

fun makeTerminalName String ::= s::String genFilesUnescapedDown::[String] =
  substituteLast(".", ".T", makeName(s), genFilesUnescapedDown);

fun makeParserName String ::= s::String = "Parser_" ++ makeIdName(s);

fun makeClassName String ::= s::String genFilesUnescapedDown::[String] =
  substituteLast(".", ".C", makeName(s), genFilesUnescapedDown);

fun makeInstanceName String ::= g::String s::String t::Type genFilesUnescapedDown::[String] =
  substituteLast(".", ".I", makeName(g ++ ":" ++ substitute(":", "_", s))) ++ "_" ++ transTypeName(t);

function substituteLast
String ::= r::String s::String str::String genFilesUnescapedDown::[String]
{
  local attribute i::Integer;
  i = lastIndexOf(r, str);
  
  return if i == -1 then str
         else substring(0,i,str) ++ s ++
              escapeName(substring(i+length(r), length(str), str),
                         genFilesUnescapedDown);
}

-- Escapes a name, to avoid collisions on case-insensitive filesystems.
fun escapeName String ::= str::String genFilesUnescapedDown::[String] =
  case length(filter(eq(toLowerCase(str), _), genFilesUnescapedDown)) of
  | 0 -> error(s"missing genFilesUnescapedUp equation for ${str}")
  | 1 -> str
  | _ -> implode("", map(escapeChar, explode("", str)))
  end;
fun escapeChar String ::= ch::String =
  if isUpper(ch) || ch == "_" then "_" ++ ch else ch;
