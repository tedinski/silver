grammar silver:langutil:reflect;

import silver:langutil:reflect:serialize only;  -- Include this in the silver.langutil artifact.

@{-
 - Use reflection to get the pp or unparse of an unknown term,
 - falling back to use the reflective pp.
 -}
function genericPP
Document ::= x::a
{
  nondecorated local typeNamePP::Document = text(fromMaybe("<OBJ>", reflectTypeName(x)));
  return
    fromRight(
      alt(
        map(\ pp::Document -> pp"${typeNamePP} { ${pp} }",
          getSynthesized(x, "silver:langutil:pp")),
        alt(
          map(\ pps::[Document] -> pp"${typeNamePP} [ ${ppImplode(pp", ", pps)} ]",
            getSynthesized(x, "silver:langutil:pps")),
          map(\ unparse::String -> pp"${typeNamePP} { ${text(unparse)} }",
            getSynthesized(x, "silver:langutil:unparse")))),
      reflect(x).pp);
}
