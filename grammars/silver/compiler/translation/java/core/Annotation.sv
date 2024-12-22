grammar silver:compiler:translation:java:core;

aspect production annotationDcl
top::AGDcl ::= 'annotation' a::QName tl::BracketedOptTypeExprs '::' te::TypeExpr ';'
{
  local className :: String = "A" ++ a.name;

-- We report the trans type, despite the fact that the attribute may be parameterized!
-- It should be fine, though. If we're a tv, then it's 'Object' and anything
-- else will be a subtype...

  top.genFilesUnescapedUp := [a.name];
  top.genFiles := [(className ++ ".java", s"""

package ${makeName(top.grammarName)};

public interface ${className} {

	public ${te.typerep.transType} getAnno_${makeIdName(fName)}();

}
""")];
}

