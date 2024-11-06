grammar silver:compiler:definition:flow:ast;

{--
 - Represents a decision tree of potential decoration sites to determine if an inherited attribute
 - has been supplied for some vertex type.
 -}
nonterminal DecSiteTree with decSitePP, decSiteAlts, decSiteReqs, maxDepth, dbgPP;
flowtype DecSiteTree = decorate {}, forward {};

synthesized attribute decSitePP::String;
synthesized attribute decSiteAlts::[DecSiteTree];
synthesized attribute decSiteReqs::[DecSiteTree];

inherited attribute maxDepth::Integer;
synthesized attribute dbgPP::String;

aspect default production
top::DecSiteTree ::=
{
  top.decSiteAlts = [^top];
  top.decSiteReqs = [^top];
  top.dbgPP = top.decSitePP;
}

{--
 - No attributes can be known to be supplied.
 - Primarilly, denotes a cycle in decoration site resolution.
 -}
production neverDec
top::DecSiteTree ::= 
{
  top.decSitePP = "never";
  top.decSiteAlts = [];
}

{-
 - All attributes are known to be supplied.
 - Can occur if a dispatch signature has no implementing productions, or in the search reduction process.
 -}
production alwaysDec
top::DecSiteTree ::= 
{
  top.decSitePP = "always";
  top.decSiteReqs = [];
}

{--
 - An attribute can be supplied by either of these sites.
 -}
production altDec
top::DecSiteTree ::= d1::DecSiteTree d2::DecSiteTree
{
  top.decSitePP = implode(" | ", map((.decSitePP), top.decSiteAlts));
  top.decSiteAlts = d1.decSiteAlts ++ d2.decSiteAlts;
  top.dbgPP = if top.maxDepth > 0 then s"(${d1.dbgPP} | ${d2.dbgPP})" else "...";
  d1.maxDepth = top.maxDepth - 1;
  d2.maxDepth = top.maxDepth - 1;
}

{--
 - An attribute is present if it is supplied by both of these sites.
 -}
production bothDec
top::DecSiteTree ::= d1::DecSiteTree d2::DecSiteTree
{
  top.decSitePP = s"{${implode(", ", map((.decSitePP), top.decSiteReqs))}}";
  top.decSiteReqs = d1.decSiteReqs ++ d2.decSiteReqs;
  top.dbgPP = if top.maxDepth > 0 then s"(${d1.dbgPP} & ${d2.dbgPP})" else "...";
  d1.maxDepth = top.maxDepth - 1;
  d2.maxDepth = top.maxDepth - 1;
}

production viaProdVertexDec
top::DecSiteTree ::= prodName::String vt::VertexType d::DecSiteTree
{
  top.decSitePP = d.decSitePP;
  top.decSiteReqs = d.decSiteReqs;
  top.decSiteAlts = d.decSiteAlts;
  top.dbgPP = if top.maxDepth > 0 then s"via ${vt.vertexPP} of production ${prodName}: ${d.dbgPP}" else "...";
  d.maxDepth = top.maxDepth - 1;
}

production viaDispatchDec
top::DecSiteTree ::= dispatchSig::String sigName::String d::DecSiteTree
{
  top.decSitePP = d.decSitePP;
  top.decSiteReqs = d.decSiteReqs;
  top.decSiteAlts = d.decSiteAlts;
  top.dbgPP = if top.maxDepth > 0 then s"via child ${sigName} of dispatch ${dispatchSig}: ${d.dbgPP}" else "...";
  d.maxDepth = top.maxDepth - 1;
}

{--
 - An attribute can be supplied to a vertex type in some production.
 -}
production directDec
top::DecSiteTree ::= prodName::String vt::VertexType
{
  -- TODO: What if vt is an anonVertexType?
  top.decSitePP = s"${vt.vertexPP} of production ${prodName}";
}

{--
 - An attribute can be supplied via forwarding.
 - Inherited attributes on a translation attribute are only supplied if this is
 - the forward of the production (not a forward prod attr), and there is no
 - override equation for the translation attribute.
 -}
production forwardDec
top::DecSiteTree ::= prodName::String prodAttrName::Maybe<String>
{
  top.decSitePP =
    case prodAttrName of
    | just(attrName) -> s"via forward production attribute ${attrName} of production ${prodName}"
    | _ -> s"via forward of production ${prodName}"
    end;
}

{--
 - Decoration sites where some other attribute must be supplied as a dependency.
 -}
production depAttrDec
top::DecSiteTree ::= attrName::String d::DecSiteTree
{
  top.decSitePP = s"dependency ${attrName} supplied to ${d.decSitePP}";
  top.dbgPP = if top.maxDepth > 0 then s"dependency ${attrName} supplied to ${d.dbgPP}" else "...";
  d.maxDepth = top.maxDepth - 1;
}

{--
  - Supplying an inherited attribute via a flow projection requires the projected dependencies to be supplied.
  -}
production projectedDepsDec
top::DecSiteTree ::= prodName::String sigName::String d::DecSiteTree
{
  top.decSitePP = s"projected dependencies for ${sigName} in production ${prodName}: ${d.decSitePP}";
  top.dbgPP = if top.maxDepth > 0 then s"projected dependencies for ${sigName} in production ${prodName}: ${d.dbgPP}" else "...";
  d.maxDepth = top.maxDepth - 1;
}

{--
 - An inherited attribute on a translation attribute can be supplied via a translation attribute.
 -}
production transAttrDec
top::DecSiteTree ::= attrName::String d::DecSiteTree
{
  top.decSitePP = s"via translation attribute ${attrName}: ${d.decSitePP}";
  top.dbgPP = if top.maxDepth > 0 then s"via translation attribute ${attrName}: ${d.dbgPP}" else "...";
  d.maxDepth = top.maxDepth - 1;
}

fun prettyDecSites String ::= nest::Integer d::DecSiteTree =
  replicate(nest, "\t") ++
  if length(d.decSiteAlts) > 1
  then "any of\n" ++ implode("\n", map(prettyDecSites(nest + 1, _), d.decSiteAlts))
  else if length(d.decSiteReqs) > 1
  then "all of\n" ++ implode("\n", map(prettyDecSites(nest + 1, _), d.decSiteReqs))
  else
    case d of
    | depAttrDec(attrName, d) ->
        s"dependency ${attrName} supplied to" ++
        if length(d.decSiteAlts) > 1
        then " any of\n" ++ implode("\n", map(prettyDecSites(nest + 1, _), d.decSiteAlts))
        else if length(d.decSiteReqs) > 1
        then " all of\n" ++ implode("\n", map(prettyDecSites(nest + 1, _), d.decSiteReqs))
        else " " ++ prettyDecSites(nest, ^d)
    | _ -> d.decSitePP
    end;

derive Eq, Ord on DecSiteTree;

instance Semiring DecSiteTree {
  add = altDec;
  zero = neverDec();
  mul = bothDec;
  one = alwaysDec();
}
