grammar silver:compiler:extension:autoattr;

concrete production propagateOnNTListExcludingDcl_c
top::AGDcl ::= 'propagate' attrs::AttrNameList 'on' nts::NameList 'excluding' ps::ProdNameList ';'
{
  top.unparse = s"propagate ${attrs.unparse} on ${nts.unparse} excluding ${ps.unparse};";
  propagate env;
  
  top.errors <- ps.errors;
  forwards to propagateOnNTListDcl(@attrs, @nts, @ps);
}

concrete production propagateOnNTListDcl_c
top::AGDcl ::= 'propagate' attrs::AttrNameList 'on' nts::NameList ';'
{
  top.unparse = s"propagate ${attrs.unparse} on ${nts.unparse};";
  
  forwards to
    propagateOnNTListDcl(@attrs, @nts, prodNameListNil());
}

abstract production propagateOnNTListDcl
top::AGDcl ::= attrs::AttrNameList nts::NameList ps::ProdNameList
{
  top.unparse = s"propagate ${attrs.unparse} on ${nts.unparse} excluding ${ps.unparse};";
  
  forwards to
    case nts of
    | nameListOne(n) -> propagateOnOneNTDcl(@attrs, ^n, @ps)
    | nameListCons(n, _, rest) ->
      appendAGDcl(
        propagateOnOneNTDcl(@attrs, ^n, @ps),
        propagateOnNTListDcl(^attrs, ^rest, ^ps))
    end;
}

-- Note that this only propagates on all *known* non-forwarding productions.
-- Usually all non-forwarding productions are exported by the NT, but that isn't
-- always the case (see options and closed nonterminals.)
-- For such productions the attribute must still be explicitly propagated.
abstract production propagateOnOneNTDcl
top::AGDcl ::= attrs::AttrNameList nt::QName ps::ProdNameList
{
  top.unparse = s"propagate ${attrs.unparse} on ${nt.unparse} excluding ${ps.unparse};";
  propagate env;
  
  -- Ugh, workaround for circular dependency
  top.defs := [];
  top.occursDefs := [];
  top.refDefs := [];
  top.moduleNames := [];
  top.specDefs := [];
  
  local includedProds::[ValueDclInfo] =
    filter(
      \ d::ValueDclInfo -> !d.hasForward && !contains(d.fullName, ps.names),
      getKnownProds(nt.lookupType.fullName, top.env));
  nondecorated local dcl::AGDcl =
    foldr(
      appendAGDcl, emptyAGDcl(),
      map(propagateAspectDcl(_, ^attrs), includedProds));
  
  forwards to
    if !null(nt.lookupType.errors)
    then errorAGDcl(nt.lookupType.errors)
    else dcl;
}

abstract production propagateAspectDcl
top::AGDcl ::= d::ValueDclInfo attrs::AttrNameList
{
  top.errors :=
    if null(forward.errors)
    then []
    else [nested(
      getParsedOriginLocationOrFallback(top),
      s"In propagate of ${attrs.unparse} for production ${d.fullName}:",
      forward.errors)];
  
  forwards to
    aspectProductionDcl(
      'aspect', 'production', qName(d.fullName),
      aspectProductionSignature(
        aspectProductionLHSFull(
          name(d.namedSignature.outputElement.elementName),
          d.namedSignature.outputElement.elementDclType),
        '::=',
        foldr(
          aspectRHSElemCons(_, _),
          aspectRHSElemNil(),
          map(
            \ ie::NamedSignatureElement ->
              aspectRHSElemFull(
                ie.elementShared,
                name(ie.elementName),
                freshenType(ie.elementDclType, ie.typerep.freeVariables)),
            d.namedSignature.inputElements))),
      productionBody(
        '{',
        productionStmtsSnoc(
          productionStmtsNil(),
          propagateAttrList('propagate', @attrs, ';')),
        '}'));
}

concrete production propagateAttrList
top::ProductionStmt ::= 'propagate' ns::AttrNameList ';'
{
  top.unparse = s"propagate ${ns.unparse};";
  
  -- Forwards to productionStmtAppend of propagating the first element in ns
  -- and propagateAttrDcl containing the remaining names
  forwards to
    case ns of
    | attrNameListOne(ms, n) -> propagateOneAttr(^ms, ^n)
    | attrNameListCons(ms, n, _, rest) ->
      productionStmtAppend(
        propagateOneAttr(^ms, ^n),
        propagateAttrList($1, ^rest, $3))
    end;
}

abstract production propagateOneAttr
top::ProductionStmt ::= ms::MaybeShared attr::QName
{
  top.unparse = s"propagate ${ms.unparse}${attr.unparse};";
  propagate env;

  -- We make an exception to permit propagated equations in places that would otherwise be orphaned.
  -- Since this is the only possible equation permitted in these contexts, having duplicates will
  -- still yield a well-defined specification.
  -- TOOD: Filtering based on the error message is a bit of a hack. 
  -- With https://github.com/melt-umn/silver/issues/648 we could instead filter on an error code.
  top.errors :=
    filter(\ m::Message -> !startsWith("Orphaned equation:", m.message), forward.errors);
  
  -- Ugh, workaround for circular dependency
  top.defs := [];
  top.productionAttributes := [];
  forwards to
    if !null(attr.lookupAttribute.errors)
    then errorProductionStmt(attr.lookupAttribute.errors)
    else attr.lookupAttribute.dcl.propagateDispatcher(ms.isShared, attr);
}

dispatch Propagate = ProductionStmt ::= includeShared::Boolean @attr::QName;

abstract production propagateError implements Propagate
top::ProductionStmt ::= includeShared::Boolean @attr::QName
{
  forwards to
    errorProductionStmt(
      [errFromOrigin(attr, s"Attribute ${attr.name} cannot be propagated")]);
}

abstract production propagateImpl implements Propagate
top::ProductionStmt ::= includeShared::Boolean @attr::QName impl::ProductionStmt
{
  forwards to @impl;
}

tracked nonterminal AttrNameList with config, grammarName, unparse, errors, env;
propagate config, grammarName, env, errors on AttrNameList;

concrete production attrNameListOne
top::AttrNameList ::= ms::MaybeShared n::QName
{
  top.unparse = ms.unparse ++ n.unparse;
  top.errors <- n.lookupAttribute.errors;
}

concrete production attrNameListCons
top::AttrNameList ::= ms::MaybeShared h::QName ',' t::AttrNameList
{
  top.unparse = ms.unparse ++ h.unparse ++ ", " ++ t.unparse;
  top.errors <- h.lookupAttribute.errors;
}

tracked nonterminal ProdNameList with config, grammarName, env, unparse, names, errors;
propagate config, grammarName, env, errors on ProdNameList;

abstract production prodNameListNil
top::ProdNameList ::=
{
  top.unparse = "";
  top.names = [];
}

concrete production prodNameListOne
top::ProdNameList ::= n::QName
{
  top.unparse = n.unparse;
  top.names = [n.lookupValue.fullName];
  top.errors <- n.lookupValue.errors;
  top.errors <-
    if n.lookupValue.found
    then
      case n.lookupValue.dcl of
      | prodDcl(_, _, _) -> []
      | _ -> [errFromOrigin(n, n.name ++ " is not a production")]
      end
    else [];
}

concrete production prodNameListCons
top::ProdNameList ::= h::QName ',' t::ProdNameList
{
  top.unparse = h.unparse ++ ", " ++ t.unparse;
  top.names = [h.lookupValue.fullName] ++ t.names;
  top.errors <- h.lookupValue.errors;
  top.errors <-
    if h.lookupValue.found
    then
      case h.lookupValue.dcl of
      | prodDcl(_, _, _) -> []
      | _ -> [errFromOrigin(h, h.name ++ " is not a production")]
      end
    else [];
}
