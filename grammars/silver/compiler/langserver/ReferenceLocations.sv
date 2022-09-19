grammar silver:compiler:langserver;

monoid attribute valueRefLocs::[(Location, ValueDclInfo)];
monoid attribute typeRefLocs::[(Location, TypeDclInfo)];
monoid attribute attributeRefLocs::[(Location, AttributeDclInfo)];

attribute valueRefLocs, typeRefLocs, attributeRefLocs occurs on
  RootSpec, Grammar, Root, NameList, AGDcls, AGDcl,
  ProductionSignature, FunctionSignature, AspectProductionSignature, AspectFunctionSignature,
  ConstraintList, Constraint, ProductionLHS, FunctionLHS, AspectProductionLHS, AspectFunctionLHS,
  ProductionRHS, AspectRHS, ProductionRHSElem, AspectRHSElem,
  TypeExpr, Signature, SignatureLHS, TypeExprs, BracketedTypeExprs, BracketedOptTypeExprs,
  ProductionBody, ProductionStmts, ProductionStmt, DefLHS,
  ClassBody, ClassBodyItem, InstanceBody, InstanceBodyItem,
  Expr, Exprs, ExprInhs, ExprInh, ExprLHSExpr, AppExprs, AppExpr, AnnoAppExprs, AnnoExpr,
  PrimPatterns, PrimPattern, ProdNameList;

propagate valueRefLocs, typeRefLocs, attributeRefLocs on
  RootSpec, Grammar, Root, NameList, AGDcls, AGDcl,
  ProductionSignature, FunctionSignature, AspectProductionSignature, AspectFunctionSignature,
  ConstraintList, Constraint, ProductionLHS, FunctionLHS, AspectProductionLHS, AspectFunctionLHS,
  ProductionRHS, AspectRHS, ProductionRHSElem, AspectRHSElem,
  TypeExpr, Signature, SignatureLHS, TypeExprs, BracketedTypeExprs, BracketedOptTypeExprs,
  ProductionBody, ProductionStmts, ProductionStmt, DefLHS,
  ClassBody, ClassBodyItem, InstanceBody, InstanceBodyItem,
  Expr, Exprs, ExprInhs, ExprInh, ExprLHSExpr, AppExprs, AppExpr, AnnoAppExprs, AnnoExpr,
  PrimPatterns, PrimPattern, ProdNameList;

aspect valueRefLocs on NameList using <- of
| nameListCons(q, _, _) -> if q.lookupValue.found then [(q.location, q.lookupValue.dcl)] else []
| nameListOne(q) -> if q.lookupValue.found then [(q.location, q.lookupValue.dcl)] else []
end;

aspect typeRefLocs on NameList using <- of
| nameListCons(q, _, _) -> if q.lookupType.found then [(q.location, q.lookupType.dcl)] else []
| nameListOne(q) -> if q.lookupType.found then [(q.location, q.lookupType.dcl)] else []
end;

aspect attributeRefLocs on NameList using <- of
| nameListCons(q, _, _) -> if q.lookupAttribute.found then [(q.location, q.lookupAttribute.dcl)] else []
| nameListOne(q) -> if q.lookupAttribute.found then [(q.location, q.lookupAttribute.dcl)] else []
end;

attribute typeRefLocs occurs on QNameType;
aspect typeRefLocs on top::QNameType using := of
| _ -> if top.lookupType.found then [(top.location, top.lookupType.dcl)] else []
end;

attribute attributeRefLocs occurs on QNameAttrOccur;
aspect attributeRefLocs on top::QNameAttrOccur using := of
| qNameAttrOccur(at) -> if top.found then [(at.location, top.attrDcl)] else []
end;

aspect valueRefLocs on AGDcl using <- of
| aspectProductionDcl(_, _, q, _, _) -> if q.lookupValue.found then [(q.location, q.lookupValue.dcl)] else []
| aspectFunctionDcl(_, _, q, _, _) -> if q.lookupValue.found then [(q.location, q.lookupValue.dcl)] else []
end;

aspect valueRefLocs on AGDcl using := of
| propagateOnNTListDcl(_, _, ps) -> ps.valueRefLocs
  -- Exclude mempty/append declarations from forwarding
| tcMonoidAttributeDcl(_, _, _, _, _, te, _) -> te.valueRefLocs
| strategyAttributeDcl(_, _, _, _, e) -> e.valueRefLocs
end;

aspect typeRefLocs on AGDcl using <- of
| defaultAttributionDcl(_, _, nt, _) -> if nt.lookupType.found then [(nt.location, nt.lookupType.dcl)] else []
end;

aspect typeRefLocs on AGDcl using := of
| propagateOnNTListDcl(_, nts, _) -> nts.typeRefLocs
| strategyAttributeDcl(_, _, _, _, e) -> e.typeRefLocs
end;

aspect attributeRefLocs on AGDcl using <- of
| defaultAttributionDcl(at, _, _, _) -> if at.lookupAttribute.found then [(at.location, at.lookupAttribute.dcl)] else []
end;

aspect attributeRefLocs on AGDcl using := of
  -- Only the listed attributes
| propagateOnNTListDcl(ats, _, _) -> ats.attributeRefLocs
| strategyAttributeDcl(_, _, _, _, e) -> e.attributeRefLocs
end;

aspect attributeRefLocs on Constraint using <- of
| inhOccursConstraint(_, at, _, _, _, _) -> if at.lookupAttribute.found then [(at.location, at.lookupAttribute.dcl)] else []
| synOccursConstraint(_, at, _, _, _, _, _) -> if at.lookupAttribute.found then [(at.location, at.lookupAttribute.dcl)] else []
| annoOccursConstraint(_, at, _, _, _, _) -> if at.lookupAttribute.found then [(at.location, at.lookupAttribute.dcl)] else []
end;

aspect valueRefLocs on ProductionStmt using := of
| propagateOneAttr(_) -> []
end;

aspect attributeRefLocs on ProductionStmt using := of
| propagateOneAttr(at) -> if at.lookupAttribute.found then [(at.location, at.lookupAttribute.dcl)] else []
end;

aspect typeRefLocs on ProductionStmt using := of
| propagateOneAttr(_) -> []
end;

aspect valueRefLocs on DefLHS using <- of
| lhsDefLHS(q) -> if q.lookupValue.found then [(q.location, q.lookupValue.dcl)] else []
| childDefLHS(q) -> if q.lookupValue.found then [(q.location, q.lookupValue.dcl)] else []
| localDefLHS(q) -> if q.lookupValue.found then [(q.location, q.lookupValue.dcl)] else []
end;

aspect valueRefLocs on Expr using <- of
| baseExpr(q) -> if q.lookupValue.found then [(q.location, q.lookupValue.dcl)] else []
end;

aspect valueRefLocs on Expr using := of
| access(q, _, _) -> q.valueRefLocs
end;

aspect attributeRefLocs on Expr using := of
| access(_, _, a) -> a.attributeRefLocs
end;

aspect attributeRefLocs on AnnoExpr using <- of
| annoExpr(q, _, _) -> if q.lookupAttribute.found then [(q.location, q.lookupAttribute.dcl)] else []
end;

aspect valueRefLocs on PrimPattern using <- of
| prodPatternNormal(q, _, _) -> if q.lookupValue.found then [(q.location, q.lookupValue.dcl)] else []
| prodPatternGadt(q, _, _) -> if q.lookupValue.found then [(q.location, q.lookupValue.dcl)] else []
end;

aspect valueRefLocs on ProdNameList using <- of
| prodNameListCons(q, _, _) -> if q.lookupValue.found then [(q.location, q.lookupValue.dcl)] else []
| prodNameListOne(q) -> if q.lookupValue.found then [(q.location, q.lookupValue.dcl)] else []
end;

attribute valueRefLocs, typeRefLocs, attributeRefLocs occurs on StrategyExpr, StrategyExprs;
flowtype valueRefLocs {decorate, flowEnv, compiledGrammars} on StrategyExpr, StrategyExprs;
flowtype typeRefLocs {decorate, flowEnv, compiledGrammars} on StrategyExpr, StrategyExprs;
flowtype attributeRefLocs {decorate, flowEnv, compiledGrammars} on StrategyExpr, StrategyExprs;
propagate valueRefLocs, typeRefLocs on StrategyExpr, StrategyExprs;
propagate attributeRefLocs on StrategyExpr, StrategyExprs
  excluding partialRef, totalRef;

aspect valueRefLocs on top::StrategyExpr using <- of
| prodTraversal(q, _) -> if q.lookupValue.found then [(q.location, q.lookupValue.dcl)] else []
| rewriteRule(_, _, _) -> checkExpr.valueRefLocs
end;

aspect typeRefLocs on top::StrategyExpr using <- of
| rewriteRule(_, _, _) -> checkExpr.typeRefLocs
end;

aspect attributeRefLocs on top::StrategyExpr using <- of
| rewriteRule(_, _, _) -> checkExpr.attributeRefLocs
end;

aspect attributeRefLocs on StrategyExpr using := of
| partialRef(a) -> if attrDclFound then [(a.location, attrDcl)] else []
| totalRef(a) -> if attrDclFound then [(a.location, attrDcl)] else []
end;

synthesized attribute valueFileRefLocs::map:Map<String (Location, Decorated RootSpec, ValueDclInfo)>;
synthesized attribute typeFileRefLocs::map:Map<String (Location, Decorated RootSpec, TypeDclInfo)>;
synthesized attribute attributeFileRefLocs::map:Map<String (Location, Decorated RootSpec, AttributeDclInfo)>;

attribute valueFileRefLocs, typeFileRefLocs, attributeFileRefLocs occurs on Compilation;

aspect production compilation
top::Compilation ::= g::Grammars r::Grammars _ _
{
  top.valueFileRefLocs = buildFileRefs((.valueRefLocs), g.grammarList);
  top.typeFileRefLocs = buildFileRefs((.typeRefLocs), g.grammarList);
  top.attributeFileRefLocs = buildFileRefs((.attributeRefLocs), g.grammarList);
}

function buildFileRefs
annotation sourceGrammar occurs on a =>
map:Map<String (Location, Decorated RootSpec, a)> ::= accessor::([(Location, a)] ::= Decorated RootSpec) rs::[Decorated RootSpec]
{
  return directBuildTree(flatMap(\ r::Decorated RootSpec ->
    map(\ item::(Location, a) ->
      (r.grammarSource ++ item.1.filename, item.1, head(map:lookup(item.2.sourceGrammar, r.compiledGrammars)), item.2),
      accessor(r)),
    rs));
}

attribute valueRefLocs, typeRefLocs, attributeRefLocs occurs on InterfaceItems, InterfaceItem;
propagate valueRefLocs, typeRefLocs, attributeRefLocs on InterfaceItems;

aspect default production
top::InterfaceItem ::=
{
  top.valueRefLocs := [];
  top.typeRefLocs := [];
  top.attributeRefLocs := [];
}

abstract production refLocInterfaceItem
top::InterfaceItem ::= values::[(Location, ValueDclInfo)] types::[(Location, TypeDclInfo)] attrs::[(Location, AttributeDclInfo)]
{
  top.isEqual = true;  -- Don't rebuild downstream grammars when referenced locations change
  top.valueRefLocs := values;
  top.typeRefLocs := types;
  top.attributeRefLocs := attrs;
}

aspect function packInterfaceItems
InterfaceItems ::= r::Decorated RootSpec
{
  interfaceItems <- [
    refLocInterfaceItem(r.valueRefLocs, r.typeRefLocs, r.attributeRefLocs)
  ];
}

function lookupPos
[a] ::= line::Integer col::Integer items::[(Location, a)]
{
  return map(snd, filter(
    \ item::(Location, a) ->
      item.1.line <= line && item.1.endLine >= line && item.1.column <= col && item.1.endColumn >= col,
    items));
}

function updateLocPath
Location ::= p::String l::Location
{
  return loc(p, l.line, l.column, l.endLine, l.endColumn, l.index, l.endIndex);
}

function lookupDeclLocation
annotation sourceGrammar occurs on a,
annotation sourceLocation occurs on a =>
[Location] ::= fileName::String line::Integer col::Integer decls::map:Map<String (Location, Decorated RootSpec, a)>
{
  return map(\ item::(Decorated RootSpec, a) ->
    updateLocPath(item.1.grammarSource ++ item.2.sourceLocation.filename, item.2.sourceLocation),
    lookupPos(line, col, map:lookup(fileName, decls)));
}

function findDeclLocation
[Location] ::= fileName::String line::Integer col::Integer c::Decorated Compilation
{
  return
    lookupDeclLocation(fileName, line, col, c.valueFileRefLocs) ++
    lookupDeclLocation(fileName, line, col, c.typeFileRefLocs) ++
    lookupDeclLocation(fileName, line, col, c.attributeFileRefLocs);
}