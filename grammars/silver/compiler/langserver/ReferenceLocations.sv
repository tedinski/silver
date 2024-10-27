grammar silver:compiler:langserver;

monoid attribute valueRefLocs::[(Location, ValueDclInfo)];
monoid attribute typeRefLocs::[(Location, TypeDclInfo)];
monoid attribute attributeRefLocs::[(Location, AttributeDclInfo)];

attribute valueRefLocs, typeRefLocs, attributeRefLocs occurs on
  RootSpec, Grammar, Root, NameList, AGDcls, AGDcl,
  ProductionSignature, FunctionSignature, AspectProductionSignature, AspectFunctionSignature, AspectDefaultProductionSignature,
  ConstraintList, Constraint, ProductionLHS, FunctionLHS, AspectProductionLHS, AspectFunctionLHS,
  ProductionRHS, AspectRHS, ProductionRHSElem, AspectRHSElem,
  TypeExpr, Signature, SignatureLHS, TypeExprs, BracketedTypeExprs, BracketedOptTypeExprs,
  ProductionBody, ProductionStmts, ProductionStmt, DefLHS,
  ClassBody, ClassBodyItem, InstanceBody, InstanceBodyItem,
  Expr, Exprs, ExprInhs, ExprInh, ExprLHSExpr, AppExprs, AppExpr, AnnoAppExprs, AnnoExpr,
  PrimPatterns, PrimPattern, AttrNameList, ProdNameList;

propagate valueRefLocs, typeRefLocs, attributeRefLocs on
  RootSpec, Grammar, Root, NameList, AGDcls, AGDcl,
  ProductionSignature, FunctionSignature, AspectProductionSignature, AspectFunctionSignature, AspectDefaultProductionSignature,
  ConstraintList, Constraint, ProductionLHS, FunctionLHS, AspectProductionLHS, AspectFunctionLHS,
  ProductionRHS, AspectRHS, ProductionRHSElem, AspectRHSElem,
  TypeExpr, Signature, SignatureLHS, TypeExprs, BracketedTypeExprs, BracketedOptTypeExprs,
  ProductionBody, ProductionStmts, ProductionStmt, DefLHS,
  ClassBody, ClassBodyItem, InstanceBody, InstanceBodyItem,
  Expr, Exprs, ExprInhs, ExprInh, ExprLHSExpr, AppExprs, AppExpr, AnnoAppExprs, AnnoExpr,
  PrimPatterns, PrimPattern, AttrNameList, ProdNameList;

aspect valueRefLocs on NameList using <- of
| nameListCons(q, _, _) -> if q.lookupValue.found then [(q.nameLoc, q.lookupValue.dcl)] else []
| nameListOne(q) -> if q.lookupValue.found then [(q.nameLoc, q.lookupValue.dcl)] else []
end;

aspect typeRefLocs on NameList using <- of
| nameListCons(q, _, _) -> if q.lookupType.found then [(q.nameLoc, q.lookupType.dcl)] else []
| nameListOne(q) -> if q.lookupType.found then [(q.nameLoc, q.lookupType.dcl)] else []
end;

aspect attributeRefLocs on NameList using <- of
| nameListCons(q, _, _) -> if q.lookupAttribute.found then [(q.nameLoc, q.lookupAttribute.dcl)] else []
| nameListOne(q) -> if q.lookupAttribute.found then [(q.nameLoc, q.lookupAttribute.dcl)] else []
end;

attribute typeRefLocs occurs on QNameType;
aspect typeRefLocs on top::QNameType using := of
| _ -> if top.lookupType.found then [(top.nameLoc, top.lookupType.dcl)] else []
end;

attribute attributeRefLocs occurs on QNameAttrOccur;
aspect attributeRefLocs on top::QNameAttrOccur using := of
| qNameAttrOccur(at) -> if top.found then [(at.nameLoc, top.attrDcl)] else []
end;

aspect valueRefLocs on AGDcl using <- of
| aspectProductionDcl(_, _, q, _, _) -> if q.lookupValue.found then [(q.nameLoc, q.lookupValue.dcl)] else []
| aspectFunctionDcl(_, _, q, _, _) -> if q.lookupValue.found then [(q.nameLoc, q.lookupValue.dcl)] else []
end;

aspect valueRefLocs on AGDcl using := of
| propagateOnNTListDcl(_, _, ps) -> ps.valueRefLocs
  -- Exclude mempty/append declarations from forwarding
| tcMonoidAttributeDcl(_, _, _, _, _, te, _) -> te.valueRefLocs
| strategyAttributeDcl(_, _, _, _, e) -> e.valueRefLocs
end;

aspect typeRefLocs on AGDcl using <- of
| defaultAttributionDcl(_, _, nt, _) -> if nt.lookupType.found then [(nt.nameLoc, nt.lookupType.dcl)] else []
end;

aspect typeRefLocs on AGDcl using := of
| propagateOnNTListDcl(_, nts, _) -> nts.typeRefLocs
| strategyAttributeDcl(_, _, _, _, e) -> e.typeRefLocs
end;

aspect attributeRefLocs on AGDcl using <- of
| defaultAttributionDcl(at, _, _, _) -> if at.lookupAttribute.found then [(at.nameLoc, at.lookupAttribute.dcl)] else []
end;

aspect attributeRefLocs on AGDcl using := of
  -- Only the listed attributes
| propagateOnNTListDcl(ats, _, _) -> ats.attributeRefLocs
| strategyAttributeDcl(_, _, _, _, e) -> e.attributeRefLocs
end;

aspect production propagateOnNTListDcl
top::AGDcl ::= attrs::AttrNameList nts::NameList ps::ProdNameList
{
  propagate env, flowEnv;
}

aspect production tcMonoidAttributeDcl
top::AGDcl ::= 'monoid' 'attribute' a::Name tl::BracketedOptTypeExprs _ te::TypeExpr ';'
{
  propagate grammarName, env, flowEnv;
}

aspect attributeRefLocs on Constraint using <- of
| inhOccursConstraint(_, at, _, _, _, _) -> if at.lookupAttribute.found then [(at.nameLoc, at.lookupAttribute.dcl)] else []
| synOccursConstraint(_, at, _, _, _, _, _) -> if at.lookupAttribute.found then [(at.nameLoc, at.lookupAttribute.dcl)] else []
| annoOccursConstraint(_, at, _, _, _, _) -> if at.lookupAttribute.found then [(at.nameLoc, at.lookupAttribute.dcl)] else []
end;

aspect valueRefLocs on top::ProductionStmt using <- of
| localAttributeDcl(_, _, n, _, _, _) -> map(\dcl :: ValueDclInfo -> (n.nameLoc, dcl), getValueDcl(n.name, top.env))
| productionAttributeDcl(_, _, n, _, _, _) -> map(\dcl :: ValueDclInfo -> (n.nameLoc, dcl), getValueDcl(n.name, top.env))
| nondecLocalAttributeDcl(_, _, _, n, _, _, _) -> map(\dcl :: ValueDclInfo -> (n.nameLoc, dcl), getValueDcl(n.name, top.env))
| nondecProductionAttributeDcl(_, _, _, n, _, _, _) -> map(\dcl :: ValueDclInfo -> (n.nameLoc, dcl), getValueDcl(n.name, top.env))
| forwardProductionAttributeDcl(_, _, _, n, _) -> map(\dcl :: ValueDclInfo -> (n.nameLoc, dcl), getValueDcl(n.name, top.env))
end;

aspect valueRefLocs on ProductionStmt using := of
| propagateOneAttr(_, _) -> []
end;

aspect attributeRefLocs on ProductionStmt using := of
| propagateOneAttr(_, at) -> if at.lookupAttribute.found then [(at.nameLoc, at.lookupAttribute.dcl)] else []
end;

aspect typeRefLocs on ProductionStmt using := of
| propagateOneAttr(_, _) -> []
end;

aspect valueRefLocs on DefLHS using <- of
| lhsDefLHS(q) -> if q.lookupValue.found then [(q.nameLoc, q.lookupValue.dcl)] else []
| childDefLHS(q) -> if q.lookupValue.found then [(q.nameLoc, q.lookupValue.dcl)] else []
| localDefLHS(q) -> if q.lookupValue.found then [(q.nameLoc, q.lookupValue.dcl)] else []
end;

aspect valueRefLocs on Expr using <- of
| baseExpr(q) -> if q.lookupValue.found then [(q.nameLoc, q.lookupValue.dcl)] else []
end;

aspect valueRefLocs on Expr using := of
| access(q, _, _) -> q.valueRefLocs
| attributeSection(_, _, _, _) -> []
| consListOp(h, _, t) -> h.valueRefLocs ++ t.valueRefLocs
| emptyList(_, _) -> []
| stringAppendCall(a, b) -> a.valueRefLocs ++ b.valueRefLocs
end;

aspect attributeRefLocs on Expr using := of
| access(_, _, a) -> a.attributeRefLocs
| attributeSection(_, _, a, _) -> a.attributeRefLocs
end;

aspect typeRefLocs on Expr using := of
| attributeSection(_, _, _, _) -> []
end;

aspect attributeRefLocs on AnnoExpr using <- of
| annoExpr(q, _, _) -> if q.lookupAttribute.found then [(q.nameLoc, q.lookupAttribute.dcl)] else []
end;

aspect valueRefLocs on PrimPattern using <- of
| prodPatternNormal(q, _, _) -> if q.lookupValue.found then [(q.nameLoc, q.lookupValue.dcl)] else []
| prodPatternGadt(q, _, _) -> if q.lookupValue.found then [(q.nameLoc, q.lookupValue.dcl)] else []
end;

aspect attributeRefLocs on AttrNameList using <- of
| attrNameListCons(_, q, _, _) -> if q.lookupAttribute.found then [(q.nameLoc, q.lookupAttribute.dcl)] else []
| attrNameListOne(_, q) -> if q.lookupAttribute.found then [(q.nameLoc, q.lookupAttribute.dcl)] else []
end;

aspect valueRefLocs on ProdNameList using <- of
| prodNameListCons(q, _, _) -> if q.lookupValue.found then [(q.nameLoc, q.lookupValue.dcl)] else []
| prodNameListOne(q) -> if q.lookupValue.found then [(q.nameLoc, q.lookupValue.dcl)] else []
end;

attribute valueRefLocs, typeRefLocs, attributeRefLocs occurs on StrategyExpr, StrategyExprs;
flowtype valueRefLocs {decorate, flowEnv, compiledGrammars} on StrategyExpr, StrategyExprs;
flowtype typeRefLocs {decorate, flowEnv, compiledGrammars} on StrategyExpr, StrategyExprs;
flowtype attributeRefLocs {decorate, flowEnv, compiledGrammars} on StrategyExpr, StrategyExprs;
propagate valueRefLocs, typeRefLocs on StrategyExpr, StrategyExprs;
propagate attributeRefLocs on StrategyExpr, StrategyExprs
  excluding partialRef, totalRef;

aspect valueRefLocs on top::StrategyExpr using <- of
| prodTraversal(q, _) -> if q.lookupValue.found then [(q.nameLoc, q.lookupValue.dcl)] else []
| rewriteRule(_, _, _) -> checkExpr.valueRefLocs
end;

aspect typeRefLocs on top::StrategyExpr using <- of
| rewriteRule(_, _, _) -> checkExpr.typeRefLocs
end;

aspect attributeRefLocs on top::StrategyExpr using <- of
| rewriteRule(_, _, _) -> checkExpr.attributeRefLocs
end;

aspect attributeRefLocs on StrategyExpr using := of
| partialRef(a) -> if attrDclFound then [(a.nameLoc, ^attrDcl)] else []
| totalRef(a) -> if attrDclFound then [(a.nameLoc, ^attrDcl)] else []
end;

-- Productions
-- LHS
aspect valueRefLocs on top::ProductionLHS using <- of
| productionLHS(n, _, _) -> map(\dcl :: ValueDclInfo -> (n.nameLoc, dcl), getValueDcl(n.name, top.env))
end;

aspect valueRefLocs on top::AspectProductionLHS using <- of
| aspectProductionLHSFull(n, _) -> map(\dcl :: ValueDclInfo -> (n.nameLoc, dcl), getValueDcl(n.name, top.env))
end;

aspect typeRefLocs on ProductionLHS using <- of
| productionLHS(_, _, t) -> t.typeRefLocs
end;

aspect typeRefLocs on AspectProductionLHS using <- of
| aspectProductionLHSTyped(_, _, t) -> t.typeRefLocs
end;

aspect typeRefLocs on top::AspectDefaultProductionSignature using <- of
| aspectDefaultProductionSignature(_,_,t,_) -> t.typeRefLocs
end;

--RHS
aspect valueRefLocs on top::ProductionRHSElem using <- of
| productionRHSElem(_, n, _, _) -> map(\dcl :: ValueDclInfo -> (n.nameLoc, dcl), getValueDcl(n.name, top.env))
end;

aspect valueRefLocs on top::AspectRHSElem using <- of
| aspectRHSElemFull(_, n, _) -> map(\dcl :: ValueDclInfo -> (n.nameLoc, dcl), getValueDcl(n.name, top.env))
end;

aspect typeRefLocs on ProductionRHSElem using <- of
| productionRHSElem(_, _, _, t) -> t.typeRefLocs
end;

aspect typeRefLocs on AspectRHSElem using <- of
| aspectRHSElemTyped(_, _, t) -> t.typeRefLocs
| aspectRHSElemSharedTyped(_, _, _, t) -> t.typeRefLocs
end;

synthesized attribute valueFileRefLocs::map:Map<String (Location, Decorated RootSpec, ValueDclInfo)>;
synthesized attribute typeFileRefLocs::map:Map<String (Location, Decorated RootSpec, TypeDclInfo)>;
synthesized attribute attributeFileRefLocs::map:Map<String (Location, Decorated RootSpec, AttributeDclInfo)>;

synthesized attribute allValueRefs::map:Map<String (String, Location)>;
synthesized attribute allTypeRefs::map:Map<String (String, Location)>;
synthesized attribute allAttributeRefs::map:Map<String (String, Location)>;

attribute valueFileRefLocs, typeFileRefLocs, attributeFileRefLocs, allValueRefs, allTypeRefs, allAttributeRefs occurs on Compilation;

aspect production compilation
top::Compilation ::= g::Grammars r::Grammars _ _ _
{
  top.valueFileRefLocs = buildFileRefs((.valueRefLocs), (.valueList), g.grammarList);
  top.typeFileRefLocs = buildFileRefs((.typeRefLocs), (.typeList), g.grammarList);
  top.attributeFileRefLocs = buildFileRefs((.attributeRefLocs), (.attrList), g.grammarList);
  top.allValueRefs = buildAllRefs((.valueRefLocs), g.grammarList);
  top.allTypeRefs = buildAllRefs((.typeRefLocs), g.grammarList);
  top.allAttributeRefs = buildAllRefs((.attributeRefLocs), g.grammarList);
}

fun buildFileRefs
annotation sourceLocation occurs on a,
annotation sourceGrammar occurs on a =>
map:Map<String (Location, Decorated RootSpec, a)> ::= 
  accessor::([(Location, a)] ::= Decorated RootSpec)  
  accessList::([EnvItem<a>] ::= Def)
  rs::[Decorated RootSpec] =
  directBuildTree(flatMap(\ r::Decorated RootSpec ->
    map(\ item::(Location, a) ->
      (r.grammarSource ++ item.1.filename, item.1, head(map:lookup(item.2.sourceGrammar, r.compiledGrammars)), item.2),
      accessor(r)) ++
    -- We add the declaration sites of all global defs as reference locations here as a shortcut
    -- instead of adding aspects for them in RefLocs
    flatMap(\def::Def ->
      map(\item::EnvItem<a> ->
        (r.grammarSource ++ item.dcl.sourceLocation.filename, item.dcl.sourceLocation, r, item.dcl),
        accessList(def)),
      r.defs),
    rs));

-- Create a map from a reference's unique id to its path & location
function buildAllRefs
annotation sourceGrammar occurs on a,
annotation sourceLocation occurs on a,
attribute fullName {} occurs on a =>
map:Map<String (String, Location)> ::= accessor::([(Location, a)] ::= Decorated RootSpec) rs::[Decorated RootSpec]
{
  local grammarMap :: map:Map<String String> =
    directBuildTree(map(\ r::Decorated RootSpec -> (r.declaredName, r.grammarSource), rs));

  return directBuildTree(flatMap(\ r::Decorated RootSpec ->
    (flatMap(\item::(Location, a) -> 
      [(makeRefId(item.2), r.grammarSource ++ item.1.filename, item.1)] ++
      -- Include source location & file of reference dcl
      (map(\grammarPath::String -> 
          (makeRefId(item.2), grammarPath ++ item.2.sourceLocation.filename, item.2.sourceLocation), 
          map:lookup(item.2.sourceGrammar, grammarMap))),
      accessor(r))), 
    rs));  
}

-- Compute a unique identifier for a decl including its sourceGrammar and sourceLocation,
-- since fullName might not be globally unique.
function makeRefId
annotation sourceGrammar occurs on a,
annotation sourceLocation occurs on a,
attribute fullName {} occurs on a =>
String ::= dcl::a
{
  return s"${dcl.fullName}@${dcl.sourceGrammar}@${dcl.sourceLocation.unparse}";
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

fun lookupPos [a] ::= line::Integer col::Integer items::[(Location, a)] =
  map(snd, filter(
    \ item::(Location, a) ->
      item.1.line <= line && item.1.endLine >= line && item.1.column <= col && item.1.endColumn >= col,
    items));

fun updateLocPath Location ::= p::String l::Location =
  loc(p, l.line, l.column, l.endLine, l.endColumn, l.index, l.endIndex);

fun lookupDeclLocation
annotation sourceGrammar occurs on a,
annotation sourceLocation occurs on a =>
[Location] ::= fileName::String line::Integer col::Integer decls::map:Map<String (Location, Decorated RootSpec, a)> =
  map(\ item::(Decorated RootSpec, a) ->
    updateLocPath(item.1.grammarSource ++ item.2.sourceLocation.filename, item.2.sourceLocation),
    lookupPos(line, col, map:lookup(fileName, decls)));

fun findDeclLocation
[Location] ::= fileName::String line::Integer col::Integer c::Compilation =
  lookupDeclLocation(fileName, line, col, c.valueFileRefLocs) ++
  lookupDeclLocation(fileName, line, col, c.typeFileRefLocs) ++
  lookupDeclLocation(fileName, line, col, c.attributeFileRefLocs);

-- Looks up all references to symbol at the given location
-- Returns a list of all reference locations
-- Input is filename, line & col number, & decl map to resolve the symbol
-- Uses refs map to lookup the reference paths & locations from the symbol unique id  
fun lookupReferenceLocations
annotation sourceGrammar occurs on a,
annotation sourceLocation occurs on a,
attribute fullName {} occurs on a =>
[Location] ::= fileName::String line::Integer col::Integer decls::map:Map<String (Location, Decorated RootSpec, a)> refs::map:Map<String (String, Location)> =
  flatMap(\ item::(Decorated RootSpec, a) -> 
    map(\ loc::(String, Location) -> updateLocPath(loc.1, loc.2), 
      map:lookup(makeRefId(item.2), refs)), 
    lookupPos(line, col, map:lookup(fileName, decls)));

fun findReferences
[Location] ::= fileName::String line::Integer col::Integer c::Compilation =
  lookupReferenceLocations(fileName, line, col, c.valueFileRefLocs, c.allValueRefs) ++
  lookupReferenceLocations(fileName, line, col, c.typeFileRefLocs, c.allTypeRefs) ++
  lookupReferenceLocations(fileName, line, col, c.attributeFileRefLocs, c.allAttributeRefs);
