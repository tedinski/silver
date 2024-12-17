grammar silver:compiler:extension:autoattr;

import silver:compiler:driver:util;
import silver:compiler:definition:flow:driver only ProductionGraph, FlowType, constructAnonymousGraph;

concrete production monoidAttributeDcl
top::AGDcl ::= 'monoid' 'attribute' a::Name tl::BracketedOptTypeExprs '::' te::TypeExpr 'with' e::Expr ',' q::NameOrBOperator ';'
{
  top.unparse = "monoid attribute " ++ a.unparse ++ tl.unparse ++ " :: " ++ te.unparse ++ " with " ++ e.unparse ++ ", " ++ q.unparse ++ ";";
  propagate config, grammarName, compiledGrammars, flowEnv;

  production attribute fName :: String;
  fName = top.grammarName ++ ":" ++ a.name;

  tl.initialEnv = top.env;
  tl.env = tl.envBindingTyVars;
  te.env = tl.envBindingTyVars;
  e.env = tl.envBindingTyVars;
  q.env = tl.envBindingTyVars;
  
  q.operatorForType = te.typerep;
  
  -- TODO: We want to define our own defs here but can't forward to defsAGDcl because collections define different translation.
  -- Not sure about the best way to refactor this.
  top.defs :=
    [attrDef(defaultEnvItem(monoidDcl(fName, tl.freeVariables, te.typerep, ^e, q.operation, sourceGrammar=top.grammarName, sourceLocation=a.nameLoc)))];

  top.errors <- e.errors;
  
  top.errors <-
    if length(getAttrDclAll(fName, top.env)) > 1
    then [errFromOrigin(a, "Attribute '" ++ fName ++ "' is already bound.")]
    else [];
  
  local errCheck1 :: TypeCheck = check(e.typerep, te.typerep);
  top.errors <-
    if errCheck1.typeerror
    then [errFromOrigin(e, "Monoid attribute " ++ fName ++ " of type " ++ errCheck1.rightpp ++ " has empty value specified with type " ++ errCheck1.leftpp)]
    else [];

  e.downSubst = emptySubst();
  errCheck1.downSubst = e.upSubst;
  e.downSubst2 = errCheck1.upSubst;
  e.finalSubst = e.upSubst2;
  errCheck1.finalSubst = e.finalSubst;
  
  -- oh no again!
  local myFlow :: EnvTree<FlowType> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).grammarFlowTypes;
  local myProds :: EnvTree<ProductionGraph> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).productionFlowGraphs;

  local myFlowGraph :: ProductionGraph = 
    constructAnonymousGraph(e.flowDefs, top.env, myProds, myFlow);

  e.frame = globalExprContext(fName, nilContext(), te.typerep, myFlowGraph, sourceGrammar=top.grammarName);
  e.isRoot = false;
  e.decSiteVertexInfo = nothing();
  e.alwaysDecorated = false;
  e.appDecSiteVertexInfo = nothing();
  e.dispatchFlowDeps = [];
  
  forwards to
    collectionAttributeDclSyn(
      'synthesized', 'attribute', @a, @tl, '::', @te, 'with', @q, ';');
}

concrete production tcMonoidAttributeDcl
top::AGDcl ::= 'monoid' 'attribute' a::Name tl::BracketedOptTypeExprs '::' te::TypeExpr ';'
{
  top.unparse = "monoid attribute " ++ a.unparse ++ tl.unparse ++ " :: " ++ te.unparse ++ ";";
  forwards to
    monoidAttributeDcl(
      $1, $2, @a, @tl, $5, @te, 'with',
      baseExpr(qName("silver:core:mempty")), ',',
      exprOperator(baseExpr(qName("silver:core:append"))), $7);
}

synthesized attribute appendProd :: (Expr ::= Expr Expr) occurs on Operation;

aspect production functionOperation
top::Operation ::= e::Expr _ _
{
  top.appendProd = \ e1::Expr e2::Expr -> mkFunctionInvocation(^e, [e1, e2]);
}
aspect production plusPlusOperationString
top::Operation ::= 
{
  top.appendProd = plusPlus(_, '++', _);
}
aspect production plusPlusOperationList
top::Operation ::= 
{
  top.appendProd = plusPlus(_, '++', _);
}
aspect production borOperation
top::Operation ::= 
{
  top.appendProd = or(_, '||', _);
}
aspect production bandOperation
top::Operation ::= 
{
  top.appendProd = and(_, '&&', _);
}
aspect production addOperation
top::Operation ::= 
{
  top.appendProd = plus(_, '+', _);
}
aspect production mulOperation
top::Operation ::= 
{
  top.appendProd = multiply(_, '*', _);
}

{--
 - Propagate a monoid attribute on the enclosing production
 - @param attr  The name of the attribute to propagate
 -}
abstract production propagateMonoid implements Propagate
top::ProductionStmt ::= includeShared::Boolean @attr::QName
{
  top.unparse = s"propagate ${if includeShared then "@" else ""}${attr.unparse};";
  
  -- No explicit errors, for now.  The only conceivable issue is the attribute not
  -- occuring on the LHS but this should be caught by the forward errors.  
  
  local attrFullName::String = attr.lookupAttribute.dcl.fullName;
  local inputsWithAttr::[NamedSignatureElement] =
    filter(
      \ input::NamedSignatureElement ->
        (isDecorable(input.elementDclType, top.env) || input.elementDclType.isNonterminal) &&
        !null(getOccursDcl(attrFullName, input.elementDclType.typeName, top.env)),
      top.frame.signature.inputElements);
  nondecorated local res::Expr =
    if null(inputsWithAttr)
    then attr.lookupAttribute.dcl.emptyVal
    else
      foldr1(
        attr.lookupAttribute.dcl.operation.appendProd,
        map(
          \ i::NamedSignatureElement ->
            access(
              baseExpr(qName(i.elementName)),
              '.',
              qNameAttrOccur(^attr)),
          inputsWithAttr));

  -- Construct an attribute def and call with the generated arguments
  forwards to
    attrContainsBase(
      concreteDefLHS(qName(top.frame.signature.outputElement.elementName)),
      '.',
      qNameAttrOccur(^attr),
      ':=', res, ';');
}

abstract production monoidErrorRegularAttributeDef implements AttributeDef
top::ProductionStmt ::= @dl::DefLHS @attr::QNameAttrOccur e::Expr
{
  forwards to errorAttributeDef(
    dl, attr, @e,
    [errFromOrigin(top, dl.unparse ++ "." ++ attr.unparse ++ " is a monoid collection attribute, and you must use ':=' or '<-', not '='.")]);
}
