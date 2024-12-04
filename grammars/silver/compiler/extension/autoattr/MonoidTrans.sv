grammar silver:compiler:extension:autoattr;

import silver:compiler:driver:util;
import silver:compiler:definition:flow:driver only ProductionGraph, FlowType, constructAnonymousGraph;

concrete production monoidTransAttributeDcl
top::AGDcl ::= 'monoid' 'translation' 'attribute' a::Name tl::BracketedOptTypeExprs '::' te::TypeExpr 'with' e::Expr ',' app::QName ';'
{
  top.unparse = "monoid translation attribute " ++ a.unparse ++ tl.unparse ++ " :: " ++ te.unparse ++ " with " ++ e.unparse ++ ", " ++ app.unparse ++ ";";
  top.moduleNames := [];
  propagate config, grammarName, compiledGrammars, flowEnv;

  production attribute fName :: String;
  fName = top.grammarName ++ ":" ++ a.name;

  tl.initialEnv = top.env;
  tl.env = tl.envBindingTyVars;
  te.env = tl.envBindingTyVars;
  e.env = tl.envBindingTyVars;
  app.env = tl.envBindingTyVars;

  top.errors <- e.errors;
  top.errors <- app.lookupValue.errors;
  
  top.errors <-
    if length(getAttrDclAll(fName, top.env)) > 1
    then [errFromOrigin(a, "Attribute '" ++ fName ++ "' is already bound.")]
    else [];
  
  local errCheck1 :: TypeCheck = check(e.typerep, te.typerep);
  top.errors <-
    if errCheck1.typeerror
    then [errFromOrigin(e, "Monoid translation attribute " ++ fName ++ " of type " ++ errCheck1.rightpp ++ " has empty value specified with type " ++ errCheck1.leftpp)]
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
  
  forwards to defsAGDcl(
    [attrDef(defaultEnvItem(monoidTransDcl(fName, tl.freeVariables, te.typerep, ^e, app.lookupValue.fullName, sourceGrammar=top.grammarName, sourceLocation=a.nameLoc)))]);
}

{--
 - Propagate a monoid attribute on the enclosing production
 - @param attr  The name of the attribute to propagate
 -}
abstract production propagateMonoidTrans implements Propagate
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
        \ e1 e2 -> Silver_Expr { $qName{attr.lookupAttribute.dcl.appendProdName}($Expr{e1}, $Expr{e2}) },
        map(
          \ i::NamedSignatureElement -> Silver_Expr {
            @$name{i.elementName}.$QName{^attr}
          },
          inputsWithAttr));

  -- Construct an attribute def and call with the generated arguments
  forwards to
    attributeDef(
      concreteDefLHS(qName(top.frame.signature.outputElement.elementName)),
      '.',
      qNameAttrOccur(^attr),
      '=', res, ';');
}
