grammar silver:compiler:definition:flow:env;

import silver:compiler:definition:flow:driver only ProductionGraph, FlowType, constructFunctionGraph, constructAnonymousGraph;
import silver:compiler:driver:util only RootSpec; -- actually we just want the occurrences
import silver:compiler:definition:type:syntax; -- actually we just want the occurrences
import silver:compiler:modification:concisefunctions;

attribute flowEnv occurs on FunctionSignature, FunctionLHS;
propagate flowEnv on FunctionSignature, FunctionLHS;

aspect production functionDcl
top::AGDcl ::= 'function' id::Name ns::FunctionSignature body::ProductionBody 
{
  -- oh no again!
  local myFlow :: EnvTree<FlowType> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).grammarFlowTypes;
  local myProds :: EnvTree<ProductionGraph> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).productionFlowGraphs;

  {-- Used by core to send down with .frame -}
  production myFlowGraph :: ProductionGraph = 
    constructFunctionGraph(namedSig, top.flowEnv, top.env, myProds, myFlow);

  top.flowDefs <- flatMap(
    \ ie::NamedSignatureElement -> occursContextDeps(namedSig, top.env, ie.typerep, rhsVertexType(ie.elementName)),
    namedSig.inputElements);
}

aspect production aspectFunctionDcl
top::AGDcl ::= 'aspect' 'function' id::QName ns::AspectFunctionSignature body::ProductionBody 
{
  -- oh no again!
  local myFlow :: EnvTree<FlowType> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).grammarFlowTypes;
  local myProds :: EnvTree<ProductionGraph> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).productionFlowGraphs;

  {-- Used by core to send down with .frame -}
  production myFlowGraph :: ProductionGraph = 
    constructFunctionGraph(namedSig, top.flowEnv, top.env, myProds, myFlow);
}

aspect production shortFunctionDcl
top::AGDcl ::= 'fun' id::Name ns::FunctionSignature '=' e::Expr ';'
{
  e.decSiteVertexInfo = nothing();
  e.alwaysDecorated = false;
  e.appDecSiteVertexInfo = nothing();
  e.dispatchFlowDeps = [];

  -- oh no again!
  local myFlow :: EnvTree<FlowType> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).grammarFlowTypes;
  local myProds :: EnvTree<ProductionGraph> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).productionFlowGraphs;

  production myFlowGraph :: ProductionGraph =
    constructAnonymousGraph(e.flowDefs, top.env, myProds, myFlow);

  top.flowDefs <- flatMap(
    \ ie::NamedSignatureElement -> occursContextDeps(namedSig, top.env, ie.typerep, rhsVertexType(ie.elementName)),
    namedSig.inputElements);
}
