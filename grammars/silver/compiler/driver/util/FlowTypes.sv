grammar silver:compiler:driver:util;

import silver:compiler:definition:flow:driver;
import silver:compiler:definition:flow:ast;
import silver:compiler:definition:flow:env;
import silver:compiler:analysis:uniqueness;
import silver:util:treemap as rtm;
import silver:util:graph as g;
import silver:util:cmdargs;

-- Hide all the flow type computation over here

aspect production compilation
top::Compilation ::= g::Grammars  r::Grammars  buildGrammars::[String]  a::Decorated CmdArgs  benv::BuildEnv
{
  -- aggregate all flow def information
  local allFlowDefs :: FlowDefs = foldr(consFlow, nilFlow(), flatMap((.flowDefs), allLatestGrammars));
  local allSpecDefs :: [(String, String, [String], [String])] = flatMap((.specDefs), allLatestGrammars);
  local allRefDefs :: [(String, [String])] = flatMap((.refDefs), allLatestGrammars);
  local allSharedRefs :: [(String, SharedRefSite)] = flatMap((.sharedRefs), allLatestGrammars);
  local allFlowEnv :: FlowEnv = flowEnv(allSpecDefs, allRefDefs, allSharedRefs, allFlowDefs);
  
  -- We need to know about all attributes and occurences on nonterminals.
  -- It's possible (likely) we could do better than using the overall env here.
  local allRealDefs :: [Def] = flatMap((.defs), allLatestGrammars);
  local allRealOccursDefs :: [OccursDclInfo] = flatMap((.occursDefs), allLatestGrammars);
  local allRealEnv :: Env = toEnv(allRealDefs, allRealOccursDefs);
  
  -- List of all productions
  local allProds :: [ValueDclInfo] = allRealEnv.prodDclList;
  local allNts :: [String] = nub(map(getProdNt, allProds));
  local allDispatchSigs :: [NamedSignature] = map((.dispatchSignature), allRealEnv.dispatchDclList);
  
  -- Construct production graphs.
  production prodGraph :: [ProductionGraph] = 
    map(constructProductionGraph(_, allFlowEnv, allRealEnv), allProds) ++
    -- Add in phantom, default and dispatch graphs
    flatMap(constructPhantomProductionGraph(_, allFlowEnv, allRealEnv), allNts) ++
    flatMap(constructDefaultProductionGraph(_, allFlowEnv, allRealEnv), allNts) ++
    map(constructDispatchGraph(_, allFlowEnv, allRealEnv), allDispatchSigs);
  
  local initialFT :: EnvTree<FlowType> =
    computeInitialFlowTypes(allSpecDefs);
  
  -- Now, solve for flow types!!
  local flowTypes1 :: (EnvTree<ProductionGraph>, EnvTree<FlowType>) =
    runFlowTypeInference(prodGraph, initialFT);
  
  production finalGraphEnv :: EnvTree<ProductionGraph> = flowTypes1.fst;
  production flowTypes :: EnvTree<FlowType> = flowTypes1.snd;
  
  g.productionFlowGraphs = finalGraphEnv;
  g.grammarFlowTypes = flowTypes;
  
  r.productionFlowGraphs = finalGraphEnv;
  r.grammarFlowTypes = flowTypes;
}

function getProdNt
String ::= d::ValueDclInfo
{
  return d.namedSignature.outputElement.typerep.typeName;
}
