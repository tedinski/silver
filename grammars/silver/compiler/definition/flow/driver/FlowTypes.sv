grammar silver:compiler:definition:flow:driver;

imports silver:compiler:definition:core;
imports silver:compiler:definition:env;
imports silver:compiler:definition:flow:env;
imports silver:compiler:definition:flow:ast;
imports silver:compiler:analysis:warnings:flow only isOccursSynthesized;
imports silver:compiler:analysis:uniqueness;

imports silver:util:treemap as rtm;
imports silver:util:graph as g;
imports silver:util:treeset as set;

-- Help some type signatures suck a little less
type ProdName = String;
type NtName = String;

-- from explicit specifications and initial flow graphs
function computeInitialFlowTypes
EnvTree<FlowType> ::= specDefs::[(String, String, [String], [String])]
{
  -- We don't care what flow specs reference what
  local dropRefs::[(String, String, [String])] =
    map(\ d::(String, String, [String], [String]) -> (d.1, d.2, d.3), specDefs);

  local specs :: [(NtName, [(String, [String])])] =
    ntListCoalesce(groupBy(ntListEq, sortBy(ntListLte, dropRefs)));
  
  return rtm:add(map(initialFlowType, specs), rtm:empty());
}
fun initialFlowType Pair<NtName FlowType> ::= x::(NtName, [(String, [String])]) =
  (x.fst, g:add(flatMap(toFlatEdges, x.snd), g:empty()));
fun ntListLte Boolean ::= a::Pair<NtName a>  b::Pair<NtName b> = a.fst <= b.fst;
fun ntListEq Boolean ::= a::Pair<NtName a>  b::Pair<NtName b> = a.fst == b.fst;
fun ntListCoalesce [(NtName, [(String, [String])])] ::= l::[[(NtName, String, [String])]] =
  if null(l) then []
  else (head(head(l)).fst, map(snd, head(l))) :: ntListCoalesce(tail(l));
fun toFlatEdges [Pair<String String>] ::= x::Pair<String [String]> =
  map(pair(fst=x.fst, snd=_), x.snd);

fun runFlowTypeInference
(EnvTree<ProductionGraph>, EnvTree<FlowType>) ::=
    graphs::[ProductionGraph] ntEnv::EnvTree<FlowType> =
  runState(
    fullySolveFlowTypes(map((.prod), graphs)),
    (directBuildTree(map(prodGraphToEnv, graphs)), ntEnv)).1;

type InferState = State<(EnvTree<ProductionGraph>, EnvTree<FlowType>) _>;

{--
 - Produces flow types for every nonterminal.
 - Iterates until convergence.
 -}
fun fullySolveFlowTypes InferState<()> ::= prods::[ProdName] = do {
  -- Update the flow types from all the initial production graphs
  traverse_(updateFlowType, prods);

  -- Just iterate until no new edges are added
  doWhile_(
    map(any, traverseA(
      \ prod::ProdName -> do {
        -- Update the production graph
        graphUpdated :: Boolean <- updateProdGraph(prod);

        -- Only update the flow types for the prod's NT if the prod graph changed
        when_(graphUpdated, updateFlowType(prod));
        return graphUpdated;
      },
      prods)));
};

{--
 - Update a production graph using the current flow types.
 -}
production updateProdGraph
top::InferState<Boolean> ::= prod::ProdName
{
  local graph :: ProductionGraph = findProductionGraph(prod, top.stateIn.1);
  local updatedGraph :: Maybe<ProductionGraph> =
    updateGraph(graph, top.stateIn.1, top.stateIn.2);
  top.stateOut =
    case updatedGraph of
    | just(g) -> (rtm:update(prod, [g], top.stateIn.1), top.stateIn.2)
    | nothing() -> top.stateIn
    end;
  top.stateVal = updatedGraph.isJust;
}

{--
 - Update flow types for a nonterminal based on a single production graph.
 -}
production updateFlowType
top::InferState<()> ::= prod::ProdName
{
  local graph :: ProductionGraph = findProductionGraph(prod, top.stateIn.1);
  local currentFlowType :: FlowType = findFlowType(graph.lhsNt, top.stateIn.2);
  local newFlowType :: FlowType = g:add(
    flatMap(expandVertexFilterTo(_, graph), graph.flowTypeVertexes),
    currentFlowType);
  top.stateOut = (top.stateIn.1, rtm:update(graph.lhsNt, [newFlowType], top.stateIn.2));
  top.stateVal = ();
}

-- Expand 'ver' using 'graph', then filter down to just those in 'inhs'
fun expandVertexFilterTo [(String, String)] ::= ver::FlowVertex  graph::ProductionGraph =
  map(pair(fst=ver.flowTypeName, snd=_),
    filterLhsInh(set:toList(graph.edgeMap(ver))));

{--
 - Filters vertexes down to just the names of inherited attributes on the LHS
 -}
global filterLhsInh :: ([String] ::= [FlowVertex]) = flatMap(collectInhs, _);

{--
 - Used to filter down to just the inherited attributes (on the LHS)
 - 
 - @param f  The flow vertex in question
 - @return  {f} if f is an LHS Inh vertex, otherwise {}
 -}
fun collectInhs [String] ::= f::FlowVertex =
  case f of
  | lhsInhVertex(a) -> [a]
  | _ -> []
  end;


{--
 - Flow type lookup names for vertices
 -}
synthesized attribute flowTypeName :: String occurs on FlowVertex;

aspect production lhsSynVertex
top::FlowVertex ::= attrName::String
{
  top.flowTypeName = attrName;
}
aspect production lhsInhVertex
top::FlowVertex ::= attrName::String
{
  top.flowTypeName = error("Internal compiler error: shouldn't be solving flow types for inherited attributes?");
}
aspect production rhsSynVertex
top::FlowVertex ::= sigName::String  attrName::String
{
  top.flowTypeName = error("Internal compiler error: shouldn't be solving flow types for child synthesized attributes?");
}
aspect production rhsInhVertex
top::FlowVertex ::= sigName::String  attrName::String
{
  top.flowTypeName = error("Internal compiler error: shouldn't be solving flow types for child inherited attributes?");
}
aspect production localEqVertex
top::FlowVertex ::= fName::String
{
  top.flowTypeName = fName; -- secretly only ever "forward" when we actually demand flowTypeName
}
aspect production localSynVertex
top::FlowVertex ::= fName::String  attrName::String
{
  top.flowTypeName = error("Internal compiler error: shouldn't be solving flow types for local synthesized attributes?");
}
aspect production localInhVertex
top::FlowVertex ::= fName::String  attrName::String
{
  top.flowTypeName = error("Internal compiler error: shouldn't be solving flow types for local inherited attributes?");
}
aspect production anonEqVertex
top::FlowVertex ::= fName::String
{
  top.flowTypeName = error("Internal compiler error: shouldn't be solving flow types for anon equations?");
}
aspect production anonSynVertex
top::FlowVertex ::= fName::String  attrName::String
{
  top.flowTypeName = error("Internal compiler error: shouldn't be solving flow types for anon synthesized attributes?");
}
aspect production anonInhVertex
top::FlowVertex ::= fName::String  attrName::String
{
  top.flowTypeName = error("Internal compiler error: shouldn't be solving flow types for anon inherited attributes?");
}
aspect production subtermSynVertex
top::FlowVertex ::= parent::VertexType prodName::String sigName::String  attrName::String
{
  top.flowTypeName = error("Internal compiler error: shouldn't be solving flow types for subterm synthesized attributes?");
}
aspect production subtermInhVertex
top::FlowVertex ::= parent::VertexType prodName::String sigName::String  attrName::String
{
  top.flowTypeName = error("Internal compiler error: shouldn't be solving flow types for subterm inherited attributes?");
}
