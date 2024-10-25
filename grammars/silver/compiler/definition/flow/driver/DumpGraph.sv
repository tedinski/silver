grammar silver:compiler:definition:flow:driver;

import silver:compiler:driver;
import silver:util:cmdargs;
import silver:util:treemap as rtm;

-- This isn't exactly a warning, but it can live here for now...

synthesized attribute dumpFlowGraph :: Boolean occurs on CmdArgs;

aspect production endCmdArgs
top::CmdArgs ::= _
{
  top.dumpFlowGraph = false;
}
abstract production dumpFlowGraphFlag
top::CmdArgs ::= rest::CmdArgs
{
  top.dumpFlowGraph = true;
  forwards to @rest;
}
aspect function parseArgs
Either<String  Decorated CmdArgs> ::= args::[String]
{
  flags <- [ flagSpec(name="--dump-flow-graph", paramString=nothing(),
               help="write the flowtypes out to several Graphviz files",
               flagParser=flag(dumpFlowGraphFlag))
             -- Ted mistyped this a lot.
           , flagSpec(name="--dump-flow-graphs", paramString=nothing(),
               help="a typo of --dump-flow-graph",
               flagParser=flag(dumpFlowGraphFlag))
           ];
  -- not omitting descriptions deliberately!
}

aspect production compilation
top::Compilation ::= g::Grammars  _  _  a::Decorated CmdArgs  benv::BuildEnv
{
  top.postOps <-
    if a.dumpFlowGraph
    then [dumpFlowGraphAction(prodGraph, rtm:values(finalGraphEnv), unList(rtm:toList(flowTypes)))]
    else [];
}

-- Coalesce sequences of pairs with the same key
-- e.g. "ab,ac,ad,bc,bd -> a[bcd],b[cd]"
function unList
[Pair<String [b]>] ::= l::[Pair<String b>]
{
  local recurse :: [Pair<String [b]>] = unList(tail(l));
  
  return if null(l) then
    []
  else if !null(recurse) && head(recurse).fst == head(l).fst then
    (head(l).fst, head(l).snd :: head(recurse).snd) :: tail(recurse)
  else
    (head(l).fst, [head(l).snd]) :: recurse;
}



abstract production dumpFlowGraphAction
top::DriverAction ::= prodGraph::[ProductionGraph]  finalGraph::[ProductionGraph]  flowTypes::[Pair<String [FlowType]>]
{
  top.run = do {
    eprintln("Generating flow graphs");
    writeFile("flow-deps-transitive.dot", "digraph flow {\n" ++ generateDotGraph(finalGraph) ++ "}");
    writeFile("flow-deps-direct.dot", "digraph flow {\n" ++ generateDotGraph(prodGraph) ++ "}");
    writeFile("flow-types.dot", "digraph flow {\n" ++ generateFlowDotGraph(flowTypes) ++ "}");
    return 0;
  };

  top.order = 0;
}


function generateFlowDotGraph
String ::= flowTypes::[Pair<String [FlowType]>]
{
  local nt::String = head(flowTypes).fst;
  local edges::[Pair<String String>] = g:toList(head(head(flowTypes).snd));
  
  return if null(flowTypes) then ""
  else "subgraph \"cluster:" ++ nt ++ "\" {\nlabel=\"" ++ substring(lastIndexOf(":", nt) + 1, length(nt), nt) ++ "\";\n" ++ 
       implode("", map(makeLabelDcls(nt, _), nub(expandLabels(edges)))) ++
       implode("", map(makeNtFlow(nt, _), edges)) ++
       "}\n" ++
       generateFlowDotGraph(tail(flowTypes));
}

fun expandLabels [String] ::= l::[Pair<String String>] =
  if null(l) then [] else head(l).fst :: head(l).snd :: expandLabels(tail(l));
function makeLabelDcls
String ::= nt::String  attr::String
{
  local a :: String = substring(lastIndexOf(":", attr) + 1, length(attr), attr);
  return "\"" ++ nt ++ "/" ++ attr ++ "\"[label=\"" ++ a ++ "\"];\n";
}
fun makeNtFlow String ::= nt::String  e::Pair<String String> =
  "\"" ++ nt ++ "/" ++ e.fst ++ "\" -> \"" ++ nt ++ "/" ++ e.snd ++ "\";\n";

fun generateDotGraph String ::= specs::[ProductionGraph] =
  case specs of
  | [] -> ""
  | productionGraph(prod, _, _, graph, suspect, _) :: t ->
      "subgraph \"cluster:" ++ prod ++ "\" {\n" ++ 
      implode("", map(makeDotArrow(prod, _, ""), g:toList(graph))) ++
      implode("", map(makeDotArrow(prod, _, " [style=dotted]"), suspect)) ++
      "}\n" ++
      generateDotGraph(t)
  end;

-- "production/flowvertex" -> "production/flowvertex"
fun makeDotArrow String ::= p::String e::(FlowVertex, FlowVertex) style::String =
  "\"" ++ p ++ "/" ++ e.fst.dotName ++ "\" -> \"" ++ p ++ "/" ++ e.snd.dotName ++ "\"" ++ style ++ ";\n";



{--
 - DOT graph names for vertices in the production flow graphs
 -}
synthesized attribute dotName :: String occurs on FlowVertex;

aspect production lhsSynVertex
top::FlowVertex ::= attrName::String
{
  top.dotName = attrName;
}
aspect production lhsInhVertex
top::FlowVertex ::= attrName::String
{
  top.dotName = attrName;
}
aspect production rhsSynVertex
top::FlowVertex ::= sigName::String  attrName::String
{
  top.dotName = sigName ++ "/" ++ attrName;
}
aspect production rhsInhVertex
top::FlowVertex ::= sigName::String  attrName::String
{
  top.dotName = sigName ++ "/" ++ attrName;
}
aspect production localEqVertex
top::FlowVertex ::= fName::String
{
  top.dotName = fName;
}
aspect production localSynVertex
top::FlowVertex ::= fName::String  attrName::String
{
  top.dotName = fName ++ "/" ++ attrName;
}
aspect production localInhVertex
top::FlowVertex ::= fName::String  attrName::String
{
  top.dotName = fName ++ "/" ++ attrName;
}
aspect production anonEqVertex
top::FlowVertex ::= fName::String
{
  top.dotName = fName;
}
aspect production anonSynVertex
top::FlowVertex ::= fName::String  attrName::String
{
  top.dotName = fName ++ "/" ++ attrName;
}
aspect production anonInhVertex
top::FlowVertex ::= fName::String  attrName::String
{
  top.dotName = fName ++ "/" ++ attrName;
}
aspect production subtermSynVertex
top::FlowVertex ::= parent::VertexType prodName::String sigName::String  attrName::String
{
  top.dotName = parent.synVertex(prodName ++ "@" ++ sigName ++ "/" ++ attrName).dotName;  -- Hack!
}
aspect production subtermInhVertex
top::FlowVertex ::= parent::VertexType prodName::String sigName::String  attrName::String
{
  top.dotName = parent.inhVertex(prodName ++ "@" ++ sigName ++ "/" ++ attrName).dotName;  -- Hack!
}



