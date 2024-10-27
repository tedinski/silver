grammar silver:compiler:analysis:warnings:exporting;

import silver:compiler:driver;
import silver:util:cmdargs;

import silver:compiler:definition:core;
import silver:compiler:definition:env;

-- This isn't exactly a warning, but it can live here for now...

synthesized attribute dumpDepGraph :: Boolean occurs on CmdArgs;
synthesized attribute dumpExportGraph :: Boolean occurs on CmdArgs;

aspect production endCmdArgs
top::CmdArgs ::= _
{
  top.dumpDepGraph = false;
  top.dumpExportGraph = false;
}
abstract production dumpDepGraphFlag
top::CmdArgs ::= rest::CmdArgs
{
  top.dumpDepGraph = true;
  forwards to @rest;
}
abstract production dumpExportGraphFlag
top::CmdArgs ::= rest::CmdArgs
{
  top.dumpExportGraph = true;
  forwards to @rest;
}
aspect function parseArgs
Either<String  Decorated CmdArgs> ::= args::[String]
{
  flags <- [
    flagSpec(name="--dump-import-graph", paramString=nothing(),
      help="dump a graph of dependencies between grammars as a Graphviz file",
      flagParser=flag(dumpDepGraphFlag))];
  flags <- [
    flagSpec(name="--dump-export-graph", paramString=nothing(),
      help="dump a graph of exports between grammars as a Graphviz file",
      flagParser=flag(dumpExportGraphFlag))];
  -- not omitting from descriptions deliberately!
}
aspect production compilation
top::Compilation ::= g::Grammars  _  _  a::Decorated CmdArgs  benv::BuildEnv
{
  top.postOps <- if a.dumpDepGraph then [dumpDepGraphAction(g.grammarList)] else [];
  top.postOps <- if a.dumpExportGraph then [dumpExportGraphAction(g.grammarList)] else [];
}

abstract production dumpDepGraphAction
top::DriverAction ::= specs::[Decorated RootSpec]
{
  top.run = do {
    eprintln("Generating import graph");
    writeFile("deps.dot", "digraph deps {\n" ++ generateDotGraph(specs) ++ "}");
    return 0;
  };

  top.order = 0;
}

abstract production dumpExportGraphAction
top::DriverAction ::= specs::[Decorated RootSpec]
{
  top.run = do {
    eprintln("Generating export graph");
    writeFile("exports.dot", "digraph exports {\n" ++ generateDotExportGraph(specs) ++ "}");
    return 0;
  };

  top.order = 0;
}

fun generateDotGraph String ::= specs::[Decorated RootSpec] =
  case specs of
  | [] -> ""
  | h::t ->
      "\"" ++ h.declaredName ++ "\"[label=\"" ++ h.declaredName ++ "\"];\n" ++
      implode("", map(makeDotArrow(h.declaredName, _), h.moduleNames)) ++
      generateDotGraph(t)
  end;

fun generateDotExportGraph String ::= specs::[Decorated RootSpec] =
  case specs of
  | [] -> ""
  | h::t ->
      "\"" ++ h.declaredName ++ "\"[label=\"" ++ h.declaredName ++ "\"];\n" ++
      implode("", map(makeDotArrow(h.declaredName, _), computeOptionalDeps([h.declaredName], h.compiledGrammars))) ++
      generateDotExportGraph(t)
  end;

fun makeDotArrow String ::= f::String t::String =
  if t == "silver:core" then "" 
  else "\"" ++ f ++ "\" -> \"" ++ t ++ "\";\n";

