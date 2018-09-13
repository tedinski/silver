grammar silver:driver:util;

import silver:definition:core only jarName;

nonterminal Compilation with config, postOps, grammarList, recheckGrammars, allGrammars;

flowtype postOps {config} on Compilation;

synthesized attribute postOps :: [DriverAction] with ++;
synthesized attribute grammarList :: [Decorated RootSpec];
synthesized attribute recheckGrammars :: [String];
-- This is used on the outside, e.g. the ide functions.
synthesized attribute allGrammars :: [Decorated RootSpec];

{--
 - This abstractly represents a compilation.
 - Note, in particular, that this does not *DO* any IO at all itself.
 -
 - However, it does expect some "flow":
 -  * 'g' should be examined, and then 'top.recheckGrammars' used to provide 'r'
 -
 - @param g  A list of grammar initially read in
 - @param r  A list of grammars that we re-compiled, due to dirtiness in 'g'
 - @param buildGrammar  The initial grammar requested built
 - @param silverHome  The home location of Silver
 - @param silverGen  The directory to store generated files
 -}
abstract production compilation
top::Compilation ::= g::Grammars  r::Grammars  buildGrammar::String  benv::BuildEnv
{
  -- the list of rootspecs coming out of g
  top.grammarList = g.grammarList;
  -- the list of grammars that should be re-checked
  top.recheckGrammars = g.recheckGrammars;
  
  g.compiledGrammars = directBuildTree(map(grammarPairing, g.grammarList));
  -- However, we are then forced to use the interface files that we are going to
  -- recheck in the .compiledGrammars for the recheck.
  -- That means they don't see "themselves" but their previous interface file.
  r.compiledGrammars = g.compiledGrammars;
  -- This *should* be okay, because the information should be identical in both.
  
  -- This determines what is actually needed in this build.
  -- For example, it excludes "options" and conditional builds that aren't
  -- actually used / triggered.
  production grammarsDependedUpon :: [String] =
    expandAllDeps([buildGrammar], [], g.compiledGrammars);
  
  -- Ditto the above, but rootspecs
  production grammarsRelevant :: [Decorated RootSpec] =
    keepGrammars(grammarsDependedUpon, g.grammarList);
  
  -- JUST the grammars read from source, that are relevant, ignoring rechecked grammars
  production grammarsToTranslate :: [Decorated RootSpec] =
    keepGrammars(grammarsDependedUpon, g.translateGrammars);
  
  top.allGrammars = g.grammarList ++ r.grammarList;

  top.postOps := [];
}

nonterminal Grammars with config, compiledGrammars, productionFlowGraphs, grammarFlowTypes, grammarList, recheckGrammars, translateGrammars, jarName;

abstract production consGrammars
top::Grammars ::= h::RootSpec  t::Grammars
{
  top.grammarList = h :: t.grammarList;
  top.recheckGrammars = h.recheckGrammars ++ t.recheckGrammars;
  top.translateGrammars = h.translateGrammars ++ t.translateGrammars;
  top.jarName = orElse(h.jarName, t.jarName);
}

abstract production nilGrammars
top::Grammars ::=
{
  top.grammarList = [];
  top.recheckGrammars = [];
  top.translateGrammars = [];
  top.jarName = nothing();
}

{--
 - Returns a pair, suitable for building an environment
 -}
function grammarPairing
Pair<String Decorated RootSpec> ::= r::Decorated RootSpec
{
  return pair(r.declaredName, r);
}

{--
 - Keep only a selected set of grammars.
 - @param keep  The set of grammars to keep
 - @param d  The list of grammars to filter
 -}
function keepGrammars
[Decorated RootSpec] ::= keep::[String] d::[Decorated RootSpec]
{
  return if null(d) then [] else (if contains(head(d).declaredName, keep) then [head(d)] else []) ++ keepGrammars(keep, tail(d));
}

