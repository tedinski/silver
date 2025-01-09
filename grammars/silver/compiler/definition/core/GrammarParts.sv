grammar silver:compiler:definition:core;

nonterminal Grammar with
  -- Global inherited attributes
  config, compiledGrammars, productionFlowGraphs, grammarFlowTypes,
  -- Grammar inherited attributes
  grammarName, env, globalImports, grammarDependencies,
  -- Synthesized attributes
  declaredName, moduleNames, exportedGrammars, optionalGrammars, condBuild,
  defs, occursDefs, importedDefs, importedOccursDefs, allFileErrors, jarName;

flowtype Grammar = decorate {config, compiledGrammars, productionFlowGraphs, grammarFlowTypes, grammarName, env, flowEnv, globalImports, grammarDependencies};

{--
- A list of grammars that this grammar depends upon,
- directly or indirectly. (i.e. based on other grammar's exports)
- NOT including options.
-}
inherited attribute grammarDependencies :: [String];
{--
 - Grammar-wide imports definitions.  Exists because we need to place
 - a file's individual imports between grammar definitions and grammar
 - wide imports.
 -}
inherited attribute globalImports :: Env;
{--
 - The definitions resulting from grammar-wide imports definitions.
 - At the top of a grammar, these are echoed down as globalImports
 -}
monoid attribute importedDefs :: [Def];
monoid attribute importedOccursDefs :: [OccursDclInfo];
{--
 - An overall listing of error messages for a grammar
 -}
synthesized attribute grammarErrors :: [Pair<String [Message]>];
{--
 - All files in a grammar, paired with their error messages.
 -}
synthesized attribute allFileErrors :: [Pair<String [Message]>];

propagate
    config, compiledGrammars, productionFlowGraphs, grammarFlowTypes,
    grammarName, env, globalImports, grammarDependencies,
    moduleNames, exportedGrammars, optionalGrammars, condBuild, defs,
    occursDefs, importedDefs, importedOccursDefs, jarName
  on Grammar;

abstract production nilGrammar
top::Grammar ::=
{
  -- A value here is actually used. Grammars without any .sv files
  -- turn into this, and this "aren't found". TODO verify this is true?
  top.declaredName = ":null";
  top.allFileErrors = [];
}

abstract production consGrammar
top::Grammar ::= h::File  t::Grammar
{
  top.declaredName = if h.declaredName == t.declaredName then h.declaredName else top.grammarName;

  production attribute fileErrors::[Message] with ++;
  fileErrors := h.errors;
  top.allFileErrors = (getParsedOriginLocation(h).fromJust.filename, fileErrors) :: t.allFileErrors;

  fileErrors <- attachNote logicalLocationFromOrigin(h) on
    warnIfMultJarName(h.jarName, t.jarName)
  end;
}
