grammar silver:compiler:definition:core;

{--
 - Root represents one textual file of Silver source.
 -}
tracked nonterminal Root with
  -- Global-level inherited attributes
  config, compiledGrammars,
  -- Grammar-level inherited attributes
  grammarName, env, globalImports, grammarDependencies,
  -- File-level inherited attributes
  -- Synthesized attributes
  declaredName, unparse, errors, defs, occursDefs, moduleNames, importedDefs, importedOccursDefs,
  exportedGrammars, optionalGrammars, condBuild, jarName;

flowtype Root = decorate {config, compiledGrammars, grammarName, env, globalImports, grammarDependencies, flowEnv};

tracked nonterminal GrammarDcl with 
  declaredName, grammarName, unparse, errors;

propagate errors on Root, GrammarDcl;
propagate config, compiledGrammars, grammarName, globalImports, grammarDependencies, moduleNames on Root;

concrete production root
top::Root ::= gdcl::GrammarDcl ms::ModuleStmts ims::ImportStmts ags::AGDcls
{
  top.unparse = gdcl.unparse ++ "\n\n" ++ ms.unparse ++ "\n\n" ++ ims.unparse ++ "\n\n" ++ ags.unparse;
  top.declaredName = gdcl.declaredName;

  top.defs := ags.defs;
  top.occursDefs := ags.occursDefs;

  top.importedDefs := ms.defs;
  top.importedOccursDefs := ms.occursDefs;
  top.exportedGrammars := ms.exportedGrammars;
  top.optionalGrammars := ms.optionalGrammars;
  top.condBuild := ms.condBuild;
  top.jarName := ags.jarName;
  
  -- We have an mismatch in how the environment gets put together:
  --  Outermost, we have grammar-wide imports in one scope.  That's top.globalImports here.
  --  THEN, we have this particular file's list of local imports. That's ims.defs here.
  --  THEN, we have the grammar-wide definitions, from the whole grammr. That's top.env here.
  -- So we're kind of injecting local imports in between two grammar-wide things there.
  ags.env = appendEnv(top.env, newScopeEnv(ims.defs, occursEnv(ims.occursDefs, top.globalImports)));
}

concrete production noGrammarDcl
top::GrammarDcl ::=
{
  top.unparse = "";
  top.declaredName = top.grammarName;
}

concrete production grammarDcl_c
top::GrammarDcl ::= 'grammar' qn::QName ';'
{
  top.unparse = "grammar " ++ qn.unparse ++ ";";

  top.declaredName = qn.name;
  top.errors <-
    if qn.name == top.grammarName then []
    else [errFromOrigin(top, "Grammar declaration is incorrect: " ++ qn.name)];
} action {
  insert semantic token IdGrammarName_t at qn.nameLoc;
}

