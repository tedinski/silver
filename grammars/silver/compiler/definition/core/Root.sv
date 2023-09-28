grammar silver:compiler:definition:core;

{--
 - Root represents one textual file of Silver source.
 -}
nonterminal Root with
  -- Global-level inherited attributes
  config, compiledGrammars,
  -- Grammar-level inherited attributes
  grammarName, env, globalImports, grammarDependencies,
  -- File-level inherited attributes
  -- Synthesized attributes
  declaredName, unparse, location, errors, defs, occursDefs, moduleNames, importedDefs, importedOccursDefs,
  exportedGrammars, optionalGrammars, condBuild, jarName;

flowtype Root = decorate {config, compiledGrammars, grammarName, env, globalImports, grammarDependencies, flowEnv};

nonterminal GrammarDcl with 
  declaredName, grammarName, location, unparse, errors;

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

  -- See https://github.com/melt-umn/silver/issues/444.
  -- An explicit file-scope import of silver:core would cause silver:core to not get implicitly imported
  -- for the whole grammar, but since it is file scope silver:core wouldn't be visible in other files.
  -- This behaviour is unintuitative, and the user probably meant to write a grammar-scope import hiding
  -- or renaming something - so raise an error in this case.
  top.errors <-
    if contains("silver:core", ims.moduleNames)
    then [err(ims.location, "File-scope import of silver:core is non supported. Did you mean 'imports silver:core ...;'?")]
    else [];
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
    else [err(top.location, "Grammar declaration is incorrect: " ++ qn.name)];
} action {
  insert semantic token IdGrammarName_t at qn.baseNameLoc;
}

