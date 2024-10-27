grammar silver:compiler:definition:core;

imports silver:compiler:driver:util;

tracked nonterminal ModuleStmts with config, grammarName, unparse, errors, moduleNames, defs, occursDefs, exportedGrammars, optionalGrammars, condBuild, compiledGrammars, grammarDependencies;
tracked nonterminal ModuleStmt with config, grammarName, unparse, errors, moduleNames, defs, occursDefs, exportedGrammars, optionalGrammars, condBuild, compiledGrammars, grammarDependencies;

tracked nonterminal ImportStmt with config, grammarName, unparse, errors, moduleNames, defs, occursDefs, compiledGrammars, grammarDependencies;
tracked nonterminal ImportStmts with config, grammarName, unparse, errors, moduleNames, defs, occursDefs, compiledGrammars, grammarDependencies;

tracked nonterminal ModuleExpr with config, grammarName, unparse, errors, moduleNames, defs, occursDefs, compiledGrammars, grammarDependencies;
tracked nonterminal ModuleName with config, grammarName, unparse, errors, moduleNames, defs, occursDefs, compiledGrammars, grammarDependencies;

tracked nonterminal NameList with config, grammarName, unparse, names, env;

tracked nonterminal WithElems with config, grammarName, unparse, envMaps;
tracked nonterminal WithElem with config, grammarName, unparse, envMaps;

propagate config, grammarName, errors, moduleNames, defs, occursDefs, compiledGrammars, grammarDependencies
  on ModuleStmts, ModuleStmt, ImportStmt, ImportStmts;
propagate exportedGrammars, optionalGrammars, condBuild on ModuleStmts;
propagate env on NameList;

{--
 - A list of QName strings. Used for 'only' and 'hiding'.
 -}
synthesized attribute names :: [String];
{--
 - A renaming mapping used for 'with'.
 -}
synthesized attribute envMaps :: [Pair<String String>];

-- TODO: eliminate, fold into ModuleName, make filter parameters inh attrs.
tracked nonterminal Module with defs, occursDefs, errors;

abstract production module 
top::Module ::= need::[String]
                seen::[String]
                compiledGrammars::EnvTree<Decorated RootSpec>
                grammarDependencies::[String]
                asPrepend::String
                onlyFilter::Maybe<[String]>
                hidingFilter::[String]
                withRenames::[Pair<String String>]
{
  -- TODO: the use of 'seen' below is a not fully fleshed out.
  -- what we really need is some way to eliminate duplicate imports.
  production med :: ModuleExportedDefs =
    moduleExportedDefs(compiledGrammars, grammarDependencies, need, seen);
  
  local defs :: Defs = foldr(consDefs, nilDefs(), med.defs);
  defs.filterItems = onlyFilter.fromJust;

  local defs_after_only :: Defs =
    if !onlyFilter.isJust then ^defs else defs.filterOnly;
  defs_after_only.filterItems = hidingFilter;

  local defs_after_hiding :: Defs =
    if null(hidingFilter) then ^defs_after_only else defs_after_only.filterHiding;
  defs_after_hiding.withRenames = withRenames;

  local defs_after_renames :: Defs =
    if null(withRenames) then ^defs_after_hiding else defs_after_hiding.renamed;
  defs_after_renames.pfx = asPrepend ++ ":";

  local defs_after_prepend :: Defs =
    if asPrepend == "" then ^defs_after_renames else defs_after_renames.prepended;

  top.defs := defs_after_prepend.defs;
  top.occursDefs := med.occursDefs;
  top.errors := med.errors;
}

-- recurses through exportedGrammars, grabbing all definitions
tracked nonterminal ModuleExportedDefs with defs, occursDefs, errors;

{--
 - Computes the set of defs we get from an import
 - @param compiledGrammars  Way to look up modules by name
 - @param grammarDependencies  All imports of this grammar, closed over exports and triggers already.
 - @param need  List of grammars we need to find and include in 'defs'.
 - @param seen  List of grammars we have already emitted as 'defs'.
 -        (ALWAYS INITIALLY the importing grammar.)
 -}
abstract production moduleExportedDefs
top::ModuleExportedDefs ::= compiledGrammars::EnvTree<Decorated RootSpec> grammarDependencies::[String] need::[String] seen::[String]
{
  production recurse :: ModuleExportedDefs =
    moduleExportedDefs(compiledGrammars, grammarDependencies, new_need, new_seen);
  
  local gram :: String = head(need);
  production rs :: [Decorated RootSpec] = searchEnvTree(gram, compiledGrammars);

  local new_seen :: [String] = gram :: seen;

  -- We need to find everything the grammars exports and all triggered stuff, too
  local add_to_need :: [String] =
    head(rs).exportedGrammars ++ triggeredGrammars(grammarDependencies, head(rs).condBuild);
  
  -- ... but only if we haven't already added this.
  local new_need :: [String] =
    if null(rs) then tail(need)
    else removeAll(new_seen, nub(tail(need) ++ add_to_need));
  
  top.defs :=
    if null(need) then [] else
    if null(rs) then recurse.defs else head(rs).defs ++ recurse.defs;
  top.occursDefs :=
    if null(need) then [] else
    if null(rs) then recurse.occursDefs else head(rs).occursDefs ++ recurse.occursDefs;
  top.errors :=
    if null(need) then [] else 
    if null(rs) then [errFromOrigin(ambientOrigin(), "Grammar '" ++ gram ++ "' cannot be found.")] ++ recurse.errors else recurse.errors;
}

fun triggeredGrammars [String] ::= grammarDependencies::[String]  trig::[[String]] =
  if null(trig) then
    []
  else if contains(head(tail(head(trig))), grammarDependencies) then 
    head(head(trig)) :: triggeredGrammars(grammarDependencies, tail(trig))
  else
    triggeredGrammars(grammarDependencies, tail(trig));

--------------
-- ImportStmts

concrete production importStmt
top::ImportStmt ::= 'import' m::ModuleExpr ';'
{
  top.unparse = "import " ++ m.unparse ++ ";";

  -- See https://github.com/melt-umn/silver/issues/444.
  -- An explicit file-scope import of silver:core would cause silver:core to not get implicitly imported
  -- for the whole grammar, but since it is file scope silver:core wouldn't be visible in other files.
  -- This behaviour is unintuitative, and the user probably meant to write a grammar-scope import hiding
  -- or renaming something - so raise an error in this case.
  top.errors <-
    if contains("silver:core", m.moduleNames)
    then [errFromOrigin(top, "File-scope import of silver:core is non supported. Did you mean 'imports silver:core ...;'?")]
    else [];
}

concrete production nilImportStmts
top::ImportStmts ::=
{
  top.unparse = "";
}

concrete production consImportStmts
top::ImportStmts ::= h::ImportStmt t::ImportStmts
{
  top.unparse = h.unparse ++ "\n" ++ t.unparse;
}

abstract production appendImportStmts
top::ImportStmts ::= h::ImportStmts t::ImportStmts
{
  top.unparse = h.unparse ++ "\n" ++ t.unparse;
}

--------------
-- ModuleStmts

concrete production nilModuleStmts 
top::ModuleStmts ::=
{
  top.unparse = "";
}

concrete production consModulesStmts
top::ModuleStmts ::= h::ModuleStmt t::ModuleStmts
{
  top.unparse = h.unparse ++ "\n" ++ t.unparse;
}

concrete production importsStmt
top::ModuleStmt ::= 'imports' m::ModuleExpr ';'
{
  top.unparse = "imports " ++ m.unparse ++ ";";

  top.exportedGrammars := [];
  top.optionalGrammars := [];
  top.condBuild := [];
}

concrete production exportsStmt
top::ModuleStmt ::= 'exports' m::ModuleName ';'
{
  top.unparse = "exports " ++ m.unparse ++ ";";

  top.exportedGrammars := m.moduleNames;
  top.optionalGrammars := [];
  top.condBuild := [];
}

concrete production exportsWithStmt
top::ModuleStmt ::= 'exports' m::QName 'with' c::QName ';'
{
  top.unparse = "exports " ++ m.unparse ++ " with " ++ c.unparse ++ ";";
  
  top.errors <-
    if !null(searchEnvTree(m.name, top.compiledGrammars)) then []
    else [errFromOrigin(m, "Grammar '" ++ m.name ++ "' cannot be found.")];

  top.errors <-
    if !null(searchEnvTree(c.name, top.compiledGrammars)) then []
    else [errFromOrigin(c, "Grammar '" ++ c.name ++ "' cannot be found.")];

  top.exportedGrammars := [];
  top.optionalGrammars := [];
  top.condBuild := [[m.name, c.name]];
} action {
  insert semantic token IdGrammarName_t at m.nameLoc;
  insert semantic token IdGrammarName_t at c.nameLoc;
}
concrete production optionalStmt
top::ModuleStmt ::= 'option' m::QName ';'
{
  top.unparse = "option " ++ m.unparse ++ ";";

  top.errors <-
    if !null(searchEnvTree(m.name, top.compiledGrammars)) then []
    else [errFromOrigin(m, "Grammar '" ++ m.name ++ "' cannot be found.")];

  top.exportedGrammars := [];
  top.optionalGrammars := [m.name];
  top.condBuild := [];
} action {
  insert semantic token IdGrammarName_t at m.nameLoc;
}
  

-----------------------
-- ModuleName

concrete production moduleName
top::ModuleName ::= pkg::QName
{
  top.unparse = pkg.unparse;
  top.moduleNames := [pkg.name];

  production attribute m :: Module;
  m = module([pkg.name], [top.grammarName], top.compiledGrammars, top.grammarDependencies, "", nothing(), [], []);
  
  top.errors := m.errors;
  top.defs := m.defs;
  top.occursDefs := m.occursDefs;
} action {
  insert semantic token IdGrammarName_t at pkg.nameLoc;
}

-----------------------
-- ModuleExpr

concrete production moduleAll
top::ModuleExpr ::= pkg::QName
{
  top.unparse = pkg.unparse;
  top.moduleNames := [pkg.name];

  production attribute m :: Module;
  m = module([pkg.name], [top.grammarName], top.compiledGrammars, top.grammarDependencies, "", nothing(), [], []);
  
  top.errors := m.errors;
  top.defs := m.defs;
  top.occursDefs := m.occursDefs;
} action {
  insert semantic token IdGrammarName_t at pkg.nameLoc;
}

concrete production moduleAllWith
top::ModuleExpr ::= pkg::QName 'with' wc::WithElems
{
  top.unparse = pkg.unparse ++ " with " ++ wc.unparse;
  top.moduleNames := [pkg.name];

  production attribute m :: Module;
  m = module([pkg.name], [top.grammarName], top.compiledGrammars, top.grammarDependencies, "", nothing(), [], wc.envMaps);
  
  top.errors := m.errors;
  top.defs := m.defs;
  top.occursDefs := m.occursDefs;
} action {
  insert semantic token IdGrammarName_t at pkg.nameLoc;
}

concrete production moduleOnly
top::ModuleExpr ::= pkg::QName 'only' ns::NameList
{
  top.unparse = pkg.unparse ++ " only " ++ ns.unparse;
  top.moduleNames := [pkg.name];

  production attribute m :: Module;
  m = module([pkg.name], [top.grammarName], top.compiledGrammars, top.grammarDependencies, "", just(ns.names), [], []);
  
  top.errors := m.errors;
  top.defs := m.defs;
  top.occursDefs := m.occursDefs;
} action {
  insert semantic token IdGrammarName_t at pkg.nameLoc;
}

concrete production moduleOnlyNothing
top::ModuleExpr ::= pkg::QName 'only'
{
  top.unparse = pkg.unparse ++ " only ";
  top.moduleNames := [pkg.name];

  production attribute m :: Module;
  m = module([pkg.name], [top.grammarName], top.compiledGrammars, top.grammarDependencies, "", just([]), [], []);
  
  top.errors := m.errors;
  top.defs := m.defs;
  top.occursDefs := m.occursDefs;
} action {
  insert semantic token IdGrammarName_t at pkg.nameLoc;
}

concrete production moduleOnlyWith
top::ModuleExpr ::= pkg::QName 'only' ns::NameList 'with' wc::WithElems
{
  top.unparse = pkg.unparse ++ " only " ++ ns.unparse ++ " with " ++ wc.unparse;
  top.moduleNames := [pkg.name];

  production attribute m :: Module;
  m = module([pkg.name], [top.grammarName], top.compiledGrammars, top.grammarDependencies, "", just(ns.names), [], wc.envMaps);
  
  top.errors := m.errors;
  top.defs := m.defs;
  top.occursDefs := m.occursDefs;
} action {
  insert semantic token IdGrammarName_t at pkg.nameLoc;
}

concrete production moduleHiding
top::ModuleExpr ::= pkg::QName 'hiding' ns::NameList
{
  top.unparse = pkg.unparse ++ " hiding " ++ ns.unparse;
  top.moduleNames := [pkg.name];

  production attribute m :: Module;
  m = module([pkg.name], [top.grammarName], top.compiledGrammars, top.grammarDependencies, "", nothing(), ns.names, []);
  
  top.errors := m.errors;
  top.defs := m.defs;
  top.occursDefs := m.occursDefs;
} action {
  insert semantic token IdGrammarName_t at pkg.nameLoc;
}

concrete production moduleHidingWith
top::ModuleExpr ::= pkg::QName 'hiding' ns::NameList 'with' wc::WithElems
{
  top.unparse = pkg.unparse ++ " hiding " ++ ns.unparse ++ " with " ++ wc.unparse;
  top.moduleNames := [pkg.name];

  production attribute m :: Module;
  m = module([pkg.name], [top.grammarName], top.compiledGrammars, top.grammarDependencies, "", nothing(), ns.names, wc.envMaps);
  
  top.errors := m.errors;
  top.defs := m.defs;
  top.occursDefs := m.occursDefs;
} action {
  insert semantic token IdGrammarName_t at pkg.nameLoc;
}

concrete production moduleAs
top::ModuleExpr ::= pkg1::QName 'as' pkg2::QName
{
  top.unparse = pkg1.unparse ++ " as " ++ pkg2.unparse;
  top.moduleNames := [pkg1.name];

  production attribute m :: Module;
  m = module([pkg1.name], [top.grammarName], top.compiledGrammars, top.grammarDependencies, pkg2.name, nothing(), [], []);
  
  top.errors := m.errors;
  top.defs := m.defs;
  top.occursDefs := m.occursDefs;
} action {
  insert semantic token IdGrammarName_t at pkg1.nameLoc;
  insert semantic token IdGrammarName_t at pkg2.nameLoc;
}

------------
-- WithElems

concrete production withElemsOne
top::WithElems ::= we::WithElem
{
  top.unparse = we.unparse;
  top.envMaps = we.envMaps;
}

concrete production withElemsCons
top::WithElems  ::= h::WithElem ',' t::WithElems
{
  top.unparse = h.unparse ++ ", " ++ t.unparse;
  top.envMaps = h.envMaps ++ t.envMaps;
}

-- TODO: Should this just be 'Name', at least for the initial
concrete production withElement
top::WithElem ::= n::QName 'as' newname::QName 
{
  top.unparse = n.unparse ++ " as " ++ newname.unparse;
  top.envMaps = [(n.name, newname.name)];
}

-----------
-- NameList

concrete production nameListOne
top::NameList ::= n::QName
{
  top.unparse = n.unparse;
  top.names = [n.name];
}

concrete production nameListCons
top::NameList ::= h::QName ',' t::NameList
{
  top.unparse = h.unparse ++ ", " ++ t.unparse;
  top.names = [h.name] ++ t.names;
}

