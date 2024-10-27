grammar silver:compiler:refactor;

import silver:compiler:translation:java:driver;

synthesized attribute doRefactor :: Boolean occurs on CmdArgs;
synthesized attribute refactorGrammars :: [String] occurs on CmdArgs;

aspect production endCmdArgs
top::CmdArgs ::= _
{
  top.doRefactor = false;
  top.refactorGrammars = [];
}
abstract production refactorFlag
top::CmdArgs ::= rest::CmdArgs
{
  top.doRefactor = true;
  top.doClean = true;
  top.noBindingChecking = true;
  top.noJavaGeneration = true;
  forwards to @rest;
}
abstract production refactorGrammarsFlag
top::CmdArgs ::= s::String rest::CmdArgs
{
  top.refactorGrammars = s :: rest.refactorGrammars;
  forwards to @rest;
}

aspect function parseArgs
Either<String  Decorated CmdArgs> ::= args::[String]
{
  flags <-
    [ flagSpec(name="--refactor-in", paramString=just("<path>"),
        help="parent grammar of grammars to refactor",
        flagParser=option(refactorGrammarsFlag)) ];
}

aspect production compilation
top::Compilation ::= g::Grammars  _  buildGrammars::[String]  a::Decorated CmdArgs  benv::BuildEnv
{
  local refactorGrammars::[Decorated RootSpec] =
    filter(\ r::Decorated RootSpec ->
      case r of
      | grammarRootSpec(_, _, grammarName, _, _, _) ->
        null(g.config.refactorGrammars) ||
        any(map(startsWith(_, grammarName), g.config.refactorGrammars))
      | _ -> false
      end,
      grammarsRelevant);

  top.postOps <-
    if a.doRefactor
    then [doRefactor(a, refactorGrammars)]
    else [];
}

abstract production doRefactor
top::DriverAction ::= a::Decorated CmdArgs  specs::[Decorated RootSpec]
{
  top.run = do {
    eprintln("Applying Refactoring.");
    traverse_(refactorSpec, specs);
    return 0;
  };
  top.order = 4;
}

fun refactorSpec IO<()> ::= r::Decorated RootSpec =
  do {
    eprintln("\t[" ++ r.declaredName ++ "]");
    traverse_(\ item::(String, Root) ->
      when_(!endsWith(".md", item.1),  -- TODO: Make this work with literate Silver files
        do {
          let fullPath::String = r.grammarSource ++ item.1;
          text::String <- readFile(fullPath);
          let newText::String = show(100, unparseFile(text, item.2));
          when_(text != newText, writeFile(fullPath, newText));
        }),
      r.transformedFiles);
  };

monoid attribute transformedFiles::[(String, Root)] occurs on RootSpec, Grammar;
propagate transformedFiles on RootSpec, Grammar;

aspect production consGrammar
top::Grammar ::= h::Root  t::Grammar
{
  top.transformedFiles <- [(getParsedOriginLocation(h).fromJust.filename, h.transformed)];
}
