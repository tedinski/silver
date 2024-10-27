grammar silver:compiler:modification:copper;

import silver:compiler:definition:concrete_syntax:copper as copper;
import silver:compiler:driver;
import silver:compiler:translation:java:driver;
import silver:reflect;
import silver:util:cmdargs;

{---------------------------------}
{- Define the --copperdump flag. -}
{---------------------------------}

synthesized attribute forceCopperDump :: Boolean occurs on CmdArgs;

aspect production endCmdArgs
top::CmdArgs ::= _
{
  top.forceCopperDump = false;
}

abstract production copperdumpFlag
top::CmdArgs ::= rest::CmdArgs
{
  top.forceCopperDump = true;
  forwards to @rest;
}

aspect function parseArgs
Either<String  Decorated CmdArgs> ::= args::[String]
{
  flags <- [
    flagSpec(name="--copperdump", paramString=nothing(),
      help="force Copper to dump parse table information",
      flagParser=flag(copperdumpFlag))];
}

{--------------------------------------}
{- Define the --copper-xml-dump flag. -}
{--------------------------------------}

synthesized attribute copperXmlDump::Boolean occurs on CmdArgs;

aspect production endCmdArgs
top::CmdArgs ::= _
{ top.copperXmlDump = false; }

production copperXmlDumpFlag
top::CmdArgs ::= rest::CmdArgs
{
  top.copperXmlDump = true;
  forwards to @rest;
}

aspect function parseArgs
Either<String  Decorated CmdArgs> ::= args::[String]
{
  flags <- [
    flagSpec(name="--copper-xml-dump", paramString=nothing(),
      help="dump the specification being passed to Copper as XML",
      flagParser=flag(copperXmlDumpFlag))];
}

{--------------------------------}
{- Request building of parsers. -}
{--------------------------------}

-- Skips parser specs from SILVER_HOST_GEN
-- The way that feature works, they shouldn't need regeneration.
fun obtainParserSpecs [ParserSpec] ::= g::Decorated RootSpec  benv::BuildEnv =
  if g.generateLocation != just(benv.silverGen) then []
  else g.parserSpecs;

aspect production compilation
top::Compilation ::= g::Grammars  _  _  a::Decorated CmdArgs  benv::BuildEnv
{
  -- Add the Copper runtime to the CLASSPATH.
  classpathRuntime <- ["${sh}/jars/CopperRuntime.jar"];

  -- Get the parsers.
  production allParsers :: [ParserSpec] =
    flatMap(obtainParserSpecs(_, benv), grammarsRelevant);

  -- Don't delete generated parsers from past builds
  keepFiles <-
    flatMap(\ spec::ParserSpec ->
      let baseName::String = benv.silverGen ++ "src/" ++ grammarToPath(spec.sourceGrammar) ++ makeParserName(spec.fullName)
      in [baseName ++ ".copperdump", baseName ++ ".java"]
      end,
      allParsers);

  -- Generate the .java files.
  top.postOps <-
    map(buildParserAction(_, g.compiledGrammars, benv.silverGen, a), allParsers);
}

{------------------------------}
{- Build the parsers to Java. -}
{------------------------------}

@{- Writes a parser out to a file.
  -
  - We create a separate GrammarAction rather than building this into genJava
  - as an optimization. The build process iteratively rebuilds all dependent
  - grammars whenever an interface file change, which may happen for a number of
  - reasons (e.g. defining a new attribute) that do not affect the concrete
  - syntax used to build a parser in a rebuilt grammar.
  - To avoid this, we cache the concrete syntax AST used to build the parser,
  - and skip parser generation if the syntax AST is unchanged.
  -}
abstract production buildParserAction
top::DriverAction ::= spec::ParserSpec  compiledGrammars::EnvTree<Decorated RootSpec>  silverGen::String  cmdArgs::Decorated CmdArgs
{
  spec.compiledGrammars = compiledGrammars;

  local specCstAst::SyntaxRoot = spec.cstAst;
  local outDir::String = silverGen ++ "src/" ++ grammarToPath(spec.sourceGrammar);
  local parserName::String = makeParserName(spec.fullName);
  local dumpFile::String = outDir ++ parserName ++ ".copperdump";

  nondecorated local buildGrammar::IO<Integer> =
    if null(specCstAst.cstErrors) then do {
      if cmdArgs.noJavaGeneration then do {
        -- Skip translating to Java.
        return 0;
      } else do {
        mkdir(outDir);
        eprintln("Generating parser " ++ spec.fullName ++ ".");
        ret::Integer <- copper:compileParserBean(specCstAst.copperParser,
          makeName(spec.sourceGrammar), parserName, false,
          outDir ++ parserName ++ ".java", cmdArgs.forceCopperDump,
          parserName ++ ".copperdump.html", cmdArgs.copperXmlDump);
        when_(ret == 0,
          case serializeBytes(^specCstAst) of
          | left(e) -> error("BUG: specCstAst was not serializable; hopefully this was caused by the most recent change to the copper modification: " ++ e)
          | right(dump) -> writeBinaryFile(dumpFile, dump)
          end);
        return ret;
      };
    } else do {
      eprintln("CST errors while generating parser " ++ spec.fullName ++ ":\n" ++
        implode("\n", specCstAst.cstErrors));
      return 1;
    };

  top.run =
    if cmdArgs.doClean || cmdArgs.forceCopperDump || cmdArgs.copperXmlDump
    then buildGrammar
    else do {
      dumpFileExists :: Boolean <- isFile(dumpFile);
      if dumpFileExists then do {
        dumpFileContents::ByteArray <- readBinaryFile(dumpFile);
        if deserializeBytes(dumpFileContents) == right(^specCstAst) then do {
          eprintln("Parser " ++ spec.fullName ++ " is up to date.");
          return 0;
        } else buildGrammar;
      } else buildGrammar;
    };

  top.order = 7;
}
