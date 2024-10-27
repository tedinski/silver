grammar silver:compiler:modification:copper_mda;

import silver:compiler:definition:concrete_syntax:copper as copper;
import silver:compiler:driver;
import silver:compiler:translation:java:driver;
import silver:compiler:translation:java:core only makeParserName, makeName;
import silver:reflect;
import silver:util:cmdargs;

aspect production compilation
top::Compilation ::= g::Grammars  _  _  a::Decorated CmdArgs  benv::BuildEnv
{
  -- TODO: consider examining all grammars, not just grammarsToTranslate?
  -- I believe this choice was originally because we weren't serializing MdaSpecs to
  -- interface files, but I think we could easily start doing that new with the new serialization code?
  top.postOps <- map(runMdaAction(_, g.compiledGrammars, benv.silverGen ++ "src/", a),
    flatMap((.mdaSpecs), grammarsToTranslate));
}

abstract production runMdaAction
top::DriverAction ::= spec::MdaSpec  compiledGrammars::EnvTree<Decorated RootSpec>  silverGen::String  cmdArgs::Decorated CmdArgs
{
  spec.compiledGrammars = compiledGrammars;

  local specCstAst :: SyntaxRoot = spec.cstAst;
  local outDir :: String = silverGen ++ "src/" ++ grammarToPath(spec.sourceGrammar);
  local parserName :: String = makeParserName(spec.fullName);
  local dumpFile :: String = outDir ++ parserName ++ ".copperdump";

  nondecorated local buildGrammar::IO<Integer> =
    if null(specCstAst.cstErrors) then do {
      mkdir(outDir);
      eprintln("Running MDA for " ++ spec.fullName ++ ".");
      ret::Integer <- copper:compileParserBean(specCstAst.copperParser,
        makeName(spec.sourceGrammar), parserName, true, "",
        cmdArgs.forceCopperDump, parserName ++ ".copperdump.html",
        false  -- TODO: Make Copper support XML dump for MDA specs
      );
      when_(ret == 0,
        case serializeBytes(^specCstAst) of
        | left(e) -> error("BUG: specCstAst was not serializable; hopefully this was caused by the most recent change to the copper_mda modification: " ++ e)
        | right(dump) -> writeBinaryFile(dumpFile, dump)
        end);
      return ret;
    } else do {
      -- Should this be stderr?
      eprintln("CST errors while preparing for MDA " ++ spec.fullName ++ ":\n" ++
        implode("\n", specCstAst.cstErrors));
      return 1;
    };

  top.run =
    if cmdArgs.doClean || cmdArgs.forceCopperDump --|| cmdArgs.copperXmlDump
    then buildGrammar
    else do {
      dumpFileExists :: Boolean <- isFile(dumpFile);
      if dumpFileExists then do {
        dumpFileContents::ByteArray <- readBinaryFile(dumpFile);
        if deserializeBytes(dumpFileContents) == right(^specCstAst) then do {
          eprintln("MDA test " ++ spec.fullName ++ " is up to date.");
          return 0;
        } else buildGrammar;
      } else buildGrammar;
    };

  top.order = 5;
}
