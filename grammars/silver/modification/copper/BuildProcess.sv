grammar silver:modification:copper;

import silver:driver;
import silver:translation:java:driver;

import silver:util:cmdargs;

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
  forwards to rest;
}
aspect function parseArgs
ParseResult<Decorated CmdArgs> ::= args::[String]
{
  flags <- [pair("--copperdump", flag(copperdumpFlag))];
  flagdescs <- ["\t--copperdump  : force Copper to dump parse table information"];
}
aspect production compilation
top::Compilation ::= g::Grammars _ buildGrammar::String silverHome::String silverGen::String
{
  classpathCompiler <- ["${sh}/jars/CopperCompiler.jar"];
  classpathRuntime <- ["${sh}/jars/CopperRuntime.jar"];
  extraTopLevelDecls <- [
    "  <taskdef name='copper' classname='edu.umn.cs.melt.copper.ant.CopperAntTask' classpathref='compile.classpath'/>",
    "  <target name='copper'>\n" ++ buildAntParserPart(allParsers, top.config) ++ "  </target>"];
  extraGrammarsDeps <- ["copper"];

  production allParsers :: [ParserSpec] = foldr(append, [], map((.parserSpecs), grammarsToTranslate));
  -- TODO: temporarily all parsers!
}

function buildAntParserPart
String ::= r::[ParserSpec] a::Decorated CmdArgs
{
  local attribute p :: ParserSpec;
  p = head(r);

  local attribute parserName :: String;
  parserName = makeParserName(p.fullName);
  
  local attribute packagename :: String;
  packagename = makeName(p.sourceGrammar);
  
  local attribute packagepath :: String;
  packagepath = grammarToPath(p.sourceGrammar);

  return if null(r) then "" else( 
"    <copper packageName='" ++ packagename ++ "' parserName='" ++ parserName ++ "' outputFile='${src}/" ++ packagepath ++ parserName ++ ".java' useSkin='XML' warnUselessNTs='false' dump='" ++ (if a.forceCopperDump then "ON" else "ERROR_ONLY") ++ "' dumpFormat='HTML' dumpFile='" ++ parserName ++ ".copperdump.html'>\n" ++
"      <inputs file='${src}/" ++ packagepath ++ parserName ++ ".copper'/>\n    </copper>\n" ++
  buildAntParserPart(tail(r), a));
}

