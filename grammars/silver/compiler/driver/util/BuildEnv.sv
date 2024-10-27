grammar silver:compiler:driver:util;

data nonterminal BuildEnv with silverHome, silverGen, grammarPath, silverHostGen, defaultSilverGen, defaultGrammarPath;

{-- Find jars, standard library -}
annotation silverHome :: String;
{-- Write files, look for already built grammars -}
annotation silverGen :: String;
{-- Search for source files -}
annotation grammarPath :: [String];
{-- Search for already built grammars. **Always includes silverGen!** -}
annotation silverHostGen :: [String];

synthesized attribute defaultSilverGen :: String;
synthesized attribute defaultGrammarPath :: [String]; -- Just the stdlib, so not actually just the default value

{--
 - Build environment information.
 - Note: each of these paths always terminates with /
 - TODO: consider moving svParser, args to this structure too? (e.g. clean flag, build grammar)
 - maybe also buildGrammar?
 - Note: this constructor is referenced in the language server, so any
 - anno args here should be easy to construct from Java.
 -}
abstract production buildEnv
top::BuildEnv ::=
{
  -- So that this exists in exactly one location:
  top.defaultSilverGen = top.silverHome ++ "generated/";
  top.defaultGrammarPath = [
    top.silverHome ++ "jars/silver.core.jar",
    top.silverHome ++ "jars/silver.util.jar",
    top.silverHome ++ "jars/silver.langutil.jar",
    top.silverHome ++ "jars/silver.rewrite.jar",
    top.silverHome ++ "jars/silver.regex.jar",
    -- Allow linking against the compiler by default.
    -- This makes it easier to build extended versions of Silver.
    top.silverHome ++ "jars/silver.compiler.composed.Default.jar"
  ];
}

-- Takes environment and values from args and determines buildEnv according to correct priorities.
function fromArgsAndEnv
BuildEnv ::=
  SILVER_HOME::String -- empty string or value
  SILVER_GEN::String -- empty string or value
  GRAMMAR_PATH::[String] -- any number of values
  SILVER_HOST_GEN::[String] -- any number of values
  homeArg::[String] -- empty list or one value
  genArg::[String] -- empty list or one value
  pathArg::[String] -- any number of values
  noStdlib::Boolean -- if true, don't use the defaultGrammarPath
{
  -- If provided with one, use that, otherwise always use the environment value (if empty, use that)
  local silverHome :: String =
    endWithSlash(head(homeArg ++ [SILVER_HOME]));
  
  -- Use the argument, or if NON-EMPTY, use the environment. Otherwise, use the inferred value from silverHome.
  local silverGen :: String =
    endWithSlash(head(genArg ++ (if SILVER_GEN == "" then [] else [SILVER_GEN]) ++ [benv.defaultSilverGen]));
  
  -- Use the arguments (all of them), followed by environment (if any?), followed by STDLIB, and CWD.
  local grammarPath :: [String] =
    pathArg ++
    GRAMMAR_PATH ++
    (if noStdlib then [] else benv.defaultGrammarPath) ++
    ["."];
  
  -- Always search generated first, and what the environment provides us with.
  local silverHostGen :: [String] =
    silverGen :: map(endWithSlash, SILVER_HOST_GEN);

  local benv :: BuildEnv = buildEnv(
    silverHome=silverHome,
    silverGen=silverGen,
    grammarPath=grammarPath,
    silverHostGen=silverHostGen);
  
  return benv;
}

{--
 - Ensures a string ends with a forward slash. Safe to use if it already has one.
 -}
fun endWithSlash String ::= s::String = if endsWith("/", s) then s else s ++ "/";


