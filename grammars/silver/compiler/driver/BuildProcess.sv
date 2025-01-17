grammar silver:compiler:driver;

imports silver:compiler:definition:core;
imports silver:compiler:definition:env;

imports silver:util:cmdargs;

exports silver:compiler:driver:util;

type SVParser = (ParseResult<File> ::= String String);

{--
 - Run the silver compiler, as if invoked from the command line.
 -}
function cmdLineRun
IO<Integer> ::= args::[String]  svParser::SVParser
{
  local unit :: IOErrorable<Compilation> =
    cmdLineRunInitial(args, svParser);
    
  return performActions(unit);
}

-- Compute the environment, and then setup and do a build run. No postOps executed, though.
fun cmdLineRunInitial IOErrorable<Compilation> ::= args::[String]  svParser::SVParser =
  do {
    env::(Decorated CmdArgs, BuildEnv) <- computeEnv(args);
    setupBuildRun(svParser, env.1, env.2);
  };

-- Perform the postOps from a cmdLineRunInitial.
fun performActions IO<Integer> ::= unit::IOErrorable<Compilation> =
  do {
    res::Either<RunError Compilation> <- unit.run;
    case res of
    | left(re) -> do {
        eprintln(re.errMsg);
        return re.code;
      }
    | right(comp) -> runAll(comp.postOps)
    end;
  };

-- Parser args and environment
fun computeEnv IOErrorable<(Decorated CmdArgs, BuildEnv)> ::= args::[String] =
  case parseArgs(args) of
  | left(argErrors) -> throwRunError(1, argErrors)
  | right(a) -> do {
    -- Figure out build env from environment and args
    benv::BuildEnv <- determineBuildEnv(a);
    silverVersion::String <- lift(stateIO(getJarVersion));
    -- Because we want printing the version to work even if the environment is messed up
    -- we premptively handle that here. This is slightly unfortunate.
    -- Ideally, version printing would be just another thing we could have the command
    -- line decide to go do, but currently it's hard to re-use code if we do that.
    if a.displayVersion then
      throwRunError(127, -- error code so 'ant' isnt run
        "Silver Version " ++ silverVersion ++ "\n" ++
        "SILVER_HOME = " ++ benv.silverHome ++ "\n" ++
        "SILVER_GEN = " ++ benv.silverGen ++ "\n" ++
        "GRAMMAR_PATH:\n" ++ implode("\n", benv.grammarPath))
    else pure((a, benv));
  }
  end;

-- Upon deciding that we're to build one or more grammars into a jar, we do this
fun setupBuildRun
IOErrorable<Compilation> ::=
  svParser::SVParser
  a::Decorated CmdArgs
  benv::BuildEnv =
  do {
    -- Check environment stuff specific to building a grammar
    checkbuild::[String] <- lift(checkPreBuild(benv, a.buildGrammars));
    when_(!null(checkbuild), throwRunError(1, implode("\n", checkbuild)));

    -- Build!
    buildrun :: Compilation <- lift(buildRun(svParser, a, benv, a.buildGrammars));
    let missingGrammars::[String] =
      removeAll(map((.declaredName), buildrun.grammarList), a.buildGrammars);
    when_(!null(missingGrammars),
      throwRunError(1, "The specified grammar(s) " ++ implode(", ", missingGrammars) ++ " could not be found.\n"));

    return buildrun;
  };

{--
 - Given an environment and a grammar to build, returns a Compilation.
 - Note that it's the caller's responsibility to actually evaluate that
 - compilation's actions.
 -}
fun buildRun
IO<Compilation> ::=
  svParser::SVParser
  a::Decorated CmdArgs
  benv::BuildEnv
  buildGrammars::[String] = mdo {
    -- Compile grammars. There's some tricky circular program data flow here.
    -- This does an "initial grammar stream" composed of 
    -- grammars and interface files that *locally* seem good.
    rootStream :: [Maybe<RootSpec>] <-
      unsafeInterleaveIO(compileGrammars(svParser, benv, grammarStream, a.doClean, false));

    -- The list of grammars to build. This is circular with the above, producing
    -- a list that's terminated when the response count is equal to the number of emitted
    -- grammar names.
    let grammarStream :: [String] =
      buildGrammars ++
      eatGrammars(mentionedGrammars, length(buildGrammars), buildGrammars, rootStream, unit.grammarList);
    
    -- This is, essentially, a data structure representing a compilation.
    -- Note that it is pure: it doesn't take any actions.
    let unit :: Compilation =
      compilation(
        foldr(consGrammars, nilGrammars(), catMaybes(rootStream)),
        foldr(consGrammars, nilGrammars(), catMaybes(reRootStream)),
        buildGrammars, a, benv);

    -- There is a second circularity here where we use unit.reGrammarList
    -- to supply the second parameter to unit.
    reRootStream :: [Maybe<RootSpec>] <-
      unsafeInterleaveIO(compileGrammars(svParser, benv, reGrammarStream, a.doClean, true));
    
    let reGrammarStream :: [String] =
      unit.initDirtyGrammars ++
      eatGrammars(
        (.dirtyGrammars), length(unit.initDirtyGrammars),
        unit.initRecompiledGrammars ++ unit.initDirtyGrammars,
        reRootStream, unit.reGrammarList);

    return unit;
  };

{--
 - Eat the stream `need` and produce the output stream of (maybe, if found) `RootSpec`s.
 -
 - @param benv   The compiler configuration, including search paths
 - @param need   A **stream** of grammars to compile.
 - @param clean  If true, ignore interface files entirely.
 -}
fun compileGrammars
IO<[Maybe<RootSpec>]> ::=
  svParser::SVParser
  benv::BuildEnv
  need::[String]
  ignoreInterface::Boolean
  forceRecompile::Boolean
  = traverseA(\ g::String -> compileGrammar(svParser, benv, g, ignoreInterface, forceRecompile).run, need);

{--
 - Consumes a stream of parses, outputs a stream of new dependencies.
 - Typically used as a circular program with 'compileGrammars'
 -
 - @param triggered  A function returning a list of grammars that sould be triggered by a grammar
 - @param n  Expected number of new inputs from rootStream
 - @param sofar  Set of grammars already seen, and should not be requested again
 - @param rootStream  Stream of found/not found info. Should not be used except to test presence
 - @param grammars  List of grammars *in the same order as 'just' appears in rootStream*
 - @return  A stream of new dependencies
 -}
function eatGrammars
[String] ::= triggered::([String] ::= Decorated RootSpec)  n::Integer  sofar::[String]  rootStream::[Maybe<a>]  grammars::[Decorated RootSpec]
{
  local it :: Decorated RootSpec = head(grammars);  
  local directDeps :: [String] = triggered(it);
  
  local newDeps :: [String] = removeAll(sofar, directDeps);
  
  return
    if n == 0 then
      []
    else if !head(rootStream).isJust then
      eatGrammars(triggered, n-1, sofar, tail(rootStream), grammars)
    else
      newDeps ++ eatGrammars(triggered, n-1+length(newDeps), newDeps ++ sofar, tail(rootStream), tail(grammars));
}

annotation code::Integer;
annotation errMsg::String;

data RunError = runError
  with code, errMsg;

-- A common return type for IO functions. Does IO and returns error or whatever.
type IOErrorable<a> = EitherT<RunError IO a>;

fun throwRunError IOErrorable<a> ::= c::Integer m::String = throwError(runError(code=c, errMsg=m));

function getJarVersion
IOVal<String> ::= i::IOToken
{
  return error("NYI");
} foreign {
  "java" : return "new silver.core.Pioval(%i%, common.Util.getJarVersion(Init.class))";
}