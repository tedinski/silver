grammar silver:compiler:extension:doc:driver;

import silver:compiler:extension:doc:core;

import silver:compiler:driver;
import silver:compiler:definition:env;
import silver:compiler:definition:core;

import silver:util:cmdargs;

synthesized attribute docGeneration :: Boolean occurs on CmdArgs;
synthesized attribute printUndoc :: Boolean occurs on CmdArgs;
synthesized attribute countUndoc :: Boolean occurs on CmdArgs;
synthesized attribute parseDocs :: Boolean occurs on CmdArgs;
synthesized attribute docOutOption :: Maybe<String> occurs on CmdArgs;

aspect production endCmdArgs
top::CmdArgs ::= _
{
  top.docGeneration = false;
  top.printUndoc = false;
  top.countUndoc = false;
  top.parseDocs = false;
  top.docOutOption = nothing();
}

abstract production docFlag
top::CmdArgs ::= rest::CmdArgs
{
  top.docGeneration = true;
  top.parseDocs = true;
  forwards to @rest;
}

abstract production printUndocFlag
top::CmdArgs ::= rest::CmdArgs
{
  top.printUndoc = true;
  top.parseDocs = true;
  forwards to @rest;
}

abstract production countUndocFlag
top::CmdArgs ::= rest::CmdArgs
{
  top.countUndoc = true;
  top.parseDocs = true;
  forwards to @rest;
}

abstract production docOutFlag
top::CmdArgs ::= loc::String rest::CmdArgs
{
  top.docOutOption = case rest.docOutOption of
    | nothing() -> just(loc)
    | _ -> error("Duplicate arguments for docOutOption")
  end;
  forwards to @rest;
}

aspect function parseArgs
Either<String  Decorated CmdArgs> ::= args::[String]
{
  flags <- [ flagSpec(name="--doc", paramString=nothing(),
               help="build the documentation",
               flagParser=flag(docFlag))
           , flagSpec(name="--print-undoc", paramString=nothing(),
               help="print names of undocumented items",
               flagParser=flag(printUndocFlag))
           , flagSpec(name="--count-undoc", paramString=nothing(),
               help="print names of undocumented items",
               flagParser=flag(countUndocFlag))
           , flagSpec(name="--doc-out", paramString=nothing(),
               help="output location for documentation",
               flagParser=option(docOutFlag))];
}

aspect production compilation
top::Compilation ::= g::Grammars  _  _  a::Decorated CmdArgs  benv::BuildEnv
{
  local outputLoc::String = fromMaybe(benv.silverGen ++ "/doc/", a.docOutOption) ++ "/";
  top.postOps <- if a.docGeneration then 
                 [genDoc(a, grammarsToTranslate, outputLoc)]
                 else [];
  top.postOps <- if a.printUndoc || a.countUndoc then 
                 [printUndoc(a, grammarsToTranslate)]
                 else [];
}

abstract production printUndoc
top::DriverAction ::= a::Decorated CmdArgs  specs::[Decorated RootSpec]
{
  local report :: String = "\nUndocumented Items Report:\n" ++ implode("\n",
    flatMap((\x::Decorated RootSpec -> case x of 
      | grammarRootSpec(g, _, _, _, _, _) ->
          if (length(g.documentedNamed)+length(g.undocumentedNamed))!=0
          then [s" - [${g.grammarName}]: ${toString(length(g.documentedNamed))}" ++
                s"/${toString(length(g.undocumentedNamed)+length(g.documentedNamed))} " ++ 
                s"(${toString((toFloat(length(g.documentedNamed))/toFloat(length(g.undocumentedNamed)+length(g.documentedNamed)))*toFloat(100))}%) items documented"
            ++ (if a.printUndoc && (length(g.undocumentedNamed)!=0)
                then ", missing: " ++ implode(", ", g.undocumentedNamed)
                else ".")]
          else []
      | _ -> []
      end), specs));

  top.run = do { println(report); return 0; };
  top.order = 5;
}


abstract production genDoc
top::DriverAction ::= a::Decorated CmdArgs  specs::[Decorated RootSpec]  outputLoc::String
{
  top.run = do {
    eprintln("Generating Documentation.");
    traverse_(writeSpec(_, outputLoc), specs);
    return 0;
  };
  top.order = 4;
}

function writeSpec
IO<()> ::= r::Decorated RootSpec  outputLoc::String
{
  local path :: String = outputLoc ++ grammarToPath(r.declaredName);

  return do {
    eprintln("\t[" ++ r.declaredName ++ "]");
    isD::Boolean <- isDirectory(path);
    unless(isD, do {
      mkDSuccess::Boolean <- mkdir(path);
      unless(mkDSuccess, do {
        eprintln("Unrecoverable Error: Unable to create directory: " ++ path);
        exit(-5);
      });
    });
    mkdir(path);
    deleteDirFiles(path);
    writeFiles(path, r.genFiles);
  };
}
