grammar silver:compiler:driver;

{-
 - A short guide to error codes:
 - Negative = configuration/installation error
 - 1-19 = command line/start up error
 - 20+ = Normal use error (errors in spec)
 - 127 = "abnormal" success (e.g. printed version string, quit now)
 - 0 = success of course
 -}

{- Orders:
 - 0: parsing errors (also flow graph emitting)
 - 1: binding errors
 - 3: interfaces and classes
 - 4: doc
 - 5: copper_mda
 - 6: buildxml
 - 7: impide
 -}

aspect production compilation
top::Compilation ::= g::Grammars  r::Grammars  buildGrammars::[String]  a::Decorated CmdArgs  benv::BuildEnv
{
  top.postOps <- [printAllParsingErrors(top.allGrammars)];
  top.postOps <- if a.noBindingChecking then [] else
    [printAllBindingErrors(top.allGrammars)]; 
  top.postOps <- [touchIfaces(r.grammarList, benv.silverGen)];
}

abstract production touchIfaces
top::DriverAction ::= r::[Decorated RootSpec] genPath::String
{
  top.run = do { touchFiles(map(sviPath(_, genPath), r)); return 0; };
  top.order = 3;
}
fun sviPath String ::= r::Decorated RootSpec genPath::String =
  genPath ++ "src/" ++ grammarToPath(r.declaredName) ++ "Silver.svi";

abstract production printAllBindingErrors
top::DriverAction ::= specs::[Decorated RootSpec]
{
  -- Force printing of status before doing error checks
  top.run = do {
    eprintln("Checking For Errors.");
    forward.run;
  };

  forwards to printAllBindingErrorsHelp(specs);
}

abstract production printAllBindingErrorsHelp
top::DriverAction ::= specs::[Decorated RootSpec]
{
  top.run =
    case specs of
    | [] -> pure(0)
    | spec :: rest -> do {
        unless(null(spec.grammarErrors),
          eprintln("Errors for " ++ spec.declaredName ++ "\n" ++ flatMap(renderMessages(spec.grammarSource, _), spec.grammarErrors)));
        let containsErrors :: Boolean = grammarContainsErrors(spec.grammarErrors, spec.config.warnError);
        recurse :: Integer <- printAllBindingErrorsHelp(rest).run;
        return if containsErrors || recurse != 0 then 20 else 0;
      }
    end;

  top.order = 1;
}

abstract production printAllParsingErrors
top::DriverAction ::= specs::[Decorated RootSpec]
{
  top.run =
    case specs of
    | [] -> pure(0)
    | spec :: rest -> do {
        unless(null(spec.parsingErrors),
          eprintln("Errors for " ++ spec.declaredName ++ "\n" ++ flatMap(renderMessages(spec.grammarSource, _), spec.parsingErrors)));
        recurse :: Integer <- printAllParsingErrors(rest).run;
        return if !null(spec.parsingErrors) || recurse != 0 then 21 else 0;
      }
    end;

  top.order = 0;
}

fun renderMessages String ::= grammarSource::String  msg::Pair<String [Message]> =
  " [" ++ grammarSource ++ msg.fst ++ "]\n" ++ messagesToString(msg.snd) ++ "\n";

fun grammarContainsErrors Boolean ::= es::[Pair<String [Message]>]  werr::Boolean =
  if null(es) then false
  else containsErrors(head(es).snd, werr) || grammarContainsErrors(tail(es), werr);

