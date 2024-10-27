grammar silver:compiler:driver;

imports silver:reflect;

{--
 - Find an interface file, if it exists, and can be deserialized.
 -
 - @param grammarName    The grammar we're looking for an interface file for
 - @param silverHostGen  The search path to look for interface files within
 -}
function compileInterface
MaybeT<IO RootSpec> ::= grammarName::String  silverHostGen::[String]
{
  local gramPath :: String = grammarToPath(grammarName);

  return do {
    -- IO Step 1: Find the interface file, if any
    gen :: String <- findInterfaceLocation(gramPath, silverHostGen);
    let file :: String = gen ++ "src/" ++ gramPath ++ "Silver.svi";

    -- IO Step 2: Let's say so, and parse it
    lift(eprintln("Found " ++ grammarName ++ "\n\t[" ++ file ++ "]"));
    text :: ByteArray <- lift(readBinaryFile(file));
    let ir :: Either<String InterfaceItems> = deserializeBytes(text);

    -- IO Step 3: Perhaps complain it failed to deserialize
    case ir of
    | left(msg) ->
      do {
        lift(eprintln(
          "\n\tFailed to deserialize interface file!\n" ++ msg ++
          "\n\tRecovering by parsing grammar...."));
        empty;
      }
    | right(i) when !null(i.interfaceErrors) ->
      do {
        lift(eprintln(
          "\n\tErrors unpacking interface file:\n  " ++ implode("\n  ", i.interfaceErrors) ++
          "\n\tRecovering by parsing grammar...."));
        empty;
      }
    | right(i) -> pure(interfaceRootSpec(i, just(gen), nothing()))
    end;
  };
}

{--
 - Takes a grammar name (already converted to a path) and searches for Silver.svi
 -}
fun findInterfaceLocation MaybeT<IO String> ::= gramPath::String searchPaths::[String] =
  case searchPaths of
  | [] -> empty
  | h :: t -> do {
      exists :: Boolean <- lift(isFile(h ++ "src/" ++ gramPath ++ "Silver.svi"));
      if exists then pure(h) else findInterfaceLocation(gramPath, t);
    }
  end;
