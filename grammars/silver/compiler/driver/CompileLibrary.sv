grammar silver:compiler:driver;

function compileLibrary
MaybeT<IO RootSpec> ::= grammarName::String  libs::[String]
{
  local gramPath :: String = grammarToPath(grammarName);

  return do {
    -- IO Step 1: Find the interface file, if any
    jar :: String <- findGrammarJarLocation(gramPath, libs);

    -- IO Step 2: Let's say so, and parse it
    lift(eprintln("Found " ++ grammarName ++ "\n\t[" ++ jar ++ "]"));
    text :: ByteArray <- lift(readBinaryJarEntry(jar, gramPath ++ "Silver.svi"));
    let ir :: Either<String InterfaceItems> = deserializeBytes(text);

    -- IO Step 3: Perhaps complain it failed to deserialize.
    -- A failure to deserialize here is a fatal error, as it indicates a problem with the library jar file.
    case ir of
    | left(msg) -> lift(
      do {
        eprintln(
          "\n\tFailed to deserialize interface file!\n" ++ msg ++
          s"\n\tEnsure the library jar file ${jar} is up to date.");
        exit(3);
      })
    | right(i) when !null(i.interfaceErrors) -> lift(
      do {
        eprintln(
          "\n\tErrors unpacking interface file:\n  " ++ implode("\n  ", i.interfaceErrors) ++
          s"\n\tEnsure the library jar file ${jar} is up to date.");
        exit(4);
      })

    | right(i) -> pure(interfaceRootSpec(i, nothing(), just(jar)))
    end;
  };
}

fun findGrammarJarLocation MaybeT<IO String> ::= gramPath::String searchPaths::[String] =
  case searchPaths of
  | h :: t -> alt(findGrammarJarInLocation(gramPath, h), findGrammarJarLocation(gramPath, t))
  | [] -> empty
  end;

fun findGrammarJarInLocation MaybeT<IO String> ::= gramPath::String path::String =
  do {
    isJar :: Boolean <- lift(isJarFile(path));
    guard(isJar);
    hasGrammar :: Boolean <- lift(jarContainsEntry(path, gramPath ++ "Silver.svi"));
    guard(hasGrammar);
    return path;
  };
