grammar silver:compiler:driver;

import silver:reflect:nativeserialize;

{--
 - Hunts down a grammar and obtains its symbols, either by building or from an interface file.
 -}
function compileGrammar
MaybeT<IO RootSpec> ::=
  svParser::SVParser
  benv::BuildEnv
  grammarName::String
  clean::Boolean
{
  local gramPath :: String = grammarToPath(grammarName);

  return do {
    findGrammar::Maybe<(Integer, String, [String])> <- lift(do {
        -- IO Step 1: Look for the grammar's source files
        grammarLocation :: String <- findGrammarLocation(gramPath, benv.grammarPath);

        -- IO Step 2: List those files, and obtain their newest modification time
        files :: [String] <- lift(listSilverFiles(grammarLocation));
        when_(null(files), empty); -- Grammar had no files!
        grammarTime :: Integer <- lift(fileTimes(grammarLocation, files));

        return (grammarTime, grammarLocation, files);
      }.run);
    alt(
      -- IO Step 3: Let's look for a valid interface file
      if clean
        then empty  -- We just skip this search if it's a clean build
        else compileInterface(grammarName, benv.silverHostGen, map(fst, findGrammar)),
      do {
        -- We didn't find a valid interface file
        foundGrammar::(Integer, String, [String]) <- maybeT(pure(findGrammar));
        let grammarTime::Integer = foundGrammar.1;
        let grammarLocation::String = foundGrammar.2;
        let files::[String] = foundGrammar.3;

        -- IO Step 4: Build the grammar, and say so
        lift(eprintln("Compiling " ++ grammarName ++ "\n\t[" ++ grammarLocation ++ "]\n\t[" ++ renderFileNames(files, 0) ++ "]"));
        gramCompile::([Root], [ParseError]) <- lift(compileFiles(svParser, grammarLocation, files));

        -- IO Step 5: Check for an old interface file, to tell if we need to transitively re-translate
        oldInterface::Maybe<InterfaceItems> <- lift(do {
            guard(!clean);  -- Skip this if we are doing a clean build anyway, to avoid comparing old interface files.
            gen :: String <- findInterfaceLocation(gramPath, benv.silverHostGen);
            let file :: String = gen ++ "src/" ++ gramPath ++ "Silver.svi";
            --lift(eprintln(s"Found old interface ${file}"));
            content::ByteArray <- lift(readBinaryFile(file));
            case nativeDeserialize(content) of
            | left(msg) -> empty
            | right(ii) -> pure(ii)
            end;
          }.run);

        return if null(gramCompile.2)
          then grammarRootSpec(foldRoot(gramCompile.1), oldInterface, grammarName, grammarLocation, grammarTime, benv.silverGen)
          else errorRootSpec(gramCompile.2, grammarName, grammarLocation, grammarTime, benv.silverGen);
      });
  };
}

function foldRoot
Grammar ::= l::[Root]
{
  return foldr(consGrammar, nilGrammar(), l);
}

{--
 - Determined whether a file name should be considered a Silver source file.
 -}
function isValidSilverFile
Boolean ::= f::String
{
  return any(map(endsWith(_, f), allowedSilverFileExtensions)) && !startsWith(".", f);
}
function listSilverFiles
IO<[String]> ::= dir::String
{
  return do {
    files :: [String] <- listContents(dir);
    return filter(isValidSilverFile, files);
  };
}

{--
 - Determines the maximum modification time of all files in a directory.
 - Including the directory itself, to detect file deletions.
 -}
function fileTimes
IO<Integer> ::= dir::String is::[String]
{
  return
    case is of
    | [] -> fileTime(dir) -- check the directory itself. Catches deleted files.
    | h :: t -> do {
        ft :: Integer <- fileTime(dir ++ h);
        rest :: Integer <- fileTimes(dir, t);
        return max(ft, rest);
      }
    end;
}

-- A crude approximation of line wrapping
function renderFileNames
String ::= files::[String]  depth::Integer
{
  return
    if null(files) then "" else
    if depth >= 7 then "\n\t " ++ renderFileNames(files, 0) else
    head(files) ++
    if null(tail(files)) then "" else " " ++ renderFileNames(tail(files), depth + 1);
}

{--
 - Takes a grammar name (already converted to a path) and searches the grammar
 - path for the first directory that matches.
 -}
function findGrammarLocation
MaybeT<IO String> ::= path::String searchPaths::[String]
{
  return
    case searchPaths of
    | h :: t -> alt(findGrammarInLocation(path, h), findGrammarLocation(path, t))
    | [] -> empty
    end;
}

{--
 - Looks to see if the grammar can be found in 'inPath'
 - Tries (in order) for edu:umn:cs
 - edu/umn/cs/
 - edu.umn/cs/
 - edu.umn.cs/
 -}
function findGrammarInLocation
MaybeT<IO String> ::= gram::String inPath::String
{
  -- Find the first / in the grammar name (turned path) we're looking for.
  local idx :: Integer = indexOf("/", gram);
  
  -- Replace the first / with a .
  local nextGram :: String = substring(0, idx, gram) ++ "." ++ substring(idx + 1, length(gram), gram);
  
  return do {
    exists :: Boolean <- lift(isDirectory(inPath ++ gram));
    if exists then pure(inPath ++ gram)
      else if idx == -1 then empty
      else findGrammarInLocation(nextGram, inPath);
  };
}
