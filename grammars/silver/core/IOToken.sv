grammar silver:core;

@@{-

The silver IO system is a IO-token based system.

# IO Types -}

@{--
 - The type representing the world-state token of an IO action.
 -}
synthesized attribute io :: IOToken;

@{--
 - The resulting value of an IO action.
 -}
synthesized attribute iovalue<a> :: a;

@{--
 - A container for the results of IO actions.
 -
 - @param a  The type of value returned by the IO action.
 -}
data nonterminal IOVal<a> with io, iovalue<a>;

type ByteArray foreign = "byte[]";

@{--
 - The sole constructor of IOVal results.
 -
 - @param i  The resulting world-state token.
 - @param v  The resulting value.
 -}
abstract production ioval
top::IOVal<a> ::= i::IOToken v::a
{
  top.io = i;
  top.iovalue = v;
}

@{--
 - IOToken is the IO Token used to sequence actions.
 -}
type IOToken foreign = "common.IOToken";

@@{- # IO Actions -}

@{--
 - Displays a string on standard out. Newlines are NOT automatically added.
 -
 - @param s  The string to print.
 - @param i  The "before" world-state token.
 - @return  The "after" world-state token.
 -}
function printT
IOToken ::= s::String i::IOToken
{
  return error("Not Yet Implemented: printT");
} foreign {
  "java" : return "%i%.print(%s%)";
}

@{--
  - Like printT, but adds a trailing newline automatically.
  -}
fun printlnT IOToken ::= str::String  ioIn::IOToken = printT(str ++ "\n", ioIn);

@{--
  - Like printT, but for stderr.
  -}
function eprintT
IOToken ::= str::String  ioIn::IOToken
{
  return error("Unimplemented foreign function: eprintT");
} foreign {
  "java" : return "%ioIn%.eprint(%str%)";
}

@{--
  - Like eprintT, but adds a trailing newline automatically.
  -}
fun eprintlnT IOToken ::= str::String  ioIn::IOToken = eprintT(str ++ "\n", ioIn);

@{--
 - Read a line from standard input.
 -
 - @param i  The "before" world-state token.
 - @return  The "after" world-state token.
 -}
function readLineStdinT
IOVal<Maybe<String>> ::= i::IOToken
{
  return error ("Not Yet Implemented: readLineStdinT");
} foreign {
  "java" : return "%i%.readLineStdin()";
}

@{--
 - Terminates with the specified error code.
 -
 - @warning Never returns! Does not do any cleanup!
 -
 - @param val  The error code to terminate with. (0 is considered "success")
 - @param i  The "before" world-state token.
 - @return  Does not actually return!
 -}
function exitT
IOToken ::= val::Integer i::IOToken
{
  return error("Not Yet Implemented: exitT");
} foreign {
  "java" : return "%i%.exit(%val%)";
}

@{--
 - Creates a directory, including any parents that need to be created along the way.
 - Similar to 'mkdir -p'. If it fails, it may create only some of them.
 -
 - @param s  The path to create.
 - @param i  The "before" world-state token.
 - @return  true if completely successful.  false if an error occurred along the way.
 -}
function mkdirT
IOVal<Boolean> ::= s::String i::IOToken
{
  return error("Not Yet Implemented: mkdirT");
} foreign {
  "java" : return "%i%.mkdir(%s%)";
}

@{--
 - Executes a shell command.  Specifically executes 'bash -c'.  So, not fully cross-platform.
 -
 - @warning Avoid using this if possible.  If you need an IO action not present, request it, please.
 -
 - Access to command's output is not directly available, but it is run in a shell. You can
 - redirect to a file and read that.
 -
 - @param s  The string for the shell to execute.
 - @param i  The "before" world-state token.
 - @return  The exit value of the subprocess.
 -}
function systemT
IOVal<Integer> ::= s::String i::IOToken
{
  return error("Not Yet Implemented: systemT");
} foreign {
  "java" : return "%i%.system(%s%)";
}

@{--
 - Write a string to a file, replacing whatever is there already.
 -
 - @param file  The filename to write to.
 - @param contents  The string to write to the file.
 - @param i  The "before" world-state token.
 - @return  The "after" world-state token.  May throw a java IO exception, which cannot be caught by Silver.
 -}
function writeFileT
IOToken ::= file::String contents::String i::IOToken
{
  return error("Not Yet Implemented: writeFileT");
} foreign {
  "java" : return "%i%.writeFile(%file%, %contents%)";
}

@{--
 - Append a string to a file.
 -
 - @param file  The filename to append to.
 - @param contents  The string to append to the file.
 - @param i  The "before" world-state token.
 - @return  The "after" world-state token.  May throw a java IO exception, which cannot be caught by Silver.
 -}
function appendFileT
IOToken ::= file::String contents::String i::IOToken
{
  return error("Not Yet Implemented: appendFileT");
} foreign {
  "java" : return "%i%.appendFile(%file%, %contents%)";
}

@{--
 - Write a bytearray to a file, replacing whatever is there already.
 -
 - @param file  The filename to write to.
 - @param contents  The bytearray to write to the file.
 - @param i  The "before" world-state token.
 - @return  The "after" world-state token.  May throw a java IO exception, which cannot be caught by Silver.
 -}
function writeBinaryFileT
IOToken ::= file::String contents::ByteArray i::IOToken
{
  return error("Not Yet Implemented: writeBinaryFileT");
} foreign {
  "java" : return "%i%.writeByteFile(%file%, %contents%)";
}

@{--
 - Read the entire contents of a file.  All instances of "\r\n" are replaced by "\n"
 - for compatibility reasons.
 -
 - @param s  The file to read.
 - @param i  The "before" world-state token.
 - @return  The contents of the file. May throw a java IO exception, which cannot be caught by Silver.
 -}
function readBinaryFileT
IOVal<ByteArray> ::= s::String i::IOToken
{
  return error("Not Yet Implemented: readBinaryFileT");
} foreign {
  "java" : return "%i%.readByteFile(%s%)";
}


@{--
 - The time, in seconds since 1970, when this file (or directory) was last modified.
 -
 - @param s  The file to query.
 - @param i  The "before" world-state token.
 - @return  The modification time of this file. Or 0 if file was not found.
 -}
function fileTimeT
IOVal<Integer> ::= s::String i::IOToken
{
  return error("Not Yet Implemented: fileTimeT");
} foreign {
  "java" : return "%i%.fileTime(%s%)";
}

@{--
 - Checks if a file is an ordinary file.  (non-directory, non-special)
 -
 - @param s  The file to query.
 - @param i  The "before" world-state token.
 - @return  true if if the file is ordinary.  false otherwise.
 -}
function isFileT
IOVal<Boolean> ::= s::String i::IOToken
{
  return error("Not Yet Implemented: isFileT");
} foreign {
  "java" : return "%i%.isFile(%s%)";
}

@{--
 - Checks if a path is a directory.
 -
 - @param s  The path to query.
 - @param i  The "before" world-state token.
 - @return  true if if the exists and is a directory. false otherwise.
 -}
function isDirectoryT
IOVal<Boolean> ::= s::String i::IOToken
{
  return error("Not Yet Implemented: isDirectoryT");
} foreign {
  "java" : return "%i%.isDirectory(%s%)";
}

@{--
 - Read the entire contents of a file.  All instances of "\r\n" are replaced by "\n"
 - for compatibility reasons.
 -
 - @param s  The file to read.
 - @param i  The "before" world-state token.
 - @return  The contents of the file. May throw a java IO exception, which cannot be caught by Silver.
 -}
function readFileT
IOVal<String> ::= s::String i::IOToken
{
  return error("Not Yet Implemented: readFileT");
} foreign {
  "java" : return "%i%.readFile(%s%)";
}

@{--
  - Checks if a file is a jar file.
  -
  - @param s  The file to query.
  - @param i  The "before" world-state token.
  - @return  true if if the file is a jar file.  false otherwise.
  -}
function isJarFileT
IOVal<Boolean> ::= s::String i::IOToken
{
  return error("Not Yet Implemented: isJarFileT");
} foreign {
  "java" : return "%i%.isJarFile(%s%)";
}

@{--
  - Checks if a jar file contains an entry.
  -
  - @param jar  The jar file to query.
  - @param entry  The entry to check for.
  - @param i  The "before" world-state token.
  - @return  true if if the jar file contains the entry.  false otherwise.
  -}
function jarContainsEntryT
IOVal<Boolean> ::= jar::String entry::String i::IOToken
{
  return error("Not Yet Implemented: jarContainsEntryT");
} foreign {
  "java" : return "%i%.jarContainsEntry(%jar%, %entry%)";
}

@{-
  - Reads a binary entry from a jar file.
  - @param jar  The jar file to read from.
  - @param entry  The entry to read.
  - @param i  The "before" world-state token.
  - @return  The contents of the entry.  May throw a java IO exception, which cannot be caught by Silver.
  -}
function readBinaryJarEntryT
IOVal<ByteArray> ::= jar::String entry::String i::IOToken
{
  return error("Not Yet Implemented: readBinaryJarEntryT");
} foreign {
  "java" : return "%i%.readByteJarEntry(%jar%, %entry%)";
}

@{--
 - Return the current working directory.
 -
 - @param i  The "before" world-state token.
 - @return  The current working directory of the process.
 -}
function cwdT
IOVal<String> ::= i::IOToken
{
  return error("Not Yet Implemented: cwdT");
} foreign {
  "java" : return "%i%.cwd()";
}

@{--
 - Obtain the value of an environment variable.
 -
 - @param s  The name of the environment variable to read.
 - @param i  The "before" world-state token.
 - @return  The variables string.  Empty string if the key doesn't exist.
 -}
function envVarT
IOVal<String> ::= s::String i::IOToken
{
  return error("Not Yet Implemented: envVarT");
} foreign {
  "java" : return "%i%.envVar(%s%)";
}

@{--
 - List the contents of a directory. Returns empty list if not a directory or
 - other IO error.
 -
 - @param s  The path to list the contents of.
 - @param i  The "before" world-state token.
 - @return  All files and directories in the named directory. Or [] on error.
 -}
function listContentsT
IOVal<[String]> ::= s::String i::IOToken
{
  return error("Not Yet Implemented: listContentsT");
} foreign {
  "java" : return "%i%.listContents(%s%)";
}

@{--
 - Delete a file, or an empty directory.
 -
 - @param s  The path to file to delete.
 - @param i  The "before" world-state token.
 - @return  true if the file is deleted successfully.  false otherwise.
 -}
function deleteFileT
IOVal<Boolean> ::= s::String i::IOToken
{
  return error("Not Yet Implemented: deleteFileT");
} foreign {
  "java" : return "%i%.deleteFile(%s%)";
}

@{--
 - Delete a set of files.
 -
 - @param s  The list of paths to files to delete.
 - @param i  The "before" world-state token.
 - @return  true if all files are deleted successfully.  false otherwise.
 -}
function deleteFilesT
IOVal<Boolean> ::= s::[String] i::IOToken
{
  return error("Not Yet Implemented: deleteFilesT");
} foreign {
  "java" : return "%i%.deleteFiles(%s%)";
}

@{--
 - Empty a directory of all normal files (i.e. leaving subdirectories alone)
 -
 - @param s  The path to the directory to empty
 - @param i  The "before" world-state token.
 - @return  true if contents are deleted successfully.  false otherwise.
 -}
function deleteDirFilesT
IOVal<Boolean> ::= s::String i::IOToken
{
  return error("Not Yet Implemented: deleteDirFilesT");
} foreign {
  "java" : return "%i%.deleteDirFiles(%s%)";
}

@{--
 - Delete a non-empty directory and all subdirectories and files.
 -
 - @param s  The path to the directory to delete
 - @param i  The "before" world-state token.
 - @return  The IOToken token. Errors (other than non-existence of the path) are fatal.
 -}
function deleteTreeT
IOToken ::= s::String  i::IOToken
{
  return error("Not Yet Implemented: deleteTreeT");
} foreign {
  "java" : return "%i%.deleteTree(%s%)";
}

@{--
 - Copy a file from src to dst.
 -
 - @param src  The path of the file to copy.
 - @param dst  The path of the file to write, or the directory to copy the file to.
 - @param i  The "before" world-state token.
 - @return  the IOToken token. Errors are fatal.
 -}
function copyFileT
IOToken ::= src::String  dst::String  i::IOToken
{
  return error("Not Yet Implemented: copyFileT");
} foreign {
  "java" : return "%i%.copyFile(%src%, %dst%)";
}

@{--
 - Update a file's modification time to the current time.
 -
 - @param file  The file to update the modification time of.
 - @param i  The IOToken token.
 - @return The IOToken token. Errors are suppressed.
 -}
function touchFileT
IOToken ::= file::String i::IOToken
{
  return error("Not Yet Implemented: touchFileT");
} foreign {
  "java" : return "%i%.touchFile(%file%)";
}

@{--
 - Update a set of files' modification time to the current time.
 -
 - @param files  The list of files to update the modification time of.
 - @param i  The IOToken token.
 - @return The IOToken token. Errors are suppressed.
 -}
function touchFilesT
IOToken ::= files::[String] i::IOToken
{
  return error("Not Yet Implemented: touchFilesT");
} foreign {
  "java" : return "%i%.touchFiles(%files%)";
}


@@{- # IO Misc -}

@{--
 - Create a bogus world-state token, for use with @link[unsafeTrace].
 -
 - @return  A fake world-state token.
 -}
function unsafeIO
IOToken ::=
{
  return error("Not Yet Implemented: unsafeIO");
} foreign {
  "java" : return "common.IOToken.singleton";
}

@{--
 - Execute an IO action when a value is demanded by the Silver runtime.
 - When this gets executed may be unpredictable.
 -
 - @param val  The value to evaluate to, after the IO action is performed.
 - @param act  The world-state token to demand and consume.
 - @return  val, unchanged.
 - @warning see @link[unsafeIO]
 -}
function unsafeTrace
a ::= val::a act::IOToken
{
  return error("Not Yet Implemented: unsafeTrace");
} foreign {
  "java" : return "common.Util.io(%act%, %val%)";
}
