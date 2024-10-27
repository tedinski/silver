grammar silver:core;

@{-
 - Representation of a monadic IO action.
 -
 - The stateIn/stateOut threading exists to ensure that IO actions happen in
 - the proper order, thus the invariant that stateOut should be demanded before stateVal.
 - Note that unsafeInterleaveIO intentionally violates this, causing IO actions to be evaluated when
 - their value is demanded.
 -}
closed nonterminal IO<a> with stateIn<IOToken>, stateOut<IOToken>, stateVal<a>;

abstract production bindIO
top::IO<b> ::= st::IO<a> fn::(IO<b> ::= a)
{
  st.stateIn = top.stateIn;
  local newState::IO<b> = fn(st.stateVal);
  newState.stateIn = st.stateOut;
  -- Using unsafeTrace here to ensure that when top.stateOut is demanded,
  -- we demand st.stateOut before st.stateVal
  top.stateOut = unsafeTrace(newState.stateOut, st.stateOut);
  top.stateVal = newState.stateVal;
}

abstract production returnIO
top::IO<a> ::= x::a
{
  top.stateOut = top.stateIn;
  top.stateVal = x;
}

@{-
 - Create a self-referential IO action.
 - Note that fn should be lazy in its argument, to avoid infinite recursion.
 - This can be achieved using unsafeInterleaveIO.
 -
 - @param fn A function creating an IO action from its own result.
 -}
abstract production fixIO
top::IO<a> ::= fn::(IO<a> ::= a)
{
  -- Using unsafeTrace here to ensure that when fn demands its argument,
  -- st.stateOut has been demanded.
  local st::IO<a> = fn(unsafeTrace(st.stateVal, st.stateOut));
  st.stateIn = top.stateIn;
  top.stateOut = st.stateOut;
  top.stateVal = st.stateVal;
}

instance Functor IO {
  map = liftM1;
}

instance Apply IO {
  ap = apM;
}

instance Applicative IO {
  pure = returnIO;
}

instance Bind IO {
  bind = bindIO;
}

instance Monad IO {}

instance MonadFail IO {
  fail = \ msg::String -> do {
    eprintln(msg);
    exit(1);
  };
}

instance MonadFix IO {
  mfix = fixIO;
}

function runIO
IOToken ::= st::IO<a> ioIn::IOToken
{
  return evalIO(^st, ioIn).io;
}

function evalIO
IOVal<a> ::= st::IO<a> ioIn::IOToken
{
  st.stateIn = ioIn;
  return ioval(st.stateOut, st.stateVal);
}

function unsafeEvalIO
a ::= st::IO<a>
{
  local res::IOVal<a> = evalIO(^st, unsafeIO());
  return unsafeTrace(res.iovalue, res.io);
}

@{-
 - Defer an IO action to be lazily evaluated when its result value is demanded.
 -
 - @param i An IO action to defer.
 -}
abstract production unsafeInterleaveIO
top::IO<a> ::= i::IO<a>
{
  i.stateIn = unsafeIO();
  top.stateOut = top.stateIn;
  top.stateVal = i.stateVal;
}

-- Monadic IO wrappers
abstract production stateIO
this::IO<a> ::= f::(IOVal<a> ::= IOToken)
{
  local out::IOVal<a> = f(this.stateIn);
  this.stateOut = out.io;
  this.stateVal = out.iovalue;
}

abstract production stateIOUnit
this::IO<Unit> ::= f::(IOToken ::= IOToken)
{
  local out::IOToken = f(this.stateIn);
  this.stateOut = out;
  -- Using unsafeTrace here to demand stateOut is evaluated before evaluating stateVal
  this.stateVal = unsafeTrace((), this.stateOut);
}

abstract production print
top::IO<Unit> ::= s::String
{
  top.stateOut = printT(s, top.stateIn);
  top.stateVal = unit();
}

fun println IO<Unit> ::= str::String = stateIOUnit(printlnT(str, _));

fun eprint IO<Unit> ::= str::String = stateIOUnit(eprintT(str, _));

fun eprintln IO<Unit> ::= str::String = stateIOUnit(eprintlnT(str, _));

abstract production readLineStdin
top::IO<Maybe<String>> ::=
{
  local res::IOVal<Maybe<String>> = readLineStdinT(top.stateIn);
  top.stateOut = res.io;
  top.stateVal = res.iovalue;
}

-- Having a polymorphic return type lets us write code like:
--
--   if !null(errs) {
--     print(showErrs(errs));
--     exit(1);
--   } else {
--     return value;
--   }
abstract production exit
top::IO<a> ::= val::Integer
{
  top.stateOut = exitT(val, top.stateIn);
  top.stateVal = error("stateOut should've been evaluated first?");
}

abstract production mkdir
top::IO<Boolean> ::= s::String
{
  local res::IOVal<Boolean> = mkdirT(s, top.stateIn);
  top.stateOut = res.io;
  top.stateVal = res.iovalue;
}

abstract production system
top::IO<Integer> ::= s::String
{
  local res::IOVal<Integer> = systemT(s, top.stateIn);
  top.stateOut = res.io;
  top.stateVal = res.iovalue;
}

abstract production writeFile
top::IO<Unit> ::= file::String contents::String
{
  top.stateOut = writeFileT(file, contents, top.stateIn);
  top.stateVal = unit();
}

abstract production writeBinaryFile
top::IO<Unit> ::= file::String contents::ByteArray
{
  top.stateOut = writeBinaryFileT(file, contents, top.stateIn);
  top.stateVal = unit();
}

abstract production appendFile
top::IO<Unit> ::= file::String contents::String
{
  top.stateOut = appendFileT(file, contents, top.stateIn);
  top.stateVal = unit();
}

abstract production fileTime
top::IO<Integer> ::= s::String
{
  local res::IOVal<Integer> = fileTimeT(s, top.stateIn);
  top.stateOut = res.io;
  top.stateVal = res.iovalue;
}

abstract production isFile
top::IO<Boolean> ::= s::String
{
  local res::IOVal<Boolean> = isFileT(s, top.stateIn);
  top.stateOut = res.io;
  top.stateVal = res.iovalue;
}

abstract production isDirectory
top::IO<Boolean> ::= s::String
{
  local res::IOVal<Boolean> = isDirectoryT(s, top.stateIn);
  top.stateOut = res.io;
  top.stateVal = res.iovalue;
}

abstract production readFile
top::IO<String> ::= s::String
{
  local res::IOVal<String> = readFileT(s, top.stateIn);
  top.stateOut = res.io;
  top.stateVal = res.iovalue;
}

abstract production readBinaryFile
top::IO<ByteArray> ::= s::String
{
  local res::IOVal<ByteArray> = readBinaryFileT(s, top.stateIn);
  top.stateOut = res.io;
  top.stateVal = res.iovalue;
}

abstract production isJarFile
top::IO<Boolean> ::= s::String
{
  local res::IOVal<Boolean> = isJarFileT(s, top.stateIn);
  top.stateOut = res.io;
  top.stateVal = res.iovalue;
}

abstract production jarContainsEntry
top::IO<Boolean> ::= jar::String entry::String
{
  local res::IOVal<Boolean> = jarContainsEntryT(jar, entry, top.stateIn);
  top.stateOut = res.io;
  top.stateVal = res.iovalue;
}

abstract production readBinaryJarEntry
top::IO<ByteArray> ::= jar::String entry::String
{
  local res::IOVal<ByteArray> = readBinaryJarEntryT(jar, entry, top.stateIn);
  top.stateOut = res.io;
  top.stateVal = res.iovalue;
}

abstract production cwd
top::IO<String> ::=
{
  local res::IOVal<String> = cwdT(top.stateIn);
  top.stateOut = res.io;
  top.stateVal = res.iovalue;
}

abstract production envVar
top::IO<String> ::= s::String
{
  local res::IOVal<String> = envVarT(s, top.stateIn);
  top.stateOut = res.io;
  top.stateVal = res.iovalue;
}

@{-
 - Returns a list of files in a directory.
 -
 - This is implemented in terms of `java.io.File.list()`, which does **not**
 - guarantee any particular order of files that it returns. Most operating
 - systems do not either, and POSIX does not require that Unix-like operating
 - systems do.
 -}
abstract production listContents
top::IO<[String]> ::= path::String
{
  local res::IOVal<[String]> = listContentsT(path, top.stateIn);
  top.stateOut = res.io;
  top.stateVal = res.iovalue;
}

abstract production deleteFile
top::IO<Boolean> ::= s::String
{
  local res::IOVal<Boolean> = deleteFileT(s, top.stateIn);
  top.stateOut = res.io;
  top.stateVal = res.iovalue;
}

abstract production deleteFiles
top::IO<Boolean> ::= files::[String]
{
  local res::IOVal<Boolean> = deleteFilesT(files, top.stateIn);
  top.stateOut = res.io;
  top.stateVal = res.iovalue;
}

abstract production deleteDirFiles
top::IO<Boolean> ::= s::String
{
  local res::IOVal<Boolean> = deleteDirFilesT(s, top.stateIn);
  top.stateOut = res.io;
  top.stateVal = res.iovalue;
}

abstract production deleteTree
top::IO<Unit> ::= s::String
{
  top.stateOut = deleteTreeT(s, top.stateIn);
  top.stateVal = unit();
}

abstract production copyFile
top::IO<Unit> ::= src::String dst::String
{
  top.stateOut = copyFileT(src, dst, top.stateIn);
  top.stateVal = unit();
}

abstract production touchFile
top::IO<Unit> ::= file::String
{
  top.stateOut = touchFileT(file, top.stateIn);
  top.stateVal = unit();
}

abstract production touchFiles
top::IO<Unit> ::= files::[String]
{
  top.stateOut = touchFilesT(files, top.stateIn);
  top.stateVal = unit();
}
