grammar silver:compiler:modification:ffi:java;

import silver:compiler:modification:ffi;
import silver:compiler:modification:ffi:util;
import silver:compiler:translation:java:core;
import silver:compiler:translation:java:type;
import silver:compiler:definition:core;
import silver:compiler:definition:env;
import silver:compiler:definition:type;
import silver:compiler:definition:flow:env;

synthesized attribute ffiTranslationString :: [String] occurs on FFIDef, FFIDefs;

aspect production ffidefsOne
top::FFIDefs ::= one::FFIDef
{
  top.ffiTranslationString = one.ffiTranslationString;
}

aspect production ffidefsMany
top::FFIDefs ::= one::FFIDef more::FFIDefs
{
  top.ffiTranslationString = one.ffiTranslationString ++ more.ffiTranslationString;
}

aspect production ffidef
top::FFIDef ::= name::String_t ':' 'return' code::String_t ';'
{
  top.ffiTranslationString = if name.lexeme == "\"java\"" then [cleanStringLexeme(code.lexeme)] else [];
}

function strictChildAccessor
String ::= ns::NamedSignatureElement
{
  -- TODO: Slight bug here, if we refer to an argument more than once in an FFI string,
  -- then we may evaluate argument thunks more than once!
  -- E.g. "java": "Foo.bar(%x%, %x%)"
  return "common.Util.<" ++ ns.typerep.transType ++ ">demand(" ++ ns.childRefElem ++ ")";
}

fun computeSigTranslation String ::= str::String sig::NamedSignature =
  substituteAll(str,
    map(wrapStrictNotation, sig.inputNames) ++ map(wrapLazyNotation, sig.inputNames) ++ map(wrapContextNotation, range(0, length(sig.contexts))),
    map(strictChildAccessor, sig.inputElements) ++ map((.childRefElem), sig.inputElements) ++ map(\ c::Context -> decorate c with {boundVariables = sig.freeVariables;}.contextRefElem, sig.contexts));


-- TODO: this needs clean up.
-- We should forward either to normal function declaration or special one, rather than IFing EVERYTHING in here!
aspect production functionDclFFI
top::AGDcl ::= 'function' id::Name ns::FunctionSignature body::ProductionBody 'foreign' '{' ffidefs::FFIDefs '}'
{
  top.setupInh := if null(ffidefs.ffiTranslationString)
                  then forward.setupInh
                  else ""; -- hacky hacky!  -- TODO should these be there, or empty?
  top.initProd := if null(ffidefs.ffiTranslationString)
                  then forward.initProd
                  else ""; -- hacky hacky!  -- TODO should these be there, or empty?
  top.initValues := "";
  top.postInit := "";

  top.genFilesUnescapedUp := [id.name];
  top.genFiles := if null(ffidefs.ffiTranslationString)
                    then forward.genFiles
                    else 
                    [("P" ++ escapeName(id.name, top.genFilesUnescapedDown) ++ ".java",
                      generateFunctionClassString(body.env, top.flowEnv, top.grammarName, id.name, namedSig, "return (" ++ namedSig.outputElement.typerep.transClassType ++ ")" ++ computeSigTranslation(head(ffidefs.ffiTranslationString), namedSig) ++ ";\n", top.genFilesUnescapedDown)
                    )];

  top.errors <- if length(ffidefs.ffiTranslationString) > 1
                then [errFromOrigin(ffidefs, "There is more than one Java translation in this FFI function")]
                else [];
}

