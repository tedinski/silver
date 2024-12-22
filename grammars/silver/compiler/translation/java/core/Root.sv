grammar silver:compiler:translation:java:core;

{--
 - Java classes to generate. (filename, contents)
 -}
monoid attribute genFiles :: [Pair<String String>];
{--
 - The unescaped names of the Java classes that would be generated. This is
 - used to detect when case-folding would otherwise break the build. Filenames
 - are collected, passed up, then in the RootSpec they get converted to
 - lowercase and passed back down.
 -}
monoid attribute genFilesUnescapedUp :: [String];
{-- See genFilesUnescapedUp. -}
inherited attribute genFilesUnescapedDown :: [String];
{--
 - Used for svib files.
 -}
monoid attribute genBinaryFiles :: [Pair<String ByteArray>];
{--
 - Early initializers: occurs.add, local's inh attr map creation, collection object creation
 -}
monoid attribute setupInh :: String;
{--
 - Initialize the attributes maps for each production.
 - note to be confused with "production attribute" dcls.
 -}
monoid attribute initProd :: String;
{--
 - Global values.
 -}
monoid attribute initValues :: String;
{--
 - Late initializers.
 -}
monoid attribute postInit :: String;

synthesized attribute translation :: String;
{--
 - Initial values for early weaving. e.g. counter for # attributes on NT
 -}
monoid attribute initWeaving :: String;
{--
 - Values computed by early weaving. e.g. index of attribute in NT arrays
 -}
monoid attribute valueWeaving :: String;

attribute genFiles,genFilesUnescapedUp,genFilesUnescapedDown,setupInh,initProd,initValues,postInit,initWeaving,valueWeaving occurs on Root, AGDcls, AGDcl, Grammar;

propagate genFiles,genFilesUnescapedUp,genFilesUnescapedDown,setupInh,initProd,initValues,postInit,initWeaving,valueWeaving on Root, AGDcls, Grammar;

aspect default production
top::AGDcl ::=
{
  -- Empty values as defaults
  propagate genFiles,genFilesUnescapedUp,genFilesUnescapedDown,setupInh,initProd,initValues,postInit,initWeaving,valueWeaving;
}

aspect production appendAGDcl
top::AGDcl ::= h::AGDcl t::AGDcl
{
  propagate genFiles,genFilesUnescapedUp,genFilesUnescapedDown,setupInh,initProd,initValues,postInit,initWeaving,valueWeaving;
}
