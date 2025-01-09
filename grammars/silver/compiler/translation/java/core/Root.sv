grammar silver:compiler:translation:java:core;

{--
 - Java classes to generate. (filename, contents)
 -}
monoid attribute genFiles :: [Pair<String String>];
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

attribute genFiles,setupInh,initProd,initValues,postInit,initWeaving,valueWeaving occurs on File, AGDcls, AGDcl, Grammar;

propagate genFiles,setupInh,initProd,initValues,postInit,initWeaving,valueWeaving on File, AGDcls, Grammar;

aspect default production
top::AGDcl ::=
{
  -- Empty values as defaults
  propagate genFiles,setupInh,initProd,initValues,postInit,initWeaving,valueWeaving;
}

aspect production appendAGDcl
top::AGDcl ::= h::AGDcl t::AGDcl
{
  propagate genFiles,setupInh,initProd,initValues,postInit,initWeaving,valueWeaving;
}
