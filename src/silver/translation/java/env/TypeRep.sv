grammar silver:translation:java:env;

import silver:definition:env;

synthesized attribute transType :: String;
attribute transType occurs on TypeRep;

aspect production i_integerTypeRep
top::TypeRep ::= 
{
  top.transType = "Integer";
}

aspect production i_floatTypeRep
top::TypeRep ::= 
{
  top.transType = "Float";
}


aspect production i_stringTypeRep
top::TypeRep ::= 
{
  top.transType = "StringBuffer";
}

aspect production i_booleanTypeRep
top::TypeRep ::= 
{
  top.transType = "Boolean";
}

aspect production i_termTypeRep
top::TypeRep ::= n::String r::String
{
  top.transType = "common.Terminal";
}

aspect production i_ntTypeRep
top::TypeRep ::= n::String
{
  top.transType = "common.Node";
}

aspect production i_refTypeRep
top::TypeRep ::= t::Decorated TypeRep
{
  top.transType = "common.DecoratedNode";
}

aspect production i_prodTypeRep
top::TypeRep ::= it::[Decorated TypeRep] ot::Decorated TypeRep
{
  top.transType = "java.lang.reflect.Constructor";
}
aspect production i_funTypeRep
top::TypeRep ::= it::[Decorated TypeRep] ot::Decorated TypeRep
{
  top.transType = "java.lang.reflect.Constructor";
}
aspect production i_defaultTypeRep
top::TypeRep ::= 
{
  top.transType = "Object";
}