grammar silver:definition:core;
import silver:definition:env;

synthesized attribute userFriendlyLHS :: Integer;
synthesized attribute doDecorate :: Boolean;
synthesized attribute applicationDispatcher :: Production (Expr ::= Expr Exprs);

attribute doDecorate occurs on TypeRep;
attribute applicationDispatcher occurs on TypeRep;
attribute userFriendlyLHS occurs on TypeRep;

aspect production i_ntTypeRep
top::TypeRep ::= n::String
{
  top.doDecorate = true;
  top.userFriendlyLHS = -1;
}

aspect production i_refTypeRep
top::TypeRep ::= t::Decorated TypeRep
{
  top.userFriendlyLHS = 1;
}

aspect production i_prodTypeRep
top::TypeRep ::= it::[Decorated TypeRep] ot::Decorated TypeRep
{
  top.applicationDispatcher = productionApplicationDispatcher;
}

abstract production productionApplicationDispatcher
top::Expr ::= e::Expr es::Exprs
{
  top.pp = e.pp ++ "(" ++ es.pp ++ ")";
  top.location = e.location;
  top.errors := e.errors ++ es.errors; 

  top.typerep = e.typerep.outputType;

  es.expectedInputTypes = e.typerep.inputTypes;
}


aspect production i_funTypeRep
top::TypeRep ::= it::[Decorated TypeRep] ot::Decorated TypeRep
{
  top.applicationDispatcher = functionApplicationDispatcher;
}

abstract production functionApplicationDispatcher
top::Expr ::= e::Expr es::Exprs
{
  top.pp = e.pp ++ "(" ++ es.pp ++ ")";
  top.location = e.location;
  top.errors := e.errors ++ es.errors; 

  top.typerep = e.typerep.outputType;

  es.expectedInputTypes = e.typerep.inputTypes;
}

aspect production i_defaultTypeRep
top::TypeRep ::= 
{
  top.doDecorate = false;
  top.userFriendlyLHS = 0;
  top.applicationDispatcher = genericApplicationDispatcher;
}

abstract production genericApplicationDispatcher
top::Expr ::= e::Expr es::Exprs
{
  top.pp = e.pp ++ "(" ++ es.pp ++ ")";
  top.location = e.location;
  top.errors := e.errors ++ es.errors; 

  top.typerep = topTypeRep();

  es.expectedInputTypes = [];
}