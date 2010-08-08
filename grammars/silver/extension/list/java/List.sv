grammar silver:extension:list:java;

import silver:definition:core;
import silver:definition:env;
import silver:extension:list;
import silver:translation:java:core;
import silver:translation:java:env;

import silver:translation:java:concrete_syntax:copper; -- todo : part of wrapThunk hack

aspect production emptyList
top::Expr ::= '[' ']'
{
  top.translation = "common.ConsCell.nil";
}

aspect production emptyListWType
top::Expr ::= '[' '::' t::Type ']'
{
  top.translation = "common.ConsCell.nil";
}

aspect production fullList
top::Expr ::= '[' es::Exprs ']'
{ 
  top.translation = buildListLiteral(es.exprs, top.actionCodeType.isSemanticBlock);
}

function buildListLiteral
String ::= exps::[Decorated Expr] doit::Boolean
{
  return if null(exps)
         then "common.ConsCell.nil"
         else "new common.ConsCell(" ++ wrapThunk(head(exps), doit) ++ ", " ++ buildListLiteral(tail(exps), doit) ++ ")";
}

aspect production consList
top::Expr ::= 'cons' '(' h::Expr ',' t::Expr ')'
{ 
  top.translation = "(new common.ConsCell(" ++ wrapThunk(h, top.actionCodeType.isSemanticBlock) ++ ", " ++ wrapThunk(t, top.actionCodeType.isSemanticBlock) ++ "))";
}

aspect production appendList
top::Expr ::= l::Expr r::Expr
{
  -- Technically, append is not a constructor, it's a function.  And it's strict in its first argument.
  -- so we *could* avoid wrapping it up in a thunk here... but this paradoxically worsens memory usage. :(
  top.translation = "(new common.AppendCell(" ++ wrapThunk(l, top.actionCodeType.isSemanticBlock) ++ ", " ++ wrapThunk(r, top.actionCodeType.isSemanticBlock) ++ "))";
}

aspect production listLength
top::Expr ::= e::Expr
{
  top.translation = "(new Integer(((common.ConsCell)" ++ e.translation ++ ").length()))";
}

aspect production nullList
top::Expr ::= 'null' '(' l::Expr ')'
{ 
  top.translation = "((common.ConsCell)" ++ l.translation ++ ").nil()";
}

aspect production headList
top::Expr ::= 'head' '(' l::Expr ')'
{ 
  top.translation = "((" ++ l.typerep.listComponent.transType ++ ")((common.ConsCell)" ++ l.translation ++ ").head())";
}

aspect production tailList
top::Expr ::= 'tail' '(' l::Expr ')'
{ 
  top.translation = "((common.ConsCell)" ++ l.translation ++ ").tail()";
}

-- TypeRep

aspect production i_listTypeRep
top::TypeRep ::= e::Boolean tr::Decorated TypeRep
{
  top.isNonTerminal = false;
  top.transType = "common.ConsCell";
}

