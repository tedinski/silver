grammar silver:analysis:typechecking:core;
import silver:definition:core;
import silver:definition:env;
import silver:util;

aspect production defaultProductionBody
top::ProductionBody ::= stmts::ProductionStmts
{
  top.typeErrors = stmts.typeErrors;
}

aspect production productionStmtsNone
top::ProductionStmts ::= 
{
  top.typeErrors = [];
}

aspect production productionStmts
top::ProductionStmts ::= stmt::ProductionStmt
{
  top.typeErrors = stmt.typeErrors;
}

aspect production productionStmtsCons
top::ProductionStmts ::= h::ProductionStmt t::ProductionStmts
{
  top.typeErrors = h.typeErrors ++ t.typeErrors;
}

aspect production productionStmtsAppend
top::ProductionStmts ::= h::ProductionStmts t::ProductionStmts
{
  top.typeErrors = h.typeErrors ++ t.typeErrors;
}

aspect production forwardsTo
top::ProductionStmt ::= 'forwards' 'to' e::Expr ';'
{
  local attribute er1 :: [Decorated Message];
  er1 = if e.typerep.isNonTerminal then [] else [err(top.location, "You must forward to a NonTerminal.")];

  local attribute lhsT :: Decorated TypeRep;
  lhsT = top.signature.outputElement.typerep;

  local attribute er2 :: [Decorated Message];
  er2 = if lhsT.typeEquals(lhsT, e.typerep).bValue
	then []
	else [err(top.location, "You must forward to a NonTerminal of type '" ++ lhsT.typeName ++ "'.")];

  top.typeErrors = e.typeErrors ++ er1 ++ er2;
}

aspect production forwardsToWith
top::ProductionStmt ::= 'forwards' 'to' e::Expr 'with' '{' inh::ForwardInhs '}' ';'
{
  local attribute er1 :: [Decorated Message];
  er1 = if e.typerep.isNonTerminal then [] else [err(top.location, "You must forward to a NonTerminal.")];

  local attribute lhsT :: Decorated TypeRep;
  lhsT = top.signature.outputElement.typerep;

  local attribute er2 :: [Decorated Message];
  er2 = if lhsT.typeEquals(lhsT, e.typerep).bValue
	then []
	else [err(top.location, "You must forward to a NonTerminal of type '" ++ lhsT.typeName ++ "'.")];


  top.typeErrors = e.typeErrors ++ inh.typeErrors ++ er1 ++ er2;
}

aspect production forwardingWith
top::ProductionStmt ::= 'forwarding' 'with' '{' inh::ForwardInhs '}' ';'
{
  top.typeErrors = inh.typeErrors;
}

aspect production forwardInh
top::ForwardInh ::= lhs::ForwardLHSExpr '=' e::Expr ';'
{
  local attribute valid :: Boolean;
  valid = lhs.typerep.typeEquals(lhs.typerep, e.typerep).bValue;

  local attribute er :: [Decorated Message];
  er = if valid 
       then [] 
       else [err(top.location, "The LHS and RHS of the assignment must be the same type.\n" ++
           "\tInstead they are '" ++ lhs.typerep.unparse ++ "' and '" ++ e.typerep.unparse ++ "'")] ; 

  top.typeErrors = er ++ e.typeErrors ++ lhs.typeErrors; 
}

aspect production forwardInhsOne
top::ForwardInhs ::= lhs::ForwardInh
{
  top.typeErrors = lhs.typeErrors;
}

aspect production forwardInhsCons
top::ForwardInhs ::= lhs::ForwardInh rhs::ForwardInhs
{
  top.typeErrors = lhs.typeErrors ++ rhs.typeErrors;
}

aspect production forwardLhsExpr
top::ForwardLHSExpr ::= q::QName
{
  top.typeErrors = [];
}

aspect production localAttributeDcl
top::ProductionStmt ::= 'local' 'attribute' a::Name '::' te::Type ';'
{
  top.typeErrors = [];
}

aspect production productionAttributeDcl
top::ProductionStmt ::= 'production' 'attribute' a::Name '::' te::Type ';'
{
  top.typeErrors = [];
}

aspect production returnDef
top::ProductionStmt ::= 'return' e::Expr ';'
{
  local attribute valid :: Boolean;
  valid = top.signature.outputElement.typerep.typeEquals(top.signature.outputElement.typerep, e.typerep).bValue;

  local attribute er :: [Decorated Message];
  er = if valid 
       then [] 
       else [err(top.location, "Invalid return type.\n" ++
                                  "(expected)\n   " ++ top.signature.outputElement.typerep.unparse ++ "\n(actual)\n   " ++ e.typerep.unparse)] ; 

  top.typeErrors = er ++ e.typeErrors;
}

aspect production attributeDef
top::ProductionStmt ::= val::QName '.' attr::QName '=' e::Expr ';'
{
  local attribute er :: [Decorated Message];
  er = if attr.lookupAttribute.typerep.typeEquals(attr.lookupAttribute.typerep, e.typerep).bValue
       then [] 
       else [err(top.location, "Attribute " ++ attr.name ++ " has type " ++ attr.lookupAttribute.typerep.unparse ++ " but the expression being assigned to it has type " ++ e.typerep.unparse)] ; 

  local attribute e1 :: [Decorated Message];
  e1 = if !doesOccurOn(attr.lookupAttribute.fullName, val.lookupValue.typerep.typeName, top.env)
       then [err(top.location, "Attribute '" ++ attr.lookupAttribute.fullName ++ "' does not decorate type '" ++ val.lookupValue.typerep.typeName ++ "'.")]
       else [];

  local attribute e2 :: [Decorated Message];
  e2 = if val.name == top.signature.outputElement.elementName && attr.lookupAttribute.typerep.isInherited
       then [err(top.location, "Cannot assign to the lhs's inherited attributes.")]
       else [];

  local attribute e3 :: [Decorated Message];
  e3 = if attr.lookupAttribute.typerep.isSynthesized && val.name != top.signature.outputElement.elementName
       then [err(top.location, "Assignment to synthesized attributes only permitted for the lhs.")]
       else [];

  top.typeErrors = er ++ e1 ++ e2 ++ e3 ++ e.typeErrors;
}

aspect production valueDef
top::ProductionStmt ::= val::QName '=' e::Expr ';'
{
  local attribute er :: [Decorated Message];
  er = if val.lookupValue.typerep.typeEquals(val.lookupValue.typerep, e.typerep).bValue
       then [] 
       else [err(top.location, "Value " ++ val.name ++ " has type " ++ val.lookupValue.typerep.unparse ++ " but the expression being assigned to it has type " ++ e.typerep.unparse)] ; 

  local attribute e2 :: [Decorated Message];
  e2 = if val.name == top.signature.outputElement.elementName
       then [err(top.location, "Cannot assign to the lhs.")]
       else [];

  top.typeErrors = er ++ e2 ++ e.typeErrors;
}

