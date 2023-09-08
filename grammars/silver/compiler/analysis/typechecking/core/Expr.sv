grammar silver:compiler:analysis:typechecking:core;

import silver:compiler:definition:flow:env;

attribute upSubst, downSubst, finalSubst occurs on Expr, ExprInhs, ExprInh, Exprs, AppExprs, AppExpr, AnnoExpr, AnnoAppExprs;

propagate upSubst, downSubst
   on Expr, ExprInhs, ExprInh, Exprs, AppExprs, AppExpr, AnnoExpr, AnnoAppExprs
   excluding
     and, or, notOp, ifThenElse, plus, minus, multiply, divide, modulus,
     exprInh, presentAppExpr, decorationSiteExpr,
     terminalConstructor, noteAttachment;
propagate finalSubst on Expr, ExprInhs, ExprInh, Exprs, AppExprs, AppExpr, AnnoExpr, AnnoAppExprs;

attribute finalType occurs on Expr;
attribute contexts occurs on Expr;
aspect default production
top::Expr ::=
{
  top.finalType = performSubstitution(top.typerep, top.finalSubst).defaultSpecialization;
  top.contexts = [];
}

aspect production productionReference
top::Expr ::= q::Decorated! QName
{
  contexts.contextLoc = q.location;
  contexts.contextSource = "the use of " ++ q.name;
  top.errors <- contexts.contextErrors;
  top.contexts = typeScheme.contexts;
}

aspect production functionReference
top::Expr ::= q::Decorated! QName
{
  contexts.contextLoc = q.location;
  contexts.contextSource = "the use of " ++ q.name;
  top.errors <- contexts.contextErrors;
  top.contexts = typeScheme.contexts;
}

aspect production globalValueReference
top::Expr ::= q::Decorated! QName
{
  contexts.contextLoc = q.location;
  contexts.contextSource = "the use of " ++ q.name;
  top.errors <- contexts.contextErrors;
  top.contexts = typeScheme.contexts;
}

aspect production classMemberReference
top::Expr ::= q::Decorated! QName
{
  instHead.contextLoc = q.location;
  instHead.contextSource = "the use of " ++ q.name;
  top.errors <- instHead.contextErrors;
  
  contexts.contextLoc = q.location;
  contexts.contextSource = "the use of " ++ q.name;
  top.errors <- contexts.contextErrors;
  
  top.contexts = typeScheme.contexts;
}

aspect production application
top::Expr ::= e::Expr '(' es::AppExprs ',' anns::AnnoAppExprs ')'
{
  propagate upSubst, downSubst, finalSubst;
}

aspect production access
top::Expr ::= e::Expr '.' q::QNameAttrOccur
{
  propagate upSubst, downSubst, finalSubst;
}

aspect production undecoratedAccessHandler
top::Expr ::= e::Decorated! Expr  q::Decorated! QNameAttrOccur
{
  -- TECHNICALLY, I think the current implementation makes this impossible,
  -- But let's leave it since it's the right thing to do.
  top.errors <-
    if e.finalType.isDecorated && q.found
    then [err(top.location, "Access of " ++ q.name ++ " from a decorated type.")]
    else [];
}

aspect production accessBouncer
top::Expr ::= target::(Expr ::= Decorated! Expr  Decorated! QNameAttrOccur  Location) e::Expr  q::Decorated! QNameAttrOccur
{
  propagate upSubst, downSubst, finalSubst;
}

aspect production forwardAccess
top::Expr ::= e::Expr '.' 'forward'
{
  top.errors <-
    if !e.finalType.isDecorated
    then [err(top.location, "Attribute forward being accessed from an undecorated type.")]
    else [];
}

aspect production decoratedAccessHandler
top::Expr ::= e::Decorated! Expr  q::Decorated! QNameAttrOccur
{
  -- TECHNICALLY, I think the current implementation makes this impossible,
  -- But let's leave it since it's the right thing to do.
  top.errors <-
    if !e.finalType.isDecorated
    then [err(top.location, "Attribute " ++ q.name ++ " being accessed from an undecorated type.")]
    else [];
}


aspect production noteAttachment
top::Expr ::= 'attachNote' note::Expr 'on' e::Expr 'end'
{
  local attribute errCheck1 :: TypeCheck; errCheck1.finalSubst = top.finalSubst;
  local attribute errCheck2 :: TypeCheck; errCheck2.finalSubst = top.finalSubst;

  thread downSubst, upSubst on top, note, e, errCheck1, top;
  
  errCheck1 = check(note.typerep, nonterminalType("silver:core:OriginNote", [], true, false));
  top.errors <-
       if errCheck1.typeerror
       then [err(top.location, "First argument to attachNote must be OriginNote, was " ++ errCheck1.leftpp)]
       else [];
}

aspect production and
top::Expr ::= e1::Expr '&&' e2::Expr
{
  local attribute errCheck1 :: TypeCheck; errCheck1.finalSubst = top.finalSubst;
  local attribute errCheck2 :: TypeCheck; errCheck2.finalSubst = top.finalSubst;

  thread downSubst, upSubst on top, e1, e2, errCheck1, errCheck2, top;
  
  errCheck1 = check(e1.typerep, boolType());
  errCheck2 = check(e2.typerep, boolType());
  top.errors <-
       if errCheck1.typeerror
       then [err(e1.location, "First operand to && must be type bool. Got instead type " ++ errCheck1.leftpp)]
       else [];
  top.errors <-
       if errCheck2.typeerror
       then [err(e2.location, "First operand to && must be type bool. Got instead type " ++ errCheck2.leftpp)]
       else [];
}

aspect production or
top::Expr ::= e1::Expr '||' e2::Expr
{
  local attribute errCheck1 :: TypeCheck; errCheck1.finalSubst = top.finalSubst;
  local attribute errCheck2 :: TypeCheck; errCheck2.finalSubst = top.finalSubst;

  thread downSubst, upSubst on top, e1, e2, errCheck1, errCheck2, top;
  
  errCheck1 = check(e1.typerep, boolType());
  errCheck2 = check(e2.typerep, boolType());
  top.errors <-
       if errCheck1.typeerror
       then [err(e1.location, "First operand to || must be type bool. Got instead type " ++ errCheck1.leftpp)]
       else [];
  top.errors <-
       if errCheck2.typeerror
       then [err(e2.location, "First operand to || must be type bool. Got instead type " ++ errCheck2.leftpp)]
       else [];
}

aspect production notOp
top::Expr ::= '!' e1::Expr
{
  local attribute errCheck1 :: TypeCheck; errCheck1.finalSubst = top.finalSubst;
  
  thread downSubst, upSubst on top, e1, errCheck1, top;
  
  errCheck1 = check(e1.typerep, boolType());
  top.errors <-
       if errCheck1.typeerror
       then [err(e1.location, "Operand to ! must be type bool. Got instead type " ++ errCheck1.leftpp)]
       else [];
}

aspect production ifThenElse
top::Expr ::= 'if' e1::Expr 'then' e2::Expr 'else' e3::Expr
{
  local attribute errCheck1 :: TypeCheck; errCheck1.finalSubst = top.finalSubst;
  local attribute errCheck2 :: TypeCheck; errCheck2.finalSubst = top.finalSubst;

  thread downSubst, upSubst on top, e1, e2, e3, errCheck1, errCheck2, top;
  
  errCheck1 = check(e2.typerep, e3.typerep);
  errCheck2 = check(e1.typerep, boolType());
  top.errors <-
       if errCheck1.typeerror
       then [err(top.location, "Then and else branch must have the same type. Instead they are " ++ errCheck1.leftpp ++ " and " ++ errCheck1.rightpp)]
       else [];
  top.errors <-
       if errCheck2.typeerror
       then [err(e1.location, "Condition must have the type Boolean. Instead it is " ++ errCheck2.leftpp)]
       else [];
}

aspect production plus
top::Expr ::= e1::Expr '+' e2::Expr
{
  local attribute errCheck1 :: TypeCheck; errCheck1.finalSubst = top.finalSubst;

  thread downSubst, upSubst on top, e1, e2, errCheck1, top;
  
  errCheck1 = check(e1.typerep, e2.typerep);
  top.errors <-
       if errCheck1.typeerror
       then [err(top.location, "Operands to + must be the same type. Instead they are " ++ errCheck1.leftpp ++ " and " ++ errCheck1.rightpp)]
       else [];

  top.errors <-
       if e1.finalType.instanceNum
       then []
       else [err(top.location, "Operands to + must be concrete types Integer or Float.  Instead they are of type " ++ prettyType(e1.finalType))];
}

aspect production minus
top::Expr ::= e1::Expr '-' e2::Expr
{
  local attribute errCheck1 :: TypeCheck; errCheck1.finalSubst = top.finalSubst;

  thread downSubst, upSubst on top, e1, e2, errCheck1, top;
  
  errCheck1 = check(e1.typerep, e2.typerep);
  top.errors <-
       if errCheck1.typeerror
       then [err(top.location, "Operands to - must be the same type. Instead they are " ++ errCheck1.leftpp ++ " and " ++ errCheck1.rightpp)]
       else [];

  top.errors <-
       if e1.finalType.instanceNum
       then []
       else [err(top.location, "Operands to - must be concrete types Integer or Float.  Instead they are of type " ++ prettyType(e1.finalType))];
}
aspect production multiply
top::Expr ::= e1::Expr '*' e2::Expr
{
  local attribute errCheck1 :: TypeCheck; errCheck1.finalSubst = top.finalSubst;

  thread downSubst, upSubst on top, e1, e2, errCheck1, top;
  
  errCheck1 = check(e1.typerep, e2.typerep);
  top.errors <-
       if errCheck1.typeerror
       then [err(top.location, "Operands to * must be the same type. Instead they are " ++ errCheck1.leftpp ++ " and " ++ errCheck1.rightpp)]
       else [];

  top.errors <-
       if e1.finalType.instanceNum
       then []
       else [err(top.location, "Operands to * must be concrete types Integer or Float.  Instead they are of type " ++ prettyType(e1.finalType))];
}
aspect production divide
top::Expr ::= e1::Expr '/' e2::Expr
{
  local attribute errCheck1 :: TypeCheck; errCheck1.finalSubst = top.finalSubst;

  thread downSubst, upSubst on top, e1, e2, errCheck1, top;
  
  errCheck1 = check(e1.typerep, e2.typerep);
  top.errors <-
       if errCheck1.typeerror
       then [err(top.location, "Operands to / must be the same type. Instead they are " ++ errCheck1.leftpp ++ " and " ++ errCheck1.rightpp)]
       else [];

  top.errors <-
       if e1.finalType.instanceNum
       then []
       else [err(top.location, "Operands to / must be concrete types Integer or Float.  Instead they are of type " ++ prettyType(e1.finalType))];
}
aspect production modulus
top::Expr ::= e1::Expr '%' e2::Expr
{
  local attribute errCheck1 :: TypeCheck; errCheck1.finalSubst = top.finalSubst;

  thread downSubst, upSubst on top, e1, e2, errCheck1, top;
  
  errCheck1 = check(e1.typerep, e2.typerep);
  top.errors <-
       if errCheck1.typeerror
       then [err(top.location, "Operands to % must be the same type. Instead they are " ++ errCheck1.leftpp ++ " and " ++ errCheck1.rightpp)]
       else [];

  top.errors <-
       if e1.finalType.instanceNum
       then []
       else [err(top.location, "Operands to % must be concrete types Integer or Float.  Instead they are of type " ++ prettyType(e1.finalType))];
}
aspect production neg
top::Expr ::= '-' e1::Expr
{
  
  top.errors <-
       if e1.finalType.instanceNum
       then []
       else [err(top.location, "Operand to unary - must be concrete types Integer or Float.  Instead it is of type " ++ prettyType(e1.finalType))];
}

aspect production terminalConstructor
top::Expr ::= 'terminal' '(' t::TypeExpr ',' es::Expr ',' el::Expr ')'
{
  local attribute errCheck1 :: TypeCheck; errCheck1.finalSubst = top.finalSubst;
  local attribute errCheck2 :: TypeCheck; errCheck2.finalSubst = top.finalSubst;

  thread downSubst, upSubst on top, es, el, errCheck1, errCheck2, top;
  
  errCheck1 = check(es.typerep, stringType());
  errCheck2 = check(el.typerep, nonterminalType("silver:core:Location", [], true, false));
  top.errors <-
    if errCheck1.typeerror
    then [err(es.location, "Second operand to 'terminal(type,lexeme,location)' must be a String, instead it is " ++ errCheck1.leftpp)]
    else [];

  top.errors <-
    if errCheck2.typeerror
    then [err(el.location, "Third operand to 'terminal(type,lexeme,location)' must be a Location, instead it is " ++ errCheck2.leftpp)]
    else [];
  
  top.errors <-
    if t.typerep.isTerminal || t.typerep.isError
    then []
    else [err(t.location, "First operand to 'terminal(type,lexeme,location)' must be a Terminal type, instead it is " ++ prettyType(t.typerep))];
}

aspect production decorateExprWith
top::Expr ::= 'decorate' e::Expr 'with' '{' inh::ExprInhs '}'
{
  top.errors <-
       if !isDecorable(e.finalType, top.env)
       then [err(top.location, "Operand to decorate must be a decorable type.  Instead it is of type " ++ prettyType(e.finalType))]
       else [];
}

aspect production decorationSiteExpr
top::Expr ::= '@' e::Expr
{
  local attribute errCheck1 :: TypeCheck; errCheck1.finalSubst = top.finalSubst;

  thread downSubst, upSubst on top, e, errCheck1, top;

  errCheck1 = check(e.typerep, makeDecoratedType(uniqueType(), inhSetType([]), freshType()));
  top.errors <-
       if errCheck1.typeerror
       then [err(top.location, "Operand to @ must be a unique reference with no inherited attributes.  Instead it is of type " ++ errCheck1.leftpp)]
       else [];
}

aspect production exprInh
top::ExprInh ::= lhs::ExprLHSExpr '=' e1::Expr ';'
{
  local attribute errCheck1 :: TypeCheck; errCheck1.finalSubst = top.finalSubst;

  thread downSubst, upSubst on top, e1, errCheck1, top;
  
  errCheck1 = check(lhs.typerep, e1.typerep);
  top.errors <-
       if errCheck1.typeerror
       then [err(top.location, lhs.name ++ " has expected type " ++ errCheck1.leftpp
                              ++ ", but the expression has type " ++ errCheck1.rightpp)]
       else [];
}

aspect production presentAppExpr
top::AppExpr ::= e::Expr
{
  local attribute errCheck1 :: TypeCheck; errCheck1.finalSubst = top.finalSubst;

  thread downSubst, upSubst on top, e, errCheck1, top;
  
  errCheck1 = check(e.typerep, top.appExprTyperep);
  top.errors <-
    if !errCheck1.typeerror then []
    else [err(top.location, "Argument " ++ toString(top.appExprIndex+1) ++ " of function '" ++
            top.appExprApplied ++ "' expected " ++ errCheck1.rightpp ++
            " but argument is of type " ++ errCheck1.leftpp)];  
}

-- See documentation for major restriction on use of @.
-- Essentially, the referred expression MUST have already been type checked.
