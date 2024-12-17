grammar silver:compiler:analysis:typechecking:core;

import silver:compiler:definition:flow:env;

attribute upSubst, downSubst, upSubst2, downSubst2, finalSubst occurs on
  Expr, ExprInhs, ExprInh, Exprs, AppExprs, AppExpr, AnnoExpr, AnnoAppExprs;

flowtype Expr = upSubst {forward}, finalType {forward};

propagate upSubst, downSubst
   on Expr, ExprInhs, ExprInh, Exprs, AppExprs, AppExpr, AnnoExpr, AnnoAppExprs
   excluding
     undecoratedAccessHandler, forwardAccess, decoratedAccessHandler, ifThenElse,
     decorateExprWith, exprInh, presentAppExpr, decorationSiteExpr,
     terminalConstructor, noteAttachment;
propagate @upSubst2, @downSubst2
  on Expr, ExprInhs, ExprInh, Exprs, AppExprs, AppExpr, AnnoExpr, AnnoAppExprs
  excluding
    childReference, lhsReference, localReference, forwardReference, transDecoratedAccessHandler,
    productionReference, functionReference, globalValueReference, classMemberReference;
propagate finalSubst on Expr, ExprInhs, ExprInh, Exprs, AppExprs, AppExpr, AnnoExpr, AnnoAppExprs;

attribute finalType occurs on Expr;
aspect default production
top::Expr ::=
{
  top.finalType = performSubstitution(top.typerep, top.finalSubst);
}

aspect production childReference
top::Expr ::= @q::QName
{
  -- This is safe, even if the child isn't decorable.
  -- The only way a fresh type var can appear in top.typerep is via .asDecoratedType
  top.upSubst2 = specializeRefSet(top.downSubst2, top.typerep);
}

aspect production lhsReference
top::Expr ::= @q::QName
{
  top.upSubst2 = specializeRefSet(top.downSubst2, top.typerep);
}

aspect production localReference
top::Expr ::= @q::QName
{
  -- This is safe, even if the child isn't decorable.
  -- The only way a fresh type var can appear in top.typerep is via .asDecoratedType
  top.upSubst2 = specializeRefSet(top.downSubst2, top.typerep);
}

aspect production forwardReference
top::Expr ::= @q::QName
{
  top.upSubst2 = specializeRefSet(top.downSubst2, top.typerep);
}

aspect production transDecoratedAccessHandler
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  top.upSubst2 =
    if q.attrFound
    then specializeTransRefSet(top.downSubst2, top.typerep, e.typerep, q.attrDcl.fullName)
    else specializeRefSet(top.downSubst2, top.typerep);
}

aspect production productionReference
top::Expr ::= @q::QName
{
  production specContexts::Contexts =
    foldContexts(map(performContextSubstitution(_, top.downSubst2), typeScheme.contexts));
  specContexts.env = top.env;
  specContexts.flowEnv = top.flowEnv;
  top.upSubst2 = composeSubst(top.downSubst2, specContexts.contextSpecialization);

  contexts.contextLoc = q.nameLoc;
  contexts.contextSource = "the use of " ++ q.name;
  top.errors <- contexts.contextErrors;
}

aspect production functionReference
top::Expr ::= @q::QName
{
  production specContexts::Contexts =
    foldContexts(map(performContextSubstitution(_, top.downSubst2), typeScheme.contexts));
  specContexts.env = top.env;
  specContexts.flowEnv = top.flowEnv;
  top.upSubst2 = composeSubst(top.downSubst2, specContexts.contextSpecialization);

  contexts.contextLoc = q.nameLoc;
  contexts.contextSource = "the use of " ++ q.name;
  top.errors <- contexts.contextErrors;
}

aspect production globalValueReference
top::Expr ::= @q::QName
{
  production specContexts::Contexts =
    foldContexts(map(performContextSubstitution(_, top.downSubst2), typeScheme.contexts));
  specContexts.env = top.env;
  specContexts.flowEnv = top.flowEnv;
  top.upSubst2 = composeSubst(top.downSubst2, specContexts.contextSpecialization);

  contexts.contextLoc = q.nameLoc;
  contexts.contextSource = "the use of " ++ q.name;
  top.errors <- contexts.contextErrors;
}

aspect production classMemberReference
top::Expr ::= @q::QName
{
  production specContexts::Contexts =
    foldContexts(map(performContextSubstitution(_, top.downSubst2), typeScheme.contexts));
  specContexts.env = top.env;
  specContexts.flowEnv = top.flowEnv;
  top.upSubst2 = composeSubst(top.downSubst2, specContexts.contextSpecialization);

  instHead.contextLoc = q.nameLoc;
  instHead.contextSource = "the use of " ++ q.name;
  top.errors <- instHead.contextErrors;
  
  contexts.contextLoc = q.nameLoc;
  contexts.contextSource = "the use of " ++ q.name;
  top.errors <- contexts.contextErrors;
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
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  -- TODO: remove?
  local attribute errCheck1 :: TypeCheck; errCheck1.finalSubst = top.finalSubst;
  errCheck1 = checkNonterminal(top.env, true, e.typerep);

  -- TECHNICALLY, I think the current implementation makes this impossible,
  -- But let's leave it since it's the right thing to do.
  top.errors <-
    if errCheck1.typeerror && q.found
    then [errFromOrigin(top, "Access of " ++ q.name ++ " from a decorated type.")]
    else [];
  
  thread downSubst, upSubst on top, errCheck1, forward;
}

aspect production accessBouncer
top::Expr ::= e::Expr @q::QNameAttrOccur target::Access
{
  propagate upSubst, downSubst, finalSubst;
}

aspect production forwardAccess
top::Expr ::= e::Expr '.' 'forward'
{
  local attribute errCheck1 :: TypeCheck; errCheck1.finalSubst = top.finalSubst;
  errCheck1 = checkDecorated(e.typerep);

  thread downSubst, upSubst on top, e, errCheck1, top;
  
  top.errors <-
    if errCheck1.typeerror
    then [errFromOrigin(top, "Attribute forward being accessed from an undecorated type.")]
    else [];
}

aspect production decoratedAccessHandler
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  -- TODO: remove?
  local attribute errCheck1 :: TypeCheck; errCheck1.finalSubst = top.finalSubst;
  errCheck1 = checkDecorated(e.typerep);

  -- TECHNICALLY, I think the current implementation makes this impossible,
  -- But let's leave it since it's the right thing to do.
  top.errors <-
    if errCheck1.typeerror
    then [errFromOrigin(top, "Attribute " ++ q.name ++ " being accessed from an undecorated type.")]
    else [];

  thread downSubst, upSubst on top, errCheck1, forward;
}


aspect production noteAttachment
top::Expr ::= 'attachNote' note::Expr 'on' e::Expr 'end'
{
  local attribute errCheck1 :: TypeCheck; errCheck1.finalSubst = top.finalSubst;

  thread downSubst, upSubst on top, note, e, errCheck1, top;
  
  errCheck1 = check(note.typerep, nonterminalType("silver:core:OriginNote", [], true, false));
  top.errors <-
       if errCheck1.typeerror
       then [errFromOrigin(top, "First argument to attachNote must be OriginNote, was " ++ errCheck1.leftpp)]
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
       then [errFromOrigin(top, "Then and else branch must have the same type. Instead they are " ++ errCheck1.leftpp ++ " and " ++ errCheck1.rightpp)]
       else [];
  top.errors <-
       if errCheck2.typeerror
       then [errFromOrigin(e1, "Condition must have the type Boolean. Instead it is " ++ errCheck2.leftpp)]
       else [];
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
    then [errFromOrigin(es, "Second operand to 'terminal(type,lexeme,location)' must be a String, instead it is " ++ errCheck1.leftpp)]
    else [];

  top.errors <-
    if errCheck2.typeerror
    then [errFromOrigin(el, "Third operand to 'terminal(type,lexeme,location)' must be a Location, instead it is " ++ errCheck2.leftpp)]
    else [];
  
  top.errors <-
    if t.typerep.isTerminal || t.typerep.isError
    then []
    else [errFromOrigin(t, "First operand to 'terminal(type,lexeme,location)' must be a Terminal type, instead it is " ++ prettyType(t.typerep))];
}

aspect production decorateExprWith
top::Expr ::= 'decorate' e::Expr 'with' '{' inh::ExprInhs '}'
{
  local attribute errCheck1 :: TypeCheck; errCheck1.finalSubst = top.finalSubst;

  thread downSubst, upSubst on top, e, errCheck1, inh, top;

  errCheck1 = checkDecorable(top.env, e.typerep);
  top.errors <-
       if errCheck1.typeerror
       then [errFromOrigin(top, "Operand to decorate must be a decorable type.  Instead it is of type " ++ errCheck1.leftpp)]
       else [];
}

aspect production decorationSiteExpr
top::Expr ::= '@' e::Expr
{
  local attribute errCheck1 :: TypeCheck; errCheck1.finalSubst = top.finalSubst;

  thread downSubst, upSubst on top, e, errCheck1, top;

  errCheck1 = check(e.typerep, decoratedType(freshType(), inhSetType([])));
  top.errors <-
       if errCheck1.typeerror
       then [errFromOrigin(top, "Operand to @ must be a reference with no inherited attributes.  Instead it is of type " ++ errCheck1.leftpp)]
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
       then [errFromOrigin(top, lhs.name ++ " has expected type " ++ errCheck1.leftpp
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
    else [errFromOrigin(top, "Argument " ++ toString(top.appExprIndex+1) ++ " of function '" ++
            top.appExprApplied ++ "' expected " ++ errCheck1.rightpp ++
            " but argument is of type " ++ errCheck1.leftpp)];  
}

-- See documentation for major restriction on use of @.
-- Essentially, the referred expression MUST have already been type checked.
