grammar silver:compiler:modification:list;

import silver:compiler:definition:type:syntax;

terminal LSqr_t '[' ;
terminal RSqr_t ']' ;

-- The TYPE --------------------------------------------------------------------
concrete production listTypeExpr
top::TypeExpr ::= '[' te::TypeExpr ']'
{
  top.unparse = "[" ++ te.unparse ++ "]";
  propagate grammarName, env, flowEnv;

  top.typerep = listType(te.typerep);
  
  top.errorsKindStar :=
    if top.typerep.kindrep != starKind()
    then [errFromOrigin(top, s"${top.unparse} has kind ${prettyKind(top.typerep.kindrep)}, but kind * is expected here")]
    else [];

  forwards to
    appTypeExpr(
      listCtrTypeExpr('[', ']'),
      bTypeList('<', typeListSingle(@te), '>'));
}

concrete production listCtrTypeExpr
top::TypeExpr ::= '[' ']'
{
  top.unparse = "[]";

  top.typerep = listCtrType();
  
  top.errorsKindStar :=
    if top.typerep.kindrep != starKind()
    then [errFromOrigin(top, s"${top.unparse} has kind ${prettyKind(top.typerep.kindrep)}, but kind * is expected here")]
    else [];

  forwards to typerepTypeExpr(listCtrType());
}

-- The expressions -------------------------------------------------------------

concrete production emptyList
top::Expr ::= '[' ']'
{
  top.unparse = "[]";

  forwards to Silver_Expr { silver:core:nil() };
}

-- TODO: BUG: '::' is HasType_t.  We probably want to have a different
-- terminal here, with different precedence!

concrete production consListOp
top::Expr ::= h::Expr '::' t::Expr
{
  top.unparse = "(" ++ h.unparse ++ " :: " ++ t.unparse ++ ")" ;

  h.decSiteVertexInfo = nothing();
  h.alwaysDecorated = false;
  t.decSiteVertexInfo = nothing();
  t.alwaysDecorated = false;

  forwards to Silver_Expr { silver:core:cons($Expr{@h}, $Expr{@t}) };
}

concrete production fullList
top::Expr ::= '[' es::Exprs ']'
{ 
  top.unparse = "[ " ++ es.unparse ++ " ]";

  forwards to es.listtrans;
}

-- TODO: This should probably be a translation attribute (and define a specialized Exprs here)
synthesized attribute listtrans :: Expr occurs on Exprs;

aspect production exprsEmpty
top::Exprs ::=
{
  top.listtrans = emptyList('[',']');
}

aspect production exprsSingle
top::Exprs ::= e::Expr
{
  top.listtrans = consListOp(^e, '::', emptyList('[',']'));
}

aspect production exprsCons
top::Exprs ::= e1::Expr ',' e2::Exprs
{
  top.listtrans = consListOp(^e1, '::', e2.listtrans);
}
