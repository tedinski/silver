grammar silver:compiler:analysis:uniqueness;

imports silver:compiler:definition:core;
imports silver:compiler:definition:env;
imports silver:compiler:definition:type:syntax;
imports silver:compiler:translation:java:core only finalType;

-- TODO: Eventually this should be replaced by a monoid attribute collecting all unique reference sites
synthesized attribute isUnique::Boolean occurs on Expr, Exprs, AppExprs, AppExpr;

aspect production errorExpr
top::Expr ::= msg::[Message]
{
  top.isUnique = false;
}

aspect production errorReference
top::Expr ::= msg::[Message]  q::Decorated! QName
{
  top.isUnique = false;
}

aspect production childReference
top::Expr ::= q::Decorated! QName
{
  top.isUnique = finalType(top).isUnique;
}

aspect production localReference
top::Expr ::= q::Decorated! QName
{
  top.isUnique = finalType(top).isUnique;
}

aspect production lhsReference
top::Expr ::= q::Decorated! QName
{
  top.isUnique = false;
}

aspect production forwardReference
top::Expr ::= q::Decorated! QName
{
  top.isUnique = false;
}

aspect production productionReference
top::Expr ::= q::Decorated! QName
{
  top.isUnique = false;
}

aspect production functionReference
top::Expr ::= q::Decorated! QName
{
  top.isUnique = false;
}

aspect production classMemberReference
top::Expr ::= q::Decorated! QName
{
  top.isUnique = false;
}

aspect production globalValueReference
top::Expr ::= q::Decorated! QName
{
  top.isUnique = false;
}

aspect production errorApplication
top::Expr ::= e::Decorated! Expr es::Decorated! AppExprs annos::Decorated! AnnoAppExprs
{
  top.isUnique = false;
}

aspect production functionInvocation
top::Expr ::= e::Decorated! Expr es::Decorated! AppExprs annos::Decorated! AnnoAppExprs
{
  top.isUnique = e.isUnique || es.isUnique;
}

aspect production partialApplication
top::Expr ::= e::Decorated! Expr es::Decorated! AppExprs annos::Decorated! AnnoAppExprs
{
  top.isUnique = e.isUnique || es.isUnique;
}

aspect production errorAccessHandler
top::Expr ::= e::Decorated! Expr  q::Decorated! QNameAttrOccur
{
  top.isUnique = false;
}

aspect production errorDecoratedAccessHandler
top::Expr ::= e::Decorated! Expr  q::Decorated! QNameAttrOccur
{
  top.isUnique = false;
}

aspect production forwardAccess
top::Expr ::= e::Expr '.' 'forward'
{
  top.isUnique = false;
}

aspect production synDecoratedAccessHandler
top::Expr ::= e::Decorated! Expr  q::Decorated! QNameAttrOccur
{
  top.isUnique = false;
}

aspect production inhDecoratedAccessHandler
top::Expr ::= e::Decorated! Expr  q::Decorated! QNameAttrOccur
{
  top.isUnique = false;
}

aspect production terminalAccessHandler
top::Expr ::= e::Decorated! Expr  q::Decorated! QNameAttrOccur
{
  top.isUnique = false;
}

aspect production annoAccessHandler
top::Expr ::= e::Decorated! Expr  q::Decorated! QNameAttrOccur
{
  top.isUnique = false;
}

aspect production decorateExprWith
top::Expr ::= 'decorate' e::Expr 'with' '{' inh::ExprInhs '}'
{
  top.isUnique = false;
}

aspect production decorationSiteExpr
top::Expr ::= '@' e::Expr
{
  top.isUnique = true;
}

aspect production trueConst
top::Expr ::='true'
{
  top.isUnique = false;
}

aspect production falseConst
top::Expr ::= 'false'
{
  top.isUnique = false;
}

aspect production and
top::Expr ::= e1::Expr '&&' e2::Expr
{
  top.isUnique = false;
}

aspect production or
top::Expr ::= e1::Expr '||' e2::Expr
{
  top.isUnique = false;
}

aspect production notOp
top::Expr ::= '!' e::Expr
{
  top.isUnique = false;
}

aspect production ifThenElse
top::Expr ::= 'if' e1::Expr 'then' e2::Expr 'else' e3::Expr
{
  top.isUnique = e1.isUnique || e2.isUnique || e3.isUnique;
}

aspect production intConst
top::Expr ::= i::Int_t
{
  top.isUnique = false;
}

aspect production floatConst
top::Expr ::= f::Float_t
{
  top.isUnique = false;
}

aspect production noteAttachment
top::Expr ::= 'attachNote' note::Expr 'on' e::Expr 'end'
{
  top.isUnique = e.isUnique;
}

aspect production plus
top::Expr ::= e1::Expr '+' e2::Expr
{
  top.isUnique = false;
}
aspect production minus
top::Expr ::= e1::Expr '-' e2::Expr
{
  top.isUnique = false;
}
aspect production multiply
top::Expr ::= e1::Expr '*' e2::Expr
{
  top.isUnique = false;
}
aspect production divide
top::Expr ::= e1::Expr '/' e2::Expr
{
  top.isUnique = false;
}
aspect production modulus
top::Expr ::= e1::Expr '%' e2::Expr
{
  top.isUnique = false;
}
aspect production neg
top::Expr ::= '-' e::Expr
{
  top.isUnique = false;
}

aspect production terminalConstructor
top::Expr ::= 'terminal' '(' t::TypeExpr ',' es::Expr ',' el::Expr ')'
{
  top.isUnique = false;
}

aspect production stringConst
top::Expr ::= s::String_t
{
  top.isUnique = false;
}

aspect production exprsEmpty
top::Exprs ::=
{
  top.isUnique = false;
}

aspect production exprsSingle
top::Exprs ::= e::Expr
{
  top.isUnique = false;
}

aspect production exprsCons
top::Exprs ::= e1::Expr ',' e2::Exprs
{
  top.isUnique = false;
}

aspect production missingAppExpr
top::AppExpr ::= '_'
{
  top.isUnique = false;
}
aspect production presentAppExpr
top::AppExpr ::= e::Expr
{
  top.isUnique = e.isUnique;
}

aspect production snocAppExprs
top::AppExprs ::= es::AppExprs ',' e::AppExpr
{
  top.isUnique = es.isUnique || e.isUnique;
}
aspect production oneAppExprs
top::AppExprs ::= e::AppExpr
{
  top.isUnique = e.isUnique;
}
aspect production emptyAppExprs
top::AppExprs ::=
{
  top.isUnique = false;
}

aspect production exprRef
top::Expr ::= e::Decorated! Expr
{
  top.isUnique = e.isUnique;
}

