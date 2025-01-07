grammar silver:compiler:extension:silverconstruction;

imports silver:langutil:pp;

imports silver:compiler:definition:core;
imports silver:compiler:definition:env;
imports silver:compiler:definition:type:syntax;
imports silver:compiler:modification:list;
imports silver:compiler:extension:patternmatching;

concrete production quoteAGDcl
top::Expr ::= 'Silver_AGDcl' '{' ast::AGDcl '}'
{
  top.unparse = s"Silver_AGDcl " ++ substitute("\n"," ", "{${ast.unparse}}");
  forwards to translate(reflect(^ast));
}

concrete production quoteProductionStmt
top::Expr ::= 'Silver_ProductionStmt' '{' ast::ProductionStmt '}'
{
  top.unparse = s"Silver_ProductionStmt" ++ substitute("\n"," ", "{${ast.unparse}}");
  forwards to translate(reflect(^ast));
}

concrete production quoteExpr
top::Expr ::= 'Silver_Expr' '{' ast::Expr '}'
{
  top.unparse = s"Silver_Expr {${ast.unparse}}";
  forwards to translate(reflect(^ast));
}

concrete production quoteExprInh
top::Expr ::= 'Silver_ExprInh' '{' ast::ExprInh '}'
{
  top.unparse = s"Silver_ExprInh {${ast.unparse}}";
  forwards to translate(reflect(^ast));
}

concrete production quotePattern
top::Expr ::= 'Silver_Pattern' '{' ast::Pattern '}'
{
  top.unparse = s"Silver_Pattern {${ast.unparse}}";
  forwards to translate(reflect(^ast));
}

concrete production quoteTypeExpr
top::Expr ::= 'Silver_TypeExpr' '{' ast::TypeExpr '}'
{
  top.unparse = s"Silver_TypeExpr {${ast.unparse}}";
  forwards to translate(reflect(^ast));
}

concrete production antiquoteExpr
top::Expr ::= '$Expr' '{' e::Expr '}'
{
  top.unparse = s"$$Expr{${e.unparse}}";
  forwards to
    errorExpr(
      [errFromOrigin(top, "$Expr should not occur outside of quoted Silver literal")]);
}

concrete production antiquoteExprInhs
top::ExprInhs ::= '$ExprInhs' '{' e::Expr '}'
{
  top.unparse = s"$$ExprInhs{${e.unparse}}";
  -- TODO: [errFromOrigin(top, "$ExprInhs should not occur outside of quoted Silver literal")]
  forwards to exprInhsEmpty();
}

concrete production antiquoteTypeExpr
top::TypeExpr ::= '$TypeExpr' '{' e::Expr '}'
{
  top.unparse = s"$$TypeExpr{${e.unparse}}";
  forwards to
    errorTypeExpr(
      [errFromOrigin(top, "$TypeExpr should not occur outside of quoted Silver literal")]);
}

concrete production antiquoteConstraintList
top::ConstraintList ::= '$ConstraintList' '{' e::Expr '}'
{
  top.unparse = s"$$ConstraintList{${e.unparse}}";
  -- [errFromOrigin(top, "$ConstraintList should not occur outside of quoted Silver Literal.")]
  forwards to nilConstraint();
}

concrete production antiquotePattern
top::Pattern ::= '$Pattern' '{' e::Expr '}'
{
  top.unparse = s"$$Pattern{${e.unparse}}";
  forwards to
    errorPattern(
      [errFromOrigin(top, "$Pattern should not occur outside of quoted Silver literal")]);
}

concrete production antiquoteFunctionSignature
top::FunctionSignature ::= '$FunctionSignature' '{' e::Expr '}'
{
  top.unparse = s"$$FunctionSignature{${e.unparse}}";
  forwards to
    functionSignatureNoCL(
      functionLHS(
        errorTypeExpr([errFromOrigin(top, "$FunctionSignature should not occur outside of quoted Silver literal")])),
      '::=', productionRHSNil());
}

concrete production antiquoteProductionRHS
top::ProductionRHS ::= '$ProductionRHS' '{' e::Expr '}'
{
  top.unparse = s"$$ProductionRHS{${e.unparse}}";
  forwards to productionRHSNil();
}

concrete production antiquoteAspectRHS
top::AspectRHS ::= '$AspectRHS' '{' e::Expr '}'
{
  top.unparse = s"$$AspectRHS{${e.unparse}}";
  forwards to aspectRHSElemNil();
}

concrete production antiquoteProductionStmt
top::ProductionStmt ::= '$ProductionStmt' '{' e::Expr '}'
{
  top.unparse = s"$$ProductionStmt{${e.unparse}}";
  forwards to
    errorProductionStmt(
      [errFromOrigin(top, "$ProductionStmt should not occur outside of quoted Silver Literal.")]);
}


concrete production antiquoteQName
top::QName ::= '$QName' '{' e::Expr '}'
{
  top.unparse = s"$$QName{${e.unparse}}";
  forwards to
    qNameError(
      [errFromOrigin(top, "$QName should not occur outside of quoted Silver literal")]);
}

concrete production antiquoteQNameAttrOccur
top::QNameAttrOccur ::= '$QNameAttrOccur' '{' e::Expr '}'
{
  top.unparse = s"$$QNameAttrOccur{${e.unparse}}";
  forwards to
    qNameAttrOccur(
      qNameError(
        [errFromOrigin(top, "$QNameAttrOccur should not occur outside of quoted Silver literal")]));
}

concrete production antiquoteName
top::Name ::= '$Name' '{' e::Expr '}'
{
  top.unparse = s"$$Name{${e.unparse}}";
  -- TODO: [errFromOrigin(top, "$Name should not occur outside of quoted Silver literal")]
  forwards to name("err");
}

concrete production antiquote_qName
top::QName ::= '$qName' '{' e::Expr '}'
{
  top.unparse = s"$$qName{${e.unparse}}";
  forwards to
    qNameError(
      [errFromOrigin(top, "$qName should not occur outside of Silver_Expr")]);
}

concrete production antiquote_name
top::Name ::= '$name' '{' e::Expr '}'
{
  top.unparse = s"$$name{${e.unparse}}";
  -- TODO: [errFromOrigin(top, "$Name should not occur outside of quoted Silver literal")]
  forwards to name("err");
}
