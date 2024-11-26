grammar silver:compiler:definition:flow:env;

import silver:compiler:definition:type:syntax;

attribute flowDefs, flowEnv occurs on
  ClassBody, ClassBodyItem, InstanceBody, InstanceBodyItem;
propagate flowDefs, flowEnv on
  ClassBody, ClassBodyItem, InstanceBody, InstanceBodyItem;

aspect production defaultConstraintClassBodyItem
top::ClassBodyItem ::= id::Name '::' cl::ConstraintList '=>' ty::TypeExpr '=' e::Expr ';'
{
  e.decSiteVertexInfo = nothing();
  e.alwaysDecorated = false;
  e.appDecSiteVertexInfo = nothing();
  e.dispatchFlowDeps = [];
}
aspect production instanceBodyItem
top::InstanceBodyItem ::= id::QName '=' e::Expr ';'
{
  e.decSiteVertexInfo = nothing();
  e.alwaysDecorated = false;
  e.appDecSiteVertexInfo = nothing();
  e.dispatchFlowDeps = [];
}
