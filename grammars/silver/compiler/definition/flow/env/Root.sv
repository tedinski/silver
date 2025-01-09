grammar silver:compiler:definition:flow:env;

import silver:compiler:definition:type:syntax;
import silver:compiler:definition:concrete_syntax;
import silver:compiler:modification:defaultattr;
import silver:compiler:modification:collection;
import silver:compiler:modification:copper;
import silver:compiler:modification:concisefunctions;

attribute flowDefs, refDefs, specDefs, flowEnv occurs on File, AGDcls, AGDcl, Grammar;
flowtype flowDefs {decorate} on File, AGDcls, AGDcl, Grammar;
flowtype refDefs {decorate} on File, AGDcls, AGDcl, Grammar;
flowtype specDefs {decorate} on File, AGDcls, AGDcl, Grammar;
propagate flowDefs, refDefs, specDefs, flowEnv on File, AGDcls, AGDcl, Grammar;

aspect default production
top::AGDcl ::=
{
  top.flowDefs := [];
  top.refDefs := [];
  top.specDefs := [];
}

aspect production globalValueDclConcrete
top::AGDcl ::= 'global' id::Name '::' cl::ConstraintList '=>' t::TypeExpr '=' e::Expr ';'
{
  e.decSiteVertexInfo = nothing();
  e.alwaysDecorated = false;
  e.appDecSiteVertexInfo = nothing();
  e.dispatchFlowDeps = [];
}
