grammar flow;

inherited attribute env1::[String];
inherited attribute env2::[String];
nonterminal Expr with env1, env2;
flowtype Expr = decorate {env1};

production zero
top::Expr ::=
{}

function getRef
Decorated Expr ::= x::Expr
{
  x.env1 = [];
  return x;
}

warnCode "Equation has transitive dependency on child x's inherited attribute for flow:env1 but this equation appears to be missing." {
  function getRefEnv1Missing
  Decorated Expr with {env1} ::= x::Expr
  { return x; }
}

function getRefEnv1
Decorated Expr with {env1} ::= x::Expr
{
  x.env1 = [];
  return x;
}

warnCode "Equation has transitive dependency for any inherited attribute on child x, caused by taking an unbounded reference." {
  function getRefUnbounded
  Decorated Expr with i ::= x::Expr
  {
    x.env1 = [];
    return x;
  }
}

function getRefBoundedEnv1
i subset {env1} => Decorated Expr with i ::= x::Expr
{
  x.env1 = [];
  return x;
}

-- This would be flow error, but is caught by type checking first
wrongCode "Expected return type is Decorated flow:Expr with i, but the expression has actual type Decorated flow:Expr with {flow:env1}" {
  function getDecRefUnbounded
  Decorated Expr with i ::= x::Expr
  {
    return decorate x with {env1=[];};
  }
}

-- This would be OK, but is caught by type checking anyway
wrongCode "Expected return type is Decorated flow:Expr with i, but the expression has actual type Decorated flow:Expr with {flow:env1}" {
  function getDecRefUnbounded
  i subset {env1} => Decorated Expr with i ::= x::Expr
  {
    return decorate x with {env1=[];};
  }
}

synthesized attribute getRefWith<a (i :: InhSet)>::Decorated a with i;
nonterminal RExpr<(i :: InhSet)> with env1, env2, getRefWith<RExpr<i> i>;
warnCode "Equation has transitive dependency for any inherited attribute, caused by taking an unbounded reference to the production LHS." {
  production mkRExprUnbounded
  top::RExpr<i> ::=
  {
    top.getRefWith = top;
  }
}

production mkRExprBounded
i subset {env1} => top::RExpr<i> ::=
{
  top.getRefWith = top;
}

function getRExprRefWithEnv1
Decorated RExpr<{env1}> with {env1} ::=
{
  local a::RExpr<{env1}> = mkRExprBounded();
  a.env1 = [];
  return a.getRefWith;
}