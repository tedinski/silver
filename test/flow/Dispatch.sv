grammar flow;

synthesized attribute errors1::Boolean;
synthesized attribute errors2::Boolean;

nonterminal UDExpr with env1, env2, errors1, errors2;
flowtype UDExpr = forward {env1, env2}, decorate {env1, env2}, errors1 {env1}, errors2 {env1, env2};

production directOverloadThing
top::UDExpr ::= e::UDExpr
{
  e.env1 = top.env1;
  top.errors2 = e.errors2;
  forwards to shareThing(e);
}

production indirectOverloadThing
top::UDExpr ::= e::UDExpr
{
  e.env1 = top.env1;
  top.errors2 = e.errors2;
  local prod::DispatchOp = if e.errors1 then dispatchThing1 else dispatchThing2;
  forwards to prod(e);
}

production shareThing
top::UDExpr ::= @e::UDExpr
{
  e.env2 = top.env2;
  top.errors1 = e.errors1;
  top.errors2 = !null(e.env1);
}

dispatch DispatchOp = UDExpr ::= @e1::UDExpr;

production dispatchThing1 implements DispatchOp
top::UDExpr ::= @e::UDExpr
{
  e.env2 = top.env2;
  top.errors1 = e.errors1;
  top.errors2 = !null(e.env1);
}

production dispatchThing2 implements DispatchOp
top::UDExpr ::= @e::UDExpr
{
  e.env2 = top.env1;
  top.errors1 = e.errors1;
  top.errors2 = !null(e.env1);
}

production dispatchThing3 implements DispatchOp
top::UDExpr ::= @e::UDExpr i::Integer b::Boolean
{
  e.env2 = if b then [] else top.env2;
  top.errors1 = b;
  top.errors2 = i > 0;
}

global dt3::DispatchOp = dispatchThing3(3, false);

production dispatchThing4 implements DispatchOp
top::UDExpr ::= @e::UDExpr
{
  forwards to dispatchThing3(e, 42, true);
}

wrongFlowCode "Tree e in production flow:overloadThing2 is shared in multiple places" {
production overloadThing2
top::UDExpr ::= e::UDExpr
{
  local otherRef::UDExpr = @e;
  e.env1 = top.env1;
  forwards to shareThing(e);
}
}

wrongFlowCode "Tree e in production flow:shareThing2 is shared in multiple places" {
production shareThing2
top::UDExpr ::= @e::UDExpr
{
  local otherRef::UDExpr = @e;
  local otherRef2::UDExpr = @e;
}
}

warnCode "Non-dispatch production shareThing has shared children in its signature, and can only be referenced by applying it in the root position of a forward or forward production attribute equation" {
function dispatchFunction
UDExpr ::= e::UDExpr
{
  e.env1 = [];
  return shareThing(e);
}
}

warnCode "Dispatching may require inherited attribute(s) flow:env2 on e, but these attribute(s) are supplied here after dispatching" {
production dispatchCycle
top::UDExpr ::= e::UDExpr
{
  e.env1 = top.env1;
  local prod::DispatchOp = if null(e.env2) then dispatchThing1 else dispatchThing2;
  forwards to prod(e);
}
}

dispatch DispatchOp2 = UDExpr ::= e::UDExpr;
production doimpl1 implements DispatchOp2
top::UDExpr ::= e::UDExpr
{
  e.env1 = top.env1;
  e.env2 = top.env2;
  top.errors1 = e.errors1;
  top.errors2 = !null(e.env1);
}
production doimpl2 implements DispatchOp2
top::UDExpr ::= e::UDExpr
{
  e.env1 = top.env1;
  e.env2 = top.env1;
  top.errors1 = e.errors1;
  top.errors2 = !null(e.env1);
}

warnCode "Dispatching may require inherited attribute(s) flow:env2 on e, but these attribute(s) are supplied here after dispatching" {
production dispatchCycle2
top::UDExpr ::= e::UDExpr
{
  local prod::DispatchOp2 = if null(e.env2) then doimpl1 else doimpl2;
  forwards to prod(@e);
}
}
