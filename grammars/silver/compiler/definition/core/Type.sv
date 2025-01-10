grammar silver:compiler:definition:core;

-- LHS type gives this to 'application' for "foo(...)" calls.
synthesized attribute applicationDispatcher :: Application;
-- LHS type gives this to 'access' for "foo.some" accesses.
-- (See DclInfo for the next step)
synthesized attribute accessHandler :: Access;

attribute applicationDispatcher, accessHandler occurs on Type;

aspect default production
top::Type ::=
{
  top.applicationDispatcher = errorApplication;
  top.accessHandler = errorAccessHandler;
}

aspect production appType
top::Type ::= c::Type a::Type
{
  top.applicationDispatcher = c.applicationDispatcher;
  top.accessHandler = c.accessHandler;
}

aspect production skolemType
top::Type ::= _
{
  top.accessHandler = undecoratedAccessHandler;
}

aspect production nonterminalType
top::Type ::= fn::String _ data::Boolean _
{
  top.applicationDispatcher = annoUpdateApplication;
  top.accessHandler = if data then dataAccessHandler else undecoratedAccessHandler;
}

aspect production terminalType
top::Type ::= fn::String
{
  top.accessHandler = terminalAccessHandler;
}

aspect production decoratedType
top::Type ::= te::Type _
{
  top.accessHandler = decoratedAccessHandler;
}

aspect production functionType
top::Type ::= _ _
{
  top.applicationDispatcher = functionApplication;
}

aspect production dispatchType
top::Type ::= _
{
  top.applicationDispatcher = dispatchApplication;
}

