grammar silver:definition:core;

import silver:definition:env;

nonterminal Expected;

abstract production expected_type
top::Expected ::= t::Decorated TypeRep {}

abstract production expected_decorated
top::Expected ::= {}

abstract production expected_undecorated
top::Expected ::= {}

abstract production expected_default
top::Expected ::= {}