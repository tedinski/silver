tracked nonterminal Nat;
synthesized attribute val :: Integer occurs on Nat;
synthesized attribute plusOne :: Nat occurs on Nat;
synthesized attribute minusOne :: Nat occurs on Nat;

abstract production z
top::Nat ::=
{
  top.val = 0;
  top.plusOne = s(^top);
  top.minusOne = error("minusOne of z()");
}

abstract production s
top::Nat ::= a::Nat
{
  top.val = a.val + 1;
  top.plusOne = s(a.plusOne);
  top.minusOne = ^a;
}