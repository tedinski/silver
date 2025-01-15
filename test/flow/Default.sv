grammar flow;

nonterminal DefaultDepNT with env1, errors1;

aspect default production
top::DefaultDepNT ::=
{
  top.errors1 = null(top.env1);
}

production defaultDep
top::DefaultDepNT ::=
{
  top.errors1 = false;
}

