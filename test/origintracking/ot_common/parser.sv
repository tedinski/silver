tracked nonterminal CST;
synthesized attribute transform::CST occurs on CST;

terminal Foo_t 'foo';
ignore terminal Space_t ' ';

concrete production foo
top::CST ::= 'foo'
{
	top.transform = bar();
}

abstract production bar
top::CST ::=
{
	top.transform = attachNote logicalLocationNote(txtLoc("bar")) on bar() end;
}

parser cstParse::CST {
	ot_common;
}