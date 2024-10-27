grammar silver:langutil:reflect;

imports silver:reflect;
imports silver:langutil;
imports silver:langutil:pp;

attribute pp occurs on AST;

aspect production nonterminalAST
top::AST ::= prodName::String children::ASTs annotations::NamedASTs
{
  top.pp = cat(text(prodName), parens(ppImplode(pp", ", children.pps ++ annotations.pps)));
}

aspect production terminalAST
top::AST ::= terminalName::String lexeme::String location::Location
{
  top.pp = pp"terminal(${text(terminalName)}, \"${text(escapeString(lexeme))}\", ${text(location.unparse)})";
}

aspect production listAST
top::AST ::= vals::ASTs
{
  top.pp = brackets(ppImplode(pp", ", vals.pps));
}

aspect production stringAST
top::AST ::= s::String
{
  top.pp = pp"\"${text(escapeString(s))}\"";
}

aspect production integerAST
top::AST ::= i::Integer
{
  top.pp = text(toString(i));
}

aspect production floatAST
top::AST ::= f::Float
{
  top.pp = text(toString(f));
}

aspect production booleanAST
top::AST ::= b::Boolean
{
  top.pp = text(toString(b));
}

aspect production anyAST
top::AST ::= x::a
{
  top.pp =
    case reflectTypeName(x) of
      just(n) -> pp"<${text(nativeToString(x))} :: ${text(n)}>"
    | nothing() -> pp"<${text(nativeToString(x))}>"
    end;
}

attribute pps occurs on ASTs;

aspect production consAST
top::ASTs ::= h::AST t::ASTs
{
  top.pps = h.pp :: t.pps;
}

aspect production nilAST
top::ASTs ::=
{
  top.pps = [];
}

attribute pps occurs on NamedASTs;

aspect production consNamedAST
top::NamedASTs ::= h::NamedAST t::NamedASTs
{
  top.pps = h.pp :: t.pps;
}

aspect production nilNamedAST
top::NamedASTs ::=
{
  top.pps = [];
}

attribute pp occurs on NamedAST;

aspect production namedAST
top::NamedAST ::= n::String v::AST
{
  top.pp = pp"${text(n)}=${v.pp}";
}