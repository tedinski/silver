grammar silver:rewrite;

imports silver:langutil;
imports silver:langutil:pp;
imports silver:reflect;

inherited attribute substitutionEnv::[Pair<String AST>];
synthesized attribute value::AST;

tracked nonterminal ASTExpr with pp, substitutionEnv, value;
propagate substitutionEnv on ASTExpr excluding letASTExpr, matchASTExpr;

-- AST constructors
abstract production prodCallASTExpr
top::ASTExpr ::= prodName::String children::ASTExprs annotations::NamedASTExprs
{
  top.pp = pp"${text(prodName)}(${ppImplode(pp", ", children.pps ++ annotations.pps)})";
  top.value =
    nonterminalAST(
      prodName,
      foldr(consAST, nilAST(), children.values),
      foldr(consNamedAST, nilNamedAST(), annotations.namedValues));
}

abstract production consListASTExpr
top::ASTExpr ::= h::ASTExpr t::ASTExpr
{
  top.pp = pp"(${h.pp} :: ${t.pp})";
  top.value =
    case t.value of
    | listAST(a) -> listAST(consAST(h.value, ^a))
    | _ -> error("Rewrite type error")
    end;
}

abstract production nilListASTExpr
top::ASTExpr ::=
{
  top.pp = pp"[]";
  top.value = listAST(nilAST());
}

abstract production listASTExpr
top::ASTExpr ::= vals::ASTExprs
{
  top.pp = pp"[${(ppImplode(pp", ", vals.pps))}]";
  forwards to foldr(consListASTExpr, nilListASTExpr(), vals.astExprs);
}

-- Constants
abstract production stringASTExpr
top::ASTExpr ::= s::String
{
  top.pp = pp"${text(escapeString(s))}";
  top.value = stringAST(s);
}

abstract production integerASTExpr
top::ASTExpr ::= i::Integer
{
  top.pp = pp"${text(toString(i))}";
  top.value = integerAST(i);
}

abstract production floatASTExpr
top::ASTExpr ::= f::Float
{
  top.pp = pp"${text(toString(f))}";
  top.value = floatAST(f);
}

abstract production booleanASTExpr
top::ASTExpr ::= b::Boolean
{
  top.pp = pp"${text(toString(b))}";
  top.value = booleanAST(b);
}

abstract production terminalASTExpr
top::ASTExpr ::= terminalName::String lexeme::ASTExpr location::ASTExpr
{
  top.pp = pp"terminal(${text(terminalName)}, ${lexeme.pp}, ${location.pp})";
  top.value =
    case reify(lexeme.value), reify(location.value) of
    | right(l), right(l1) -> terminalAST(terminalName, l, l1)
    | _, _ -> error("Invalid values to terminal constructor")
    end;
}

abstract production anyASTExpr
top::ASTExpr ::= x::a
{
  top.pp = reflect(x).pp;
  top.value = reflect(x);
}

-- Meta stuff
abstract production varASTExpr
top::ASTExpr ::= n::String
{
  top.pp = text(n);
  top.value =
    fromMaybe(
      error("Unbound variable " ++ n),
      lookup(n, top.substitutionEnv));
}

abstract production missingArgASTExpr
top::ASTExpr ::=
{
  top.pp = pp"_";
  top.value = error("missingArgASTExpr can only occur inside applyASTExpr arguments");
}

-- Other constructs
abstract production applyASTExpr
top::ASTExpr ::= f::ASTExpr args::ASTExprs namedArgs::NamedASTExprs
{
  top.pp = pp"${f.pp}(${ppImplode(pp", ", args.pps ++ namedArgs.pps)})";
  top.value =
    case applyAST(f.value, args.appValues, namedArgs.namedAppValues) of
    | left(msg) -> error(s"Error applying ${show(80, f.pp)}(${show(80, ppImplode(pp", ", args.pps ++ namedArgs.pps))}): ${msg}")
    | right(a) -> a
    end;
}

abstract production andASTExpr
top::ASTExpr ::= a::ASTExpr b::ASTExpr
{
  top.pp = pp"(${a.pp} && ${b.pp})";
  top.value =
    case a.value of
    | booleanAST(true) -> b.value
    | booleanAST(false) -> booleanAST(false)
    | _ -> error("Invalid values")
    end;
}

abstract production orASTExpr
top::ASTExpr ::= a::ASTExpr b::ASTExpr
{
  top.pp = pp"(${a.pp} || ${b.pp})";
  top.value =
    case a.value of
    | booleanAST(true) -> booleanAST(true)
    | booleanAST(false) -> b.value
    | _ -> error("Invalid values")
    end;
}

abstract production notASTExpr
top::ASTExpr ::= a::ASTExpr
{
  top.pp = pp"!${a.pp}";
  top.value =
    case a.value of
    | booleanAST(x) -> booleanAST(!x)
    | _ -> error("Invalid values")
    end;
}

abstract production gtASTExpr
top::ASTExpr ::= a::ASTExpr b::ASTExpr
{
  top.pp = pp"(${a.pp} > ${b.pp})";
  top.value =
    case a.value, b.value of
    | integerAST(x), integerAST(y) -> booleanAST(x > y)
    | floatAST(x), floatAST(y) -> booleanAST(x > y)
    | stringAST(x), stringAST(y) -> booleanAST(x > y)
    | x, y -> error("TODO: overloaded operator") -- Figure out how to handle this, applyAST doesn't work with type classes
    end;
}

abstract production ltASTExpr
top::ASTExpr ::= a::ASTExpr b::ASTExpr
{
  top.pp = pp"(${a.pp} < ${b.pp})";
  top.value =
    case a.value, b.value of
    | integerAST(x), integerAST(y) -> booleanAST(x < y)
    | floatAST(x), floatAST(y) -> booleanAST(x < y)
    | stringAST(x), stringAST(y) -> booleanAST(x < y)
    | x, y -> error("TODO: overloaded operator") -- Figure out how to handle this, applyAST doesn't work with type classes
    end;
}

abstract production gteqASTExpr
top::ASTExpr ::= a::ASTExpr b::ASTExpr
{
  top.pp = pp"(${a.pp} >= ${b.pp})";
  top.value =
    case a.value, b.value of
    | integerAST(x), integerAST(y) -> booleanAST(x >= y)
    | floatAST(x), floatAST(y) -> booleanAST(x >= y)
    | stringAST(x), stringAST(y) -> booleanAST(x >= y)
    | x, y -> error("TODO: overloaded operator") -- Figure out how to handle this, applyAST doesn't work with type classes
    end;
}

abstract production lteqASTExpr
top::ASTExpr ::= a::ASTExpr b::ASTExpr
{
  top.pp = pp"(${a.pp} <= ${b.pp})";
  top.value =
    case a.value, b.value of
    | integerAST(x), integerAST(y) -> booleanAST(x <= y)
    | floatAST(x), floatAST(y) -> booleanAST(x <= y)
    | stringAST(x), stringAST(y) -> booleanAST(x <= y)
    | x, y -> error("TODO: overloaded operator") -- Figure out how to handle this, applyAST doesn't work with type classes
    end;
}

abstract production eqeqASTExpr
top::ASTExpr ::= a::ASTExpr b::ASTExpr
{
  top.pp = pp"(${a.pp} == ${b.pp})";
  top.value =
    case a.value, b.value of
    | integerAST(x), integerAST(y) -> booleanAST(x == y)
    | floatAST(x), floatAST(y) -> booleanAST(x == y)
    | stringAST(x), stringAST(y) -> booleanAST(x == y)
    | booleanAST(x), booleanAST(y) -> booleanAST(x == y)
    | x, y -> error("TODO: overloaded operator") -- Figure out how to handle this, applyAST doesn't work with type classes
    end;
}

abstract production neqASTExpr
top::ASTExpr ::= a::ASTExpr b::ASTExpr
{
  top.pp = pp"(${a.pp} != ${b.pp})";
  top.value =
    case a.value, b.value of
    | integerAST(x), integerAST(y) -> booleanAST(x != y)
    | floatAST(x), floatAST(y) -> booleanAST(x != y)
    | stringAST(x), stringAST(y) -> booleanAST(x != y)
    | booleanAST(x), booleanAST(y) -> booleanAST(x != y)
    | x, y -> error("TODO: overloaded operator") -- Figure out how to handle this, applyAST doesn't work with type classes
    end;
}

abstract production ifThenElseASTExpr
top::ASTExpr ::= c::ASTExpr t::ASTExpr e::ASTExpr
{
  top.pp = pp"(if ${c.pp} then ${t.pp} else ${e.pp})";
  top.value =
    case c.value of
    | booleanAST(true) -> t.value
    | booleanAST(false) -> e.value
    | _ -> error("Invalid values")
    end;
}

abstract production noteAttachmentASTExpr
top::ASTExpr ::= a::ASTExpr b::ASTExpr
{
  top.pp = pp"attachNote ${a.pp} on {${b.pp}} end";
  top.value = case reify(a.value) of
              | right(note) -> attachNote note on b.value end
              | left(msg) -> error("Invalid value for noteAttachmentASTExpr's note: " ++ msg)
              end;
}

abstract production plusASTExpr
top::ASTExpr ::= a::ASTExpr b::ASTExpr
{
  top.pp = pp"(${a.pp} + ${b.pp})";
  top.value =
    case a.value, b.value of
    | integerAST(x), integerAST(y) -> integerAST(x + y)
    | floatAST(x), floatAST(y) -> floatAST(x + y)
    | _, _ -> error("Invalid values")
    end;
}

abstract production multiplyASTExpr
top::ASTExpr ::= a::ASTExpr b::ASTExpr
{
  top.pp = pp"(${a.pp} * ${b.pp})";
  top.value =
    case a.value, b.value of
    | integerAST(x), integerAST(y) -> integerAST(x * y)
    | floatAST(x), floatAST(y) -> floatAST(x * y)
    | _, _ -> error("Invalid values")
    end;
}

abstract production minusASTExpr
top::ASTExpr ::= a::ASTExpr b::ASTExpr
{
  top.pp = pp"(${a.pp} - ${b.pp})";
  top.value =
    case a.value, b.value of
    | integerAST(x), integerAST(y) -> integerAST(x - y)
    | floatAST(x), floatAST(y) -> floatAST(x - y)
    | _, _ -> error("Invalid values")
    end;
}

abstract production divideASTExpr
top::ASTExpr ::= a::ASTExpr b::ASTExpr
{
  top.pp = pp"(${a.pp} / ${b.pp})";
  top.value =
    case a.value, b.value of
    | integerAST(x), integerAST(y) -> integerAST(x / y)
    | floatAST(x), floatAST(y) -> floatAST(x / y)
    | _, _ -> error("Invalid values")
    end;
}

abstract production modulusASTExpr
top::ASTExpr ::= a::ASTExpr b::ASTExpr
{
  top.pp = pp"(${a.pp} % ${b.pp})";
  top.value =
    case a.value, b.value of
    | integerAST(x), integerAST(y) -> integerAST(x % y)
    | floatAST(x), floatAST(y) -> floatAST(0.0)
    | _, _ -> error("Invalid values")
    end;
}

abstract production negASTExpr
top::ASTExpr ::= a::ASTExpr
{
  top.pp = pp"-${a.pp}";
  top.value =
    case a.value of
    | integerAST(x) -> integerAST(-x)
    | floatAST(x) -> floatAST(-x)
    | _ -> error("Invalid values")
    end;
}

abstract production appendASTExpr
top::ASTExpr ::= a::ASTExpr b::ASTExpr
{
  top.pp = pp"(${a.pp} ++ ${b.pp})";
  top.value =
    case a.value, b.value of
    | stringAST(x), stringAST(y) -> stringAST(x ++ y)
    | listAST(x), listAST(y) -> listAST(appendASTs(^x, ^y))
    | _, _ -> error("Invalid values")
    end;
}

abstract production letASTExpr
top::ASTExpr ::= a::NamedASTExprs body::ASTExpr
{
  top.pp = pp"let ${ppImplode(pp", ", a.pps)} in ${body.pp} end";
  top.value = body.value;
  a.substitutionEnv = top.substitutionEnv;
  body.substitutionEnv =
    map(\ n::NamedAST -> case n of namedAST(n, a) -> (n, ^a) end, a.namedValues) ++ top.substitutionEnv;
}

abstract production lengthASTExpr
top::ASTExpr ::= a::ASTExpr
{
  top.pp = pp"length(${a.pp})";
  top.value =
    case a.value of
    | stringAST(s) -> integerAST(length(s))
    | listAST(a) -> integerAST(a.astsLength)
    | _ -> error("Invalid values")
    end;
}

abstract production toIntegerASTExpr
top::ASTExpr ::= a::ASTExpr
{
  top.pp = pp"toInteger(${a.pp})";
  top.value =
    case a.value of
    | integerAST(i) -> integerAST(toInteger(i))
    | booleanAST(b) -> integerAST(toInteger(b))
    | floatAST(f) -> integerAST(toInteger(f))
    | stringAST(s) -> integerAST(toInteger(s))
    | _ -> error("Invalid values")
    end;
}

abstract production toBooleanASTExpr
top::ASTExpr ::= a::ASTExpr
{
  top.pp = pp"toBoolean(${a.pp})";
  top.value =
    case a.value of
    | integerAST(i) -> booleanAST(toBoolean(i))
    | booleanAST(b) -> booleanAST(toBoolean(b))
    | floatAST(f) -> booleanAST(toBoolean(f))
    | stringAST(s) -> booleanAST(toBoolean(s))
    | _ -> error("Invalid values")
    end;
}

abstract production toFloatASTExpr
top::ASTExpr ::= a::ASTExpr
{
  top.pp = pp"toFloat(${a.pp})";
  top.value =
    case a.value of
    | integerAST(i) -> floatAST(toFloat(i))
    | booleanAST(b) -> floatAST(toFloat(b))
    | floatAST(f) -> floatAST(toFloat(f))
    | stringAST(s) -> floatAST(toFloat(s))
    | _ -> error("Invalid values")
    end;
}

abstract production toStringASTExpr
top::ASTExpr ::= a::ASTExpr
{
  top.pp = pp"toString(${a.pp})";
  top.value =
    case a.value of
    | integerAST(i) -> stringAST(toString(i))
    | booleanAST(b) -> stringAST(toString(b))
    | floatAST(f) -> stringAST(toString(f))
    | stringAST(s) -> stringAST(toString(s))
    | _ -> error("Invalid values")
    end;
}

-- *Undecorated* pattern match, with no regard to forwarding - not currently used
abstract production matchASTExpr
top::ASTExpr ::= e::ASTExpr pattern::ASTPattern res::ASTExpr fail::ASTExpr
{
  top.pp = pp"case ${e.pp} of ${pattern.pp} -> ${res.pp} | _ -> ${fail.pp} end";
  
  e.substitutionEnv = top.substitutionEnv;
  pattern.matchWith = e.value;
  res.substitutionEnv = pattern.substitution.fromJust ++ top.substitutionEnv;
  fail.substitutionEnv = top.substitutionEnv;
  top.value = if pattern.substitution.isJust then res.value else fail.value;
}

abstract production rewriteASTExpr
top::ASTExpr ::= s::ASTExpr e::ASTExpr
{
  top.pp = pp"rewriteWith(${s.pp}, ${e.pp})";
  
  production st::Strategy = reifyUnchecked(s.value);
  st.term = e.value;
  
  top.value =
    case st.result of
    | just(a) -> AST { silver:core:just(${a}) }
    | nothing() -> AST { silver:core:nothing() }
    end;
}

synthesized attribute astExprs::[ASTExpr];
synthesized attribute values::[AST];
synthesized attribute appValues::[Maybe<AST>];

tracked nonterminal ASTExprs with pps, astExprs, substitutionEnv, values, appValues;
propagate substitutionEnv on ASTExprs;

abstract production consASTExpr
top::ASTExprs ::= h::ASTExpr t::ASTExprs
{
  top.pps = h.pp :: t.pps;
  top.astExprs = ^h :: t.astExprs;
  top.values = h.value :: t.values;
  top.appValues =
    case h of
    | missingArgASTExpr() -> nothing()
    | _ -> just(h.value)
    end :: t.appValues;
}

abstract production nilASTExpr
top::ASTExprs ::=
{
  top.pps = [];
  top.astExprs = [];
  top.values = [];
  top.appValues = [];
}

fun appendASTExprs ASTExprs ::= a::ASTExprs b::ASTExprs =
  case a of
  | consASTExpr(h, t) -> consASTExpr(^h, appendASTExprs(^t, b))
  | nilASTExpr() -> b
  end;

synthesized attribute namedValues::[NamedAST];
synthesized attribute namedAppValues::[Pair<String Maybe<AST>>];

tracked nonterminal NamedASTExprs with pps, substitutionEnv, namedValues, namedAppValues;
propagate substitutionEnv on NamedASTExprs;

abstract production consNamedASTExpr
top::NamedASTExprs ::= h::NamedASTExpr t::NamedASTExprs
{
  top.pps = h.pp :: t.pps;
  top.namedValues = h.namedValue :: t.namedValues;
  top.namedAppValues = h.namedAppValue :: t.namedAppValues;
}

abstract production nilNamedASTExpr
top::NamedASTExprs ::=
{
  top.pps = [];
  top.namedValues = [];
  top.namedAppValues = [];
}

fun appendNamedASTExprs NamedASTExprs ::= a::NamedASTExprs b::NamedASTExprs =
  case a of
  | consNamedASTExpr(h, t) -> consNamedASTExpr(^h, appendNamedASTExprs(^t, b))
  | nilNamedASTExpr() -> b
  end;

synthesized attribute namedValue::NamedAST;
synthesized attribute namedAppValue::Pair<String Maybe<AST>>;

tracked nonterminal NamedASTExpr with pp, substitutionEnv, namedValue, namedAppValue;
propagate substitutionEnv on NamedASTExpr;

abstract production namedASTExpr
top::NamedASTExpr ::= n::String v::ASTExpr
{
  top.pp = pp"${text(n)}=${v.pp}";
  top.namedValue = namedAST(n, v.value);
  top.namedAppValue =
    (
      last(explode(":", n)),
      case v of
      | missingArgASTExpr() -> nothing()
      | _ -> just(v.value)
      end);
}
