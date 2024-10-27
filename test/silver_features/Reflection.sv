
import silver:reflect;
import silver:langutil;
import silver:langutil:pp;
import silver:langutil:reflect:serialize;

function lessHackyUnparse
String ::= x::a
{
  -- The toString of an object may vary due to changes in memory address, etc.
  -- So as a workaround replace all these in the pp with just OBJECT.
  local chunks::[String] = explode("<", show(80, reflect(x).pp));
  return
    implode(
      "<",
      head(chunks) ::
      map(
        \ s::String -> s"OBJECT :: ${head(tail(explode(" :: ", s)))}",
        tail(chunks)));
}

annotation lineNum::Integer;

nonterminal Expr with lineNum;

abstract production addExpr
top::Expr ::= e1::Expr e2::Expr
{}

abstract production intConstExpr
top::Expr ::= i::Integer
{}

abstract production idExpr
top::Expr ::= id::String
{}

abstract production decExpr
top::Expr ::= d::Decorated Expr
{}

global testExpr::Expr = addExpr(intConstExpr(2, lineNum=1), idExpr("asdf", lineNum=2), lineNum=3);

equalityTest(
  lessHackyUnparse([testExpr, intConstExpr(5, lineNum=4), decExpr(decorate testExpr with {}, lineNum=4)]),
  s"""[silver_features:addExpr(silver_features:intConstExpr(2, silver_features:lineNum=1), silver_features:idExpr("asdf", silver_features:lineNum=2), silver_features:lineNum=3), silver_features:intConstExpr(5, silver_features:lineNum=4), silver_features:decExpr(<OBJECT :: Decorated silver_features:Expr>, silver_features:lineNum=4)]""",
  String, silver_tests);

function reifyResToString
String ::= res::Either<String a>
{
  return case res of
    left(msg) -> msg
  | right(x) -> lessHackyUnparse(x)
  end;
}

global reifyRes1::Either<String Expr> = reify(nonterminalAST("silver_features:intConstExpr", consAST(integerAST(1), nilAST()), consNamedAST(namedAST("silver_features:lineNum", integerAST(2)), nilNamedAST())));

equalityTest(
  reifyResToString(reifyRes1),
  "silver_features:intConstExpr(1, silver_features:lineNum=2)",
  String, silver_tests);

equalityTest(fromRight(reifyRes1, idExpr("error", lineNum=-1)).lineNum, 2, Integer, silver_tests);

equalityTest(
  reifyResToString(reify(reflect([testExpr, intConstExpr(5, lineNum=4), decExpr(decorate testExpr with {}, lineNum=4)]))),
  lessHackyUnparse([testExpr, intConstExpr(5, lineNum=4), decExpr(decorate testExpr with {}, lineNum=4)]),
  String, silver_tests);

equalityTest(
  reifyResToString(reify(reflect(((1, 2), (3, 4))))),
  lessHackyUnparse(((1, 2), (3, 4))),
  String, silver_tests);

equalityTest(
  lessHackyUnparse(reifyUnchecked(reflect(((1, 2), (3, 4))))),
  lessHackyUnparse(((1, 2), (3, 4))),
  String, silver_tests);

nonterminal Foo;

abstract production existentialFoo
top::Foo ::= a
{}

equalityTest(
  reifyResToString(reify(reflect(existentialFoo(existentialFoo(42))))),
  lessHackyUnparse(existentialFoo(existentialFoo(42))),
  String, silver_tests);

global testVal::Pair<Pair<Integer (String ::= Float)> Pair<String Unit>> = ((1, \ f::Float -> toString(f)), ("a", unit()));

global reifyRes2::Either<String Pair<Pair<Integer (String ::= Float)> Pair<String Unit>>> = reify(anyAST(testVal));

equalityTest(reifyResToString(reifyRes2), lessHackyUnparse(testVal), String, silver_tests);

global reifyRes3::Either<String Pair<Pair<Integer (String ::= Float)> Pair<String Unit>>> = reify(reflect(testVal));

equalityTest(reifyResToString(reifyRes3), lessHackyUnparse(testVal), String, silver_tests);


nonterminal Bar<a>;

abstract production generalBar
top::Bar<(a ::= a)> ::= x::a
{}

global reifyRes4::Either<String Bar<(Integer ::= Integer)>> = reify(reflect(generalBar(1)));

equalityTest(
  reifyResToString(reifyRes4),
  lessHackyUnparse(generalBar(1)),
  String, silver_tests);

annotation anno1::Integer;
annotation anno2::Float;

nonterminal Baz with anno1, anno2;

abstract production baz
top::Baz ::=
{}

global reifyRes5::Either<String Baz> = reify(nonterminalAST("silver_features:baz", nilAST(), consNamedAST(namedAST("silver_features:anno1", integerAST(1)), consNamedAST(namedAST("silver_features:anno2", floatAST(2.0)), nilNamedAST()))));

equalityTest(fromRight(reifyRes5, baz(anno1=-1, anno2=-2.0)).anno1, 1, Integer, silver_tests);
equalityTest(fromRight(reifyRes5, baz(anno1=-1, anno2=-2.0)).anno2, 2.0, Float, silver_tests);

global foldAST::(ASTs ::= [AST]) = foldr(consAST, nilAST(), _);

global reifyRes6::Either<String [[[Integer]]]> = reify(listAST(foldAST([])));

equalityTest(reifyResToString(reifyRes6), "[]", String, silver_tests);

global reifyRes7::Either<String [[[Integer]]]> = reify(listAST(foldAST([listAST(nilAST()), listAST(foldAST([listAST(foldAST([]))])), listAST(foldAST([listAST(foldAST([integerAST(4)]))]))])));

equalityTest(reifyResToString(reifyRes7), "[[], [[]], [[4]]]", String, silver_tests);

equalityTest(
  reifyResToString(reify(listAST(foldAST([listAST(nilAST()), listAST(foldAST([listAST(foldAST([]))])), listAST(foldAST([listAST(foldAST([integerAST(4)]))]))])))),
  "[[], [[]], [[4]]]",
  String, silver_tests);

equalityTest(
  reifyResToString(reify(listAST(foldAST([listAST(nilAST()), listAST(foldAST([listAST(foldAST([floatAST(3.4)]))])), listAST(foldAST([listAST(foldAST([integerAST(4)]))]))])))),
  "Reification error at [_, _, [[?, ...], ...], ...]:\nreify is constructing Float, but found Integer AST.",
  String, silver_tests);

equalityTest(
  reifyResToString(reify(nonterminalAST("silver_features:addExpr", foldAST([nonterminalAST("silver_features:intConstExpr", foldAST([integerAST(42)]), consNamedAST(namedAST("foobar", floatAST(0.1)), nilNamedAST())), nonterminalAST("silver_features:idExpr", foldAST([stringAST("a")]), consNamedAST(namedAST("silver_features:lineNum", integerAST(1)), nilNamedAST()))]), consNamedAST(namedAST("silver_features:lineNum", integerAST(2)), nilNamedAST())))),
  "Reification error at silver_features:addExpr(?, _):\nProduction silver_features:intConstExpr expected silver_features:lineNum annotation(s), but got foobar.",
  String, silver_tests);

equalityTest(
  reifyResToString(reify(nonterminalAST("silver_features:addExpr", foldAST([nonterminalAST("silver_features:intConstExpr", foldAST([integerAST(42)]), consNamedAST(namedAST("silver_features:lineNum", floatAST(0.1)), nilNamedAST())), nonterminalAST("silver_features:idExpr", foldAST([stringAST("a")]), consNamedAST(namedAST("silver_features:lineNum", integerAST(1)), nilNamedAST()))]), consNamedAST(namedAST("silver_features:lineNum", integerAST(2)), nilNamedAST())))),
  "Reification error at silver_features:addExpr(silver_features:intConstExpr(silver_features:lineNum=?), _):\nreify is constructing Integer, but found Float AST.",
  String, silver_tests);

equalityTest(
  reifyResToString(reify(nonterminalAST("silver_features:addExpr", foldAST([nonterminalAST("silver_features:intConstExpr", foldAST([integerAST(42)]), consNamedAST(namedAST("silver_features:lineNum", integerAST(0)), nilNamedAST())), nonterminalAST("silver_features:idExpr", foldAST([stringAST("a"), stringAST("b")]), consNamedAST(namedAST("silver_features:lineNum", integerAST(1)), nilNamedAST()))]), consNamedAST(namedAST("silver_features:lineNum", integerAST(2)), nilNamedAST())))),
  "Reification error at silver_features:addExpr(_, ?):\nProduction silver_features:idExpr expected 1 child(ren), but got 2.",
  String, silver_tests);

global reifyRes8::Either<String (String ::= Integer Boolean)> = reify(anyAST((\ i::Integer f::Float b::Boolean -> toString(i) ++ toString(f) ++ toString(b))(_, 3.14, _)));

equalityTest(reifyResToString(reifyRes8), "<OBJECT :: (String ::= Integer Boolean)>", String, silver_tests);

equalityTest(reifyResToString(reify(anyAST(baz))), "<OBJECT :: (silver_features:Baz ::= ; anno1::Integer; anno2::Float)>", String, silver_tests);
equalityTest(reifyResToString(reify(anyAST(baz(anno2=_, anno1=_)))), "<OBJECT :: (silver_features:Baz ::= Float Integer)>", String, silver_tests);
equalityTest(reifyResToString(reify(anyAST(baz(anno1=1, anno2=_)))), "<OBJECT :: (silver_features:Baz ::= Float)>", String, silver_tests);
equalityTest(reifyResToString(reify(anyAST(baz(anno1=_, anno2=2.0)))), "<OBJECT :: (silver_features:Baz ::= Integer)>", String, silver_tests);

function reifySkolem
runtimeTypeable a => Either<String a> ::= x::AST
{
  return reify(^x);
}

wrongCode "runtimeTypeable" {
  function reifySkolemErr
  Either<String a> ::= x::AST
  {
    return reify(x);
  }
}

equalityTest(reifySkolem(reflect(("abc", 123))), right(("abc", 123)), Either<String Pair<String Integer>>, silver_tests);

function reifySkolem2
runtimeTypeable a => Either<String (a ::= Integer)> ::= 
{
  local fn::(a ::= Integer) = \ i::Integer -> error(toString(i));
  return reify(anyAST(fn));
}

wrongCode "runtimeTypeable" {
  function reifySkolemErr2
  Either<String (a ::= Integer)> ::= 
  {
    local fn::(a ::= Integer) = \ i::Integer -> error(toString(i));
    return reify(anyAST(fn));
  }
}

equalityTest(case reifySkolem2() of left(_) -> false | right(_) -> true end, true, Boolean, silver_tests);

function makeSpecializedId
(a ::= a) ::= a
{
  return \x::a -> x;
}

equalityTest(applyAST(anyAST(makeSpecializedId(42)), [just(reflect(12))], []).isLeft, true, Boolean, silver_tests);
equalityTest(applyAST(anyAST(makeSpecializedId(42)), [just(reflect(3.14))], []).isLeft, true, Boolean, silver_tests);

function makeSpecializedId2
runtimeTypeable a => (a ::= a) ::= a
{
  return \x::a -> x;
}

equalityTest(case applyAST(anyAST(makeSpecializedId2(42)), [just(reflect(12))], []) of left(m) -> m | right(a) -> reifyResToString(reify(a)) end, "12", String, silver_tests);
equalityTest(case applyAST(anyAST(makeSpecializedId2(42)), [just(reflect(3.14))], []) of left(m) -> m | right(a) -> reifyResToString(reify(a)) end, "Reification error in argument 0 at ?:\nreify is constructing Integer, but found Float AST.", String, silver_tests);

global testValue::Pair<[Expr] Baz> = ([testExpr, intConstExpr(5, lineNum=4)], baz(anno1=1, anno2=2.0));
global serializeRes::Either<String String> = reflect(testValue).serialize;
global deserializeRes::Either<String AST> = deserializeAST(lessHackyUnparse(testValue), case serializeRes of left(msg) -> msg | right(a) -> a end);

equalityTest(case serializeRes of left(msg) -> msg | right(a) -> a end, lessHackyUnparse(testValue), String, silver_tests);
equalityTest(case deserializeRes of left(msg) -> msg | right(a) -> show(80, a.pp) end, lessHackyUnparse(testValue), String, silver_tests);

equalityTest(
  case anyAST(\ i::Integer -> i).serialize of left(msg) -> msg | right(a) -> a end,
  "Can't serialize anyAST (type (Integer ::= Integer))",
  String, silver_tests);

global reifyRes9::Either<String Pair<[Expr] Baz>> = reify(fromRight(deserializeRes, reflect(([], baz(anno1=-3, anno2=-4.3242)))));

equalityTest(reifyResToString(reifyRes9), lessHackyUnparse(testValue), String, silver_tests);

equalityTest(
  case stringAST("\n\r\t	2as\bd1'\f\\\\\"\\").serialize of left(msg) -> msg | right(a) -> a end,
  "\"\\n\\r\\t\\t2as\\bd1'\\f\\\\\\\\\\\"\\\\\"",
  String, silver_tests);
equalityTest(
  case deserializeAST("test", "\"\\n\\r\\t\\t2as\\bd1'\\f\\\\\\\\\\\"\\\\\"") of left(msg) -> msg | right(stringAST(s)) -> s | _ -> "Unexpected case" end,
  "\n\r\t	2as\bd1'\f\\\\\"\\",
  String, silver_tests);

terminal Foo_t 'foo';
terminal Bar_t /bar[0-9]+/;

-- make this test independent of how `'foo'` translates
global terminal_foo_value :: Foo_t =
  terminal(Foo_t, "foo", loc("??", -1, -1, -1, -1, -1, -1));

global terminalTestValue::Pair<[Foo_t] Maybe<Bar_t>> = ([terminal_foo_value, terminal_foo_value], just(terminal(Bar_t, "bar42", loc("a", 1, 2, 3, 4, 5, 6))));
global terminalSerializeRes::Either<String String> = reflect(terminalTestValue).serialize;
global terminalDeserializeRes::Either<String AST> = deserializeAST(lessHackyUnparse(terminalTestValue), case terminalSerializeRes of left(msg) -> msg | right(a) -> a end);
global terminalReifyRes::Either<String Pair<[Foo_t] Maybe<Bar_t>>> = reify(case terminalDeserializeRes of left(msg) -> integerAST(37) | right(a) -> a end);

equalityTest(
  lessHackyUnparse(terminalTestValue),
  s"""silver:core:pair(silver:core:fst=[terminal(silver_features:Foo_t, "foo", ??:-1:-1), terminal(silver_features:Foo_t, "foo", ??:-1:-1)], silver:core:snd=silver:core:just(terminal(silver_features:Bar_t, "bar42", a:1:2)))""",
  String, silver_tests);
equalityTest(
  case terminalSerializeRes of left(msg) -> msg | right(a) -> a end,
  s"""silver:core:pair(silver:core:fst=[terminal(silver_features:Foo_t, "foo", silver:core:loc("??", -1, -1, -1, -1, -1, -1)), terminal(silver_features:Foo_t, "foo", silver:core:loc("??", -1, -1, -1, -1, -1, -1))], silver:core:snd=silver:core:just(terminal(silver_features:Bar_t, "bar42", silver:core:loc("a", 1, 2, 3, 4, 5, 6))))""",
  String, silver_tests);
equalityTest(case terminalDeserializeRes of left(msg) -> msg | right(a) -> show(80, a.pp) end, lessHackyUnparse(terminalTestValue), String, silver_tests);
equalityTest(reifyResToString(terminalReifyRes), lessHackyUnparse(terminalTestValue), String, silver_tests);

global reifyRes10::Either<String Baz> = reify(terminalAST("silver_features:Foo_t", "foo", txtLoc("test")));
equalityTest(reifyResToString(reifyRes10), "Reification error at ?:\nreify is constructing silver_features:Baz, but found terminal silver_features:Foo_t AST.", String, silver_tests);

global reifyRes11::Either<String Pair<String Location>> = reify(reflect(("asdf", 'foo')));
equalityTest(reifyResToString(reifyRes11), "Reification error at silver:core:pair(silver:core:snd=?):\nreify is constructing silver:core:Location, but found terminal silver_features:Foo_t AST.", String, silver_tests);

equalityTest(
  case deserializeAST("test", "terminal(asdf, \"a\", silver:core:loc(\"a\", 2, 3.14, 4, 5, 6, 7))") of left(msg) -> msg | right(a) -> show(80, a.pp) end,
  "test:1:20: error: Reification error at silver:core:loc(_, _, ?, _, _, _, _):\nreify is constructing Integer, but found Float AST.",
  String, silver_tests);

global serializeRes1::Either<String String> = serialize(("hello", [1, 2, 3, 4]));
global reifyRes12::Either<String Pair<String [Integer]>> = deserialize("test", fromRight(serializeRes1, ""));

equalityTest(
  case serializeRes1 of left(msg) -> msg | right(a) -> a end,
  s"""silver:core:pair(silver:core:fst="hello", silver:core:snd=[1, 2, 3, 4])""",
  String, silver_tests);
equalityTest(
  reifyResToString(reifyRes12),
  s"""silver:core:pair(silver:core:fst="hello", silver:core:snd=[1, 2, 3, 4])""",
  String, silver_tests);

type ForeignString foreign = "String";
wrongCode "Could not find an instance for runtimeTypeable silver_features:ForeignString (arising from the use of reifyUnchecked)" {
  function reifyForeignString
  ForeignString ::= x::AST
  { return reifyUnchecked(x); }
}

global add::(Integer ::= Integer Integer) = \ i::Integer j::Integer -> i + j;

global applyRes1::Either<String AST> = applyAST(reflect(add), [just(reflect(1)), just(reflect(2))], []);
equalityTest(lessHackyUnparse(applyRes1), "silver:core:right(silver:core:integerAST(3))", String, silver_tests);

global applyRes2::Either<String AST> = applyAST(applyAST(reflect(add), [nothing(), just(reflect(2))], []).fromRight, [just(reflect(1))], []);
equalityTest(lessHackyUnparse(applyRes2), "silver:core:right(silver:core:integerAST(3))", String, silver_tests);

global applyRes3::Either<String AST> = applyAST(reflect(add), [just(reflect(1)), nothing(), just(reflect(2))], []);
equalityTest(applyRes3.isLeft, true, Boolean, silver_tests);

global applyRes4::Either<String AST> = applyAST(reflect(baz), [], [("anno1", just(reflect(42))), ("anno2", just(reflect(3.14)))]);
equalityTest(
  case applyRes4 of left(m) -> m | right(a) -> reifyResToString(reify(a)) end,
  "silver_features:baz(silver_features:anno1=42, silver_features:anno2=3.14)",
  String, silver_tests);

global applyRes5::Either<String AST> = applyAST(reflect(baz), [], [("anno2", just(reflect(3.14))), ("anno1", just(reflect(42)))]);
equalityTest(
  case applyRes5 of left(m) -> m | right(a) -> reifyResToString(reify(a)) end,
  "silver_features:baz(silver_features:anno1=42, silver_features:anno2=3.14)",
  String, silver_tests);

global applyRes6::Either<String AST> = applyAST(reflect(baz), [], [("anno2", nothing()), ("anno1", just(reflect(42)))]);
equalityTest(
  case applyRes6 of left(m) -> m | right(a) -> reifyResToString(reify(a)) end,
  "<OBJECT :: (silver_features:Baz ::= Float)>",
  String, silver_tests);

global applyRes7::Either<String AST> = applyAST(applyAST(reflect(baz), [], [("anno2", nothing()), ("anno1", just(reflect(42)))]).fromRight, [just(reflect(3.14))], []);
equalityTest(
  case applyRes7 of left(m) -> m | right(a) -> reifyResToString(reify(a)) end,
  "silver_features:baz(silver_features:anno1=42, silver_features:anno2=3.14)",
  String, silver_tests);

global applyRes8::Either<String AST> = applyAST(reflect(baz), [], [("anno1", just(reflect(3.14))), ("anno2", just(reflect(42)))]);
equalityTest(applyRes8.isLeft, true, Boolean, silver_tests);

-- Reflection of productions with type constraints
equalityTest(decorate let res :: OCEqPair<EqExpr EqExpr> = reifyUnchecked(reflect(ocEqPair(ee1, ee2))) in res end with {compareTo = decorate ocEqPair(ee1, ee2) with {};}.isEqual, true, Boolean, silver_tests);

nonterminal WrapTypeable;
production wrapTypeable
runtimeTypeable a => top::WrapTypeable ::= x::a
{}

equalityTest(
  let res :: WrapTypeable = reifyUnchecked(reflect(wrapTypeable(("hi", 42)))) in case res of wrapTypeable(x) -> reifyUnchecked(reflect(x)) end end,
  ("hi", 42),
  Pair<String Integer>, silver_tests);

equalityTest(
  let res :: Either<String RTNT> = reify(reflect(rtProd(\ xs::[Integer] -> length(xs)))) in res.fromLeft end,
  "Reification error at ?:\nCan't construct production silver_features:rtProd because context runtimeTypeable a cannot be resolved at runtime",
  String, silver_tests);

equalityTest(
  let res :: Either<String EqPair<Integer [Integer]>> = reify(reflect(eqPair(42, [1, 2, 3]))) in res.fromLeft end,
  "Reification error at ?:\nCan't construct production silver_features:eqPair because context silver_features:myeq:MyEq a cannot be resolved at runtime",
  String, silver_tests);


inherited attribute rIdIn::Integer;
synthesized attribute rIdOut::Integer;
nonterminal RThing with rIdIn, rIdOut;
production rThing top::RThing ::=
{ top.rIdOut = top.rIdIn; }

equalityTest(getSynthesized(just(42), "silver:core:fromJust"), right(42), Either<String Integer>, silver_tests);
equalityTest(getSynthesized(decorate rThing() with {rIdIn = 42;}, "silver_features:rIdOut"), right(42), Either<String Integer>, silver_tests);
equalityTest(getInherited(decorate rThing() with {rIdIn = 42;}, "silver_features:rIdIn"), right(42), Either<String Integer>, silver_tests);
equalityTest(getSynthesized(decorate rThing() with {}, "silver_features:rIdOut").isLeft, true, Boolean, silver_tests);
equalityTest(getInherited(decorate rThing() with {}, "silver_features:rIdIn").isLeft, true, Boolean, silver_tests);
equalityTest(getInherited(decorate rThing() with {rIdIn = 42;}, "silver_features:rIdOut").isLeft, true, Boolean, silver_tests);
equalityTest(getSynthesized(decorate rThing() with {rIdIn = 42;}, "silver_features:rIdIn").isLeft, true, Boolean, silver_tests);
