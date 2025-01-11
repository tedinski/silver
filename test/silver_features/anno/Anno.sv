
import silver_features;
import silver:testing;

nonterminal AnnoNT with what; -- our target of abuse!

annotation what :: Integer;

abstract production anAnnoNT
top::AnnoNT ::=
{
}

global nt1 :: AnnoNT = anAnnoNT(what=1);
global dnt1 :: Decorated AnnoNT = decorate nt1 with {};

-- this applies, and accesses, an annotation's value
equalityTest ( nt1.what, 1, Integer, silver_tests ) ;
-- Check it works from decorated values
equalityTest ( dnt1.what, 1, Integer, silver_tests ) ;


global intFun :: (AnnoNT ::= Integer) = anAnnoNT(what=_);
global nt2 :: AnnoNT = intFun(2);

equalityTest ( nt2.what, 2, Integer, silver_tests ) ;


function ordinaryFun
AnnoNT ::=
{
  return anAnnoNT(what=3);
}

wrongCode "has initialization expression with type" {
  -- anAnnoNT :: (AnnoNT::= ; what::Integer)
  global aasdf :: (AnnoNT::=) = anAnnoNT;
}

wrongCode "Missing named parameters" {
  global aasdf :: AnnoNT = anAnnoNT();
}

wrongCode "'what' is not appropriate" {
  global aasdf :: AnnoNT = ordinaryFun(what=2);
}

wrongCode "'asfd' is not appropriate" {
  global aasdf :: AnnoNT = anAnnoNT(asfd=2);
}

wrongCode "expected Integer" {
  global aasdf :: AnnoNT = anAnnoNT(what="wrong type");
}

abstract production moreAnnoNT
top::AnnoNT ::= s::String
{
}

global fun2 :: (AnnoNT ::= String Integer) = moreAnnoNT(_, what=_);
global fun3 :: (AnnoNT ::= Integer) = moreAnnoNT("hi", what=_);
global fun4 :: (AnnoNT ::= String) = moreAnnoNT(_, what=7);

global nt3 :: AnnoNT = fun2("hi", 5);
global nt4 :: AnnoNT = fun3(6);
global nt5 :: AnnoNT = fun4("str");

equalityTest ( nt3.what, 5, Integer, silver_tests ) ;
equalityTest ( nt4.what, 6, Integer, silver_tests ) ;
equalityTest ( nt5.what, 7, Integer, silver_tests ) ;

wrongCode "Missing named parameters" {
  global aasdf :: AnnoNT = moreAnnoNT("tmp");
}
wrongCode "Too few arguments provided " {
  global aasdf :: AnnoNT = moreAnnoNT(what=2);
}

-- Let's ensure we can still pattern match alright
global grabstr :: String = case nt5 of moreAnnoNT(s) -> s | _ -> error("match failed") end;
equalityTest ( grabstr, "str", String, silver_tests ) ;

-- Occurs-on contexts
function getWhat
annotation what occurs on a =>
Integer ::= x::a
{
  return x.what;
}

equalityTest ( getWhat(nt1), 1, Integer, silver_tests ) ;
equalityTest ( getWhat(nt2), 2, Integer, silver_tests ) ;

class What a {
  getWhat2 :: (Integer ::= a);
}

instance annotation what occurs on a => What a {
  getWhat2 = (.what);
}

equalityTest ( getWhat2(nt1), 1, Integer, silver_tests ) ;
equalityTest ( getWhat2(nt2), 2, Integer, silver_tests ) ;

class annotation what occurs on a => What2 a {}
instance What2 AnnoNT {}

function getWhat3
What2 a => Integer ::= x::a
{ return x.what; }

equalityTest ( getWhat3(nt1), 1, Integer, silver_tests ) ;
equalityTest ( getWhat3(nt2), 2, Integer, silver_tests ) ;


nonterminal AnnoNT2 with anno1, anno2;

annotation anno1 :: Integer;
annotation anno2 :: String;

derive Eq on AnnoNT2;

abstract production annoNT2
top::AnnoNT2 ::=
{
}

global annoNT2a :: AnnoNT2 = annoNT2(anno1=1, anno2="2");
global annoNT2b :: AnnoNT2 = annoNT2(anno2="3", anno1=4);


equalityTest ( annoNT2a.anno1, 1, Integer, silver_tests ) ;
equalityTest ( annoNT2a.anno2, "2", String, silver_tests ) ;
equalityTest ( annoNT2b.anno1, 4, Integer, silver_tests ) ;
equalityTest ( annoNT2b.anno2, "3", String, silver_tests ) ;


abstract production annoNT2partialAppProd
top::AnnoNT2 ::= s::String
{
}

global partialApp1 :: (AnnoNT2 ::= String) = annoNT2partialAppProd(_, anno1=5, anno2="6");
global partialApp2 :: (AnnoNT2 ::= String) = annoNT2partialAppProd(_, anno2="7", anno1=8);

global partialApp1val :: AnnoNT2 = partialApp1("foo");
global partialApp2val :: AnnoNT2 = partialApp2("bar");

equalityTest ( partialApp1val.anno1, 5, Integer, silver_tests ) ;
equalityTest ( partialApp1val.anno2, "6", String, silver_tests ) ;
equalityTest ( partialApp2val.anno2, "7", String, silver_tests ) ;
equalityTest ( partialApp2val.anno1, 8, Integer, silver_tests ) ;


equalityTest(
  case partialApp1val of
  | annoNT2partialAppProd(a, anno1=b, anno2="6") when a == "foo" -> b
  | _ -> 42
  end,
  5, Integer, silver_tests);

equalityTest(
  annoNT2a(anno1=2),
  annoNT2(anno1=2, anno2="2"),
  AnnoNT2, silver_tests);
equalityTest(
  annoNT2a(anno2="def"),
  annoNT2(anno1=1, anno2="def"),
  AnnoNT2, silver_tests);
equalityTest(
  annoNT2a(anno1=3, anno2="def"),
  annoNT2(anno1=3, anno2="def"),
  AnnoNT2, silver_tests);
equalityTest(
  annoNT2a(anno2="def", anno1=3),
  annoNT2(anno1=3, anno2="def"),
  AnnoNT2, silver_tests);
equalityTest(
  annoNT2a(anno1=_)(2),
  annoNT2(anno1=2, anno2="2"),
  AnnoNT2, silver_tests);
equalityTest(
  annoNT2a(anno2=_)("def"),
  annoNT2(anno1=1, anno2="def"),
  AnnoNT2, silver_tests);
equalityTest(
  annoNT2a(anno1=4, anno2=_)("xyz"),
  annoNT2(anno1=4, anno2="xyz"),
  AnnoNT2, silver_tests);
equalityTest(
  annoNT2a(anno2=_, anno1=4)("xyz"),
  annoNT2(anno1=4, anno2="xyz"),
  AnnoNT2, silver_tests);
equalityTest(
  annoNT2a(anno2=_, anno1=_)("xyz", 42),
  annoNT2(anno1=42, anno2="xyz"),
  AnnoNT2, silver_tests);
equalityTest(
  annoNT2a(anno1=_, anno2=_)(42, "xyz"),
  annoNT2(anno1=42, anno2="xyz"),
  AnnoNT2, silver_tests);

wrongCode "Unexpected positional arguments for annotation update of nonterminal silver_features:anno:AnnoNT2" {
  global annoUpdatePosBad::AnnoNT2 = annoNT2a(7, anno2="8");
}
