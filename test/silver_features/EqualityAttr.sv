grammar silver_features;

-- TODO: Move to silver:core
ordering attribute compareKey, compare with compareTo;

nonterminal EqExpr with compareTo, isEqual, compareKey, compare;

abstract production addEqExpr
top::EqExpr ::= e1::EqExpr e2::EqExpr
{
  propagate compareTo, isEqual, compareKey, compare;
}

abstract production intEqExpr
top::EqExpr ::= i::Integer
{
  propagate compareTo, isEqual, compareKey, compare;
}

abstract production appEqExpr
top::EqExpr ::= n::String e::EqExpr
{
  propagate compareTo, isEqual, compareKey, compare;
}

{- TODO: This should give an error, but the error is in generated code at the moment so we can't test for it
abstract production polyEqExpr
Eq a => top::EqExpr ::= x::a
{
  propagate compareTo, isEqual, compare;
}
-}

global ee1::EqExpr = addEqExpr(intEqExpr(42), appEqExpr("abc", intEqExpr(5)));
global ee2::EqExpr = addEqExpr(intEqExpr(42), appEqExpr("c", intEqExpr(5)));
global ee3::EqExpr = addEqExpr(appEqExpr("c", intEqExpr(5)), intEqExpr(42));

-- TODO: Change to use ==/< operators
equalityTest(decorate ee1 with {compareTo = ee1;}.isEqual, true, Boolean, silver_tests);
equalityTest(decorate ee1 with {compareTo = ee2;}.isEqual, false, Boolean, silver_tests);
equalityTest(decorate ee1 with {compareTo = ee3;}.isEqual, false, Boolean, silver_tests);
equalityTest(decorate ee2 with {compareTo = ee1;}.isEqual, false, Boolean, silver_tests);
equalityTest(decorate ee2 with {compareTo = ee2;}.isEqual, true, Boolean, silver_tests);
equalityTest(decorate ee2 with {compareTo = ee3;}.isEqual, false, Boolean, silver_tests);
equalityTest(decorate ee3 with {compareTo = ee1;}.isEqual, false, Boolean, silver_tests);
equalityTest(decorate ee3 with {compareTo = ee2;}.isEqual, false, Boolean, silver_tests);
equalityTest(decorate ee3 with {compareTo = ee3;}.isEqual, true, Boolean, silver_tests);

equalityTest(decorate ee1 with {compareTo = ee1;}.compare < 0, false, Boolean, silver_tests);
equalityTest(decorate ee1 with {compareTo = ee2;}.compare < 0, true, Boolean, silver_tests);
equalityTest(decorate ee1 with {compareTo = ee3;}.compare < 0, false, Boolean, silver_tests);
equalityTest(decorate ee2 with {compareTo = ee1;}.compare < 0, false, Boolean, silver_tests);
equalityTest(decorate ee2 with {compareTo = ee2;}.compare < 0, false, Boolean, silver_tests);
equalityTest(decorate ee2 with {compareTo = ee3;}.compare < 0, false, Boolean, silver_tests);
equalityTest(decorate ee3 with {compareTo = ee1;}.compare < 0, true, Boolean, silver_tests);
equalityTest(decorate ee3 with {compareTo = ee2;}.compare < 0, true, Boolean, silver_tests);
equalityTest(decorate ee3 with {compareTo = ee3;}.compare < 0, false, Boolean, silver_tests);
