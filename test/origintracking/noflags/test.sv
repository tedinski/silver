imports ot_common;

mainTestSuite oitests;

global three :: Nat = s(s(s(z())));
global four :: Nat = three.plusOne;
global five :: Nat = four.plusOne;
global two :: Nat = three.minusOne;

equalityTest(identityHashCode(three), identityHashCode(three), Integer, oitests);

equalityTest(
	case getOriginInfo(four) of
    | just(originOriginInfo(link, _)) -> identityHashCode(link)
    | _ -> -1
    end,
	identityHashCode(three), Integer, oitests);

equalityTest(
	case getOriginInfo(five) of
    | just(originOriginInfo(link, _)) -> identityHashCode(link)
    | _ -> -1
    end,
	identityHashCode(four), Integer, oitests);

equalityTest(
	case getOriginInfoChain(five) of
	| _::originOriginInfo(link, _)::_ -> identityHashCode(link)
	| _ -> -1
	end,
	identityHashCode(three), Integer, oitests);

equalityTest(
	case getOriginInfo(three) of
	| just(otherOriginInfo(_, originType=setInGlobalOIT())) -> "OK"
	| _ -> "NO"
	end,
	"OK", String, oitests);

equalityTest(
	case getOriginInfo(two) of
	| just(originAndRedexOriginInfo(_, r, _, _)) -> identityHashCode(r)
	| _ -> -1
	end,
	identityHashCode(three), Integer, oitests);

equalityTest(
	case getOriginInfo(two) of
	| just(originAndRedexOriginInfo(_, _, _, _, originType=setAtNewOIT())) -> "OK"
	| _ -> "NO"
	end,
	"OK", String, oitests);

equalityTest(
	case getOriginInfo(four) of
	| just(originOriginInfo(_, _, originType=setAtConstructionOIT())) -> "OK"
	| _ -> "NO"
	end,
	"OK", String, oitests);

global reflectedThree :: AST = reflect(three);

equalityTest(
	case getOriginInfo(reflectedThree) of
	| just(originOriginInfo(_, _, originType=setFromReflectionOIT())) -> "OK"
	| _ -> "NO"
	end,
	"OK", String, oitests);

equalityTest(
	case getOriginInfo(reflectedThree) of
	| just(originOriginInfo(o, _)) -> identityHashCode(o)
	| _ -> -1
	end,
	identityHashCode(three), Integer, oitests);

global reifiedThree :: Nat = reify(reflectedThree).fromRight;

equalityTest(
	case getOriginInfo(reifiedThree) of
	| just(originOriginInfo(_, _, originType=setFromReificationOIT())) -> "OK"
	| _ -> "NO"
	end,
	"OK", String, oitests);

equalityTest(
	case getOriginInfo(reifiedThree) of
	| just(originOriginInfo(o, _)) -> identityHashCode(o)
	| _ -> -1
	end,
	identityHashCode(reflectedThree), Integer, oitests);

-- -- --

equalityTest(
	getParsedOriginLocationOrFallback(cstParse("  foo  ", "<inline>").parseTree).unparse,
	"<inline>:1:2", String, oitests); --parsed location

equalityTest(
	getParsedOriginLocationOrFallback(cstParse("  foo  ", "<inline>").parseTree.transform).unparse,
	"<inline>:1:2", String, oitests); --transitive parsed location

equalityTest(
	getParsedOriginLocationOrFallback(cstParse("  foo  ", "<inline>").parseTree.transform.transform).unparse,
	"bar", String, oitests); --logicalLocationNote