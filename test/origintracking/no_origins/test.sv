imports ot_common;

mainTestSuite oitests;

global three :: Nat = s(s(s(z())));
global four :: Nat = three.plusOne;
global five :: Nat = four.plusOne;
global two :: Nat = three.minusOne;

equalityTest(identityHashCode(three), identityHashCode(three), Integer, oitests);

equalityTest(
	getOriginInfo(three).isJust,
	false, Boolean, oitests);

equalityTest(
	getOriginInfo(four).isJust,
	false, Boolean, oitests);

equalityTest(
	getOriginInfo(five).isJust,
	false, Boolean, oitests);

equalityTest(
	getOriginInfo(two).isJust,
	false, Boolean, oitests);

global reflectedThree :: AST = reflect(three);

equalityTest(
	getOriginInfo(reflectedThree).isJust,
	false, Boolean, oitests);

global reifiedThree :: Nat = reify(reflectedThree).fromRight;

equalityTest(
	getOriginInfo(reifiedThree).isJust,
	false, Boolean, oitests);

-- -- --

equalityTest(
	getOriginInfo(cstParse("  foo  ", "<inline>").parseTree).isJust,
	false, Boolean, oitests);

equalityTest(
	getParsedOriginLocation(cstParse("  foo  ", "<inline>").parseTree).isJust,
	false, Boolean, oitests);