imports ot_common;

mainTestSuite oitests;

global three :: Nat = s(s(s(z())));
global two :: Nat = three.minusOne;

equalityTest(
	case getOriginInfo(two) of
	| just(originAndRedexOriginInfo(_, _, _, _)) -> "NO"
	| x -> "OK"
	end,
	"OK", String, oitests);