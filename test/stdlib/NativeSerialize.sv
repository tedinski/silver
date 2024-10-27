import silver:reflect;

annotation thingy::Integer;

nonterminal NSNT with thingy;

terminal NSTerm_t /z*/;

abstract production ns_foo
top::NSNT ::= z::Integer f::Float b::Boolean s::String t::NSTerm_t
{}

abstract production ns_bar
top::NSNT ::= a::NSNT b::NSNT c::[String]
{}


global val1 :: NSNT = ns_bar(ns_foo(1, 0.5, false, "AAA", terminal(NSTerm_t, "zzz"), thingy=42),
                        ns_foo(2, 0.25, true, "BBB", terminal(NSTerm_t, "zzzzzz"), thingy=24),
                        ["garfield", "odie", "nermal"], thingy=2442);
global ser1 :: Either<String ByteArray> = serializeBytes(val1);
global des1 :: Either<String NSNT> = if ser1.isRight then deserializeBytes(ser1.fromRight) else left(ser1.fromLeft);
global fin1 :: String = if des1.isRight then genericShow(des1.fromRight) else des1.fromLeft;

equalityTest(
  genericShow(val1), fin1,
  String, core_tests);



global val2 :: [Integer] = [111, 222, 333];
global ser2 :: Either<String ByteArray> = serializeBytes(val2);
global des2 :: Either<String [Integer]> = if ser2.isRight then deserializeBytes(ser2.fromRight) else left(ser2.fromLeft);
global fin2 :: String = if des2.isRight then genericShow(des2.fromRight) else des2.fromLeft;

equalityTest(
  genericShow(val2), fin2,
  String, core_tests);



global val3 :: [Integer] = [111, 222, 333];
global ser3 :: Either<String ByteArray> = serializeBytes(val3);
global des3 :: Either<String [String]> = if ser3.isRight then deserializeBytes(ser3.fromRight) else left(ser3.fromLeft);
global fin3 :: String = if des3.isRight then genericShow(des3.fromRight) else des3.fromLeft;

equalityTest(
  "Native deserialize is constructing [String], but found [Integer]", fin3,
  String, core_tests);


global val4 :: [Integer] = repeat(123, 65537); -- Test long lists
global ser4 :: Either<String ByteArray> = serializeBytes(val4);
global des4 :: Either<String [Integer]> = if ser4.isRight then deserializeBytes(ser4.fromRight) else left(ser4.fromLeft);
global fin4 :: String = if des4.isRight then genericShow(des4.fromRight) else des4.fromLeft;

equalityTest(
  genericShow(val4), fin4,
  String, core_tests);


global bytefiletest::IO<ByteArray> = do {
  writeBinaryFile("test_svb.svb", serializeBytes(val1).fromRight);
  readBinaryFile("test_svb.svb");
};

equalityTest(genericShow(deserializeBytes(evalIO(bytefiletest, unsafeIO()).iovalue).fromRight), genericShow(val1),
  String, core_tests);
