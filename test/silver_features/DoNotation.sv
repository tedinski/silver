
-- Test Maybe
global doRes1::Maybe<Integer> = do {
  a::Integer <- just(1);
  if a > 0
    then pure(2)
    else nothing();
};

equalityTest(doRes1, just(2), Maybe<Integer>, silver_tests);

global doRes1Untyped::Maybe<Integer> = do {
  a <- just(1);
  if a > 0
    then pure(2)
    else nothing();
};

equalityTest(doRes1Untyped, just(2), Maybe<Integer>, silver_tests);

-- Test list
global doRes2::[Integer] = do {
  a::Integer <- [1, 2, 3];
  b::Integer <- [4, 5, 6];
  return a * b;
};

equalityTest(foldr(\a::Integer b::Integer -> a + b, 0, doRes2), 90, Integer, silver_tests);

global doRes2Untyped::[Integer] = do {
  a <- [1, 2, 3];
  b <- [4, 5, 6];
  return a * b;
};

equalityTest(foldr(\a::Integer b::Integer -> a + b, 0, doRes2Untyped), 90, Integer, silver_tests);

global letRes::[Integer] = do {
  let x = 3;
  return x;
};

equalityTest(letRes, [3], [Integer], silver_tests);

-- Test State
global doRes3::State<Integer Integer> = do {
  a::Integer <- getState();
  setState(a + 1);
  return a * 2;
};

global res3::Pair<Integer Integer> = runState(doRes3, 2);

equalityTest(res3.fst, 3, Integer, silver_tests);
equalityTest(res3.snd, 4, Integer, silver_tests);

-- Test IO
global doRes4::IO<String> = do {
  writeFile("test_out.txt", "Hello");
  appendFile("test_out.txt", ", World!");
  readFile("test_out.txt");
};

equalityTest(evalIO(doRes4, unsafeIO()).iovalue, "Hello, World!", String, silver_tests);

-- Test something that is Applicative but not Monad
nonterminal AMaybe<a>;
production justAL top::AMaybe<a> ::= a {}
production noneAL top::AMaybe<a> ::= {}
instance Functor AMaybe {
  map = \ f::(b ::= a) m::AMaybe<a> ->
    case m of
    | noneAL() -> noneAL()
    | justAL(x) -> justAL(f(x))
    end;
}
instance Apply AMaybe {
  ap = \ mf::AMaybe<(b ::= a)> m::AMaybe<a> ->
    case mf, m of
    | justAL(f), justAL(x) -> justAL(f(x))
    | _, _ -> noneAL()
    end;
}
instance Applicative AMaybe {
  pure = justAL;
}

global doRes5::Maybe<Integer> = do {
  a::Integer <- just(1);
  b::Integer <- just(2);
  return a + b;
};

equalityTest(doRes5, just(3), Maybe<Integer>, silver_tests);

global mdoThing::State<Boolean (Integer ::= Integer)> = mdo {
  b :: Boolean <- getState();
  res :: (Integer ::= Integer) <- pure(\ x::Integer ->
    if b
    then if x == 0 then 1 else x * res(x - 1)
    else if x == 0 then 0 else x + res(x - 1));
  return res;
};

equalityTest(evalState(mdoThing, false)(5), 15, Integer, silver_tests);
equalityTest(evalState(mdoThing, true)(5), 120, Integer, silver_tests);

global mutualMDo::Maybe<(Boolean ::= Integer)> = mdo {
  pure(123);
  even :: (Boolean ::= Integer) <- pure(\ x::Integer -> if x == 0 then true else odd(x - 1, ()));
  pure(456);
  let odd :: (Boolean ::= Integer ()) = \ x::Integer _ -> if x == 0 then false else even(x - 1);
  res::Boolean <- just(even(43));
  return even;
};
equalityTest(mutualMDo.fromJust(0), true, Boolean, silver_tests);
equalityTest(mutualMDo.fromJust(1), false, Boolean, silver_tests);
equalityTest(mutualMDo.fromJust(2), true, Boolean, silver_tests);
equalityTest(mutualMDo.fromJust(3), false, Boolean, silver_tests);
