grammar silver:compiler:driver:util;

closed nonterminal DriverAction with order, run<IO<Integer>>;

synthesized attribute order :: Integer;

{--
 - Run actions in order until a non-zero error code is encountered.
 -}
fun runAll IO<Integer> ::= l::[DriverAction] =
  foldl(
    \ prev::IO<Integer> a::DriverAction ->
      bind(prev, \ code::Integer -> if code != 0 then pure(code) else a.run),
    pure(0),
    sortBy(\ a::DriverAction b::DriverAction -> a.order <= b.order, l));
