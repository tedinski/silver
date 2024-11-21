

fun succ Integer ::= i::Integer = i + 1;

-- map tests
equalityTest ( map(succ, [1,2,3,4]), [2,3,4,5],
               [Integer], core_tests ) ;
equalityTest ( map(succ, []), [],
               [Integer], core_tests ) ;

fun sub Integer ::= x::Integer y::Integer = x - y;

-- fold tests
equalityTest ( foldl(sub, 1, [3]), -2,
               Integer, core_tests ) ;
equalityTest ( foldl(sub, 10, [2,4]), 4,
               Integer, core_tests ) ;
equalityTest ( foldl(append, "1 ", ["10 ","2 ","4"]), "1 10 2 4",
               String, core_tests ) ;
equalityTest ( foldr(sub, 2, [10,8,4]), 4, 
               Integer, core_tests ) ;
equalityTest ( foldr(append, "2", ["10","8","4"]), "10842", 
               String, core_tests ) ;
equalityTest ( foldr1(sub,[10,4,2]), 8, 
               Integer, core_tests ) ;
equalityTest ( foldl1(sub,[10,4,2]), 4, 
               Integer, core_tests ) ;

fun even Boolean ::= i::Integer = case i of 0 -> true | 1 -> false | _ -> even(i-2) end;

-- filter tests
equalityTest ( filter(even, [1,2,3,4]), [2,4],
               [Integer], core_tests ) ;
equalityTest ( filter(even, [1,2,3]), [2],
               [Integer], core_tests ) ;
equalityTest ( filter(even, [1,5,3,7]), [],
               [Integer], core_tests ) ;
equalityTest ( filter(even, []), [],
               [Integer], core_tests ) ;

-- partition tests

equalityTest ( partition(even, []).fst,   [],
               [Integer], core_tests ) ;
equalityTest ( partition(even, []).snd,   [],
               [Integer], core_tests ) ;
equalityTest ( partition(even, [1]).fst,   [],
               [Integer], core_tests ) ;
equalityTest ( partition(even, [1]).snd,   [1],
               [Integer], core_tests ) ;
equalityTest ( partition(even, [1,2,3,4,5,6,7,8]).fst,   [2,4,6,8],
               [Integer], core_tests ) ;


-- contains TODO

-- nub tests
equalityTest ( nub ([1,2,3,4,3,2,1]), [1,2,3,4], 
               [Integer], core_tests ) ;

equalityTest ( nub ([1,2,3,4]), [1,2,3,4], 
               [Integer], core_tests ) ;

equalityTest ( nub ([ ]), [ ], 
               [Integer], core_tests ) ;

-- uniq tests
equalityTest ( uniq ([1,2,3,3,2,1,1,2]), [1,2,3,2,1,2], 
               [Integer], core_tests ) ;

equalityTest ( uniq ([1,2,3,4]), [1,2,3,4], 
               [Integer], core_tests ) ;

equalityTest ( uniq ([ ]), [ ], 
               [Integer], core_tests ) ;

-- remove tests
equalityTest ( remove (2, [1,2,3,4,3,2,1]), [1,3,4,3,1],
               [Integer], core_tests ) ;

equalityTest ( remove (9, [1,2,3,4,3,2,1]), [1,2,3,4,3,2,1],
               [Integer], core_tests ) ;

equalityTest ( remove (9, [ ]), [ ],
               [Integer], core_tests ) ;

-- removeAll tests
equalityTest ( removeAll ([], [1,2,3]), [1,2,3],
               [Integer], core_tests ) ;

equalityTest ( removeAll ([1,3,5], [1,2,3,4,5,6]), [2,4,6],
               [Integer], core_tests ) ;

equalityTest ( removeAll ([1,3,5], [1,1,3,4,5,3]), [4],
               [Integer], core_tests ) ;
equalityTest ( removeAll ([1,3,5], [5,3,1,3,5]), [],
               [Integer], core_tests ) ;

-- last
equalityTest ( last([5,3,1,3,5]), 5, Integer, core_tests ) ;

-- concat
equalityTest ( concat([[1, 2], [3, 4]]), [1,2,3,4], [Integer], core_tests ) ;
equalityTest ( concat([]), [], [Integer], core_tests ) ;

-- flatMap
fun dupItem [Integer] ::= i::Integer = [i, i];

equalityTest ( flatMap(dupItem, [1, 2]), [1,1,2,2], [Integer], core_tests ) ;

-- drop
equalityTest ( drop(0, [5,3,1,4,7]), [5,3,1,4,7], [Integer], core_tests ) ;
equalityTest ( drop(2, [5,3,1,4,7]), [1,4,7], [Integer], core_tests ) ;
equalityTest ( drop(44, [5,3,1,4,7]), [], [Integer], core_tests ) ;

-- take
equalityTest ( take(0, [5,3,1,4,7]), [], [Integer], core_tests ) ;
equalityTest ( take(2, [5,3,1,4,7]), [5,3], [Integer], core_tests ) ;
equalityTest ( take(44, [5,3,1,4,7]), [5,3,1,4,7], [Integer], core_tests ) ;


fun equals1 Boolean ::= x::Integer = x==1;
fun notEquals1 Boolean ::= x::Integer = x!=1;

-- takeWhile
equalityTest ( takeWhile (equals1, [2,3,1,3,5]), [],
               [Integer], core_tests ) ;
equalityTest ( takeWhile (equals1, [1,1,1,2,3,1,3,5]), [1,1,1],
               [Integer], core_tests ) ;
equalityTest ( takeWhile (equals1, [1,1,1]), [1,1,1],
               [Integer], core_tests ) ;

-- dropWhile
equalityTest ( dropWhile (equals1, [2,3,1,3,5]), [2,3,1,3,5],
               [Integer], core_tests ) ;
equalityTest ( dropWhile (equals1, [1,1,1,2,3,1,3,5]), [2,3,1,3,5],
               [Integer], core_tests ) ;
equalityTest ( dropWhile (equals1, [1,1,1]), [],
               [Integer], core_tests ) ;

-- takeUntil
equalityTest ( takeUntil (equals1, [2,3,1,3,5]), [2,3],
               [Integer], core_tests ) ;
equalityTest ( takeUntil (equals1, [1,1,1,2,3,1,3,5]), [],
               [Integer], core_tests ) ;
equalityTest ( takeUntil (equals1, [2,3,4]), [2,3,4],
               [Integer], core_tests ) ;
equalityTest ( takeUntil (equals1, []), [],
               [Integer], core_tests ) ;

-- positionOf
equalityTest ( positionOf ( 1, []), -1, Integer, core_tests) ;
equalityTest ( positionOf ( 1, [1,2]), 0, Integer, core_tests) ;
equalityTest ( positionOf ( 3, [0,1,2,3]), 3, Integer, core_tests) ;

-- repeat TODO
-- zipWith TODO
-- reverse TODO

-- sort
global emptyIntList::[Integer] = [];
equalityTest ( null(sort(emptyIntList)), true,
               Boolean, core_tests ) ;
equalityTest ( sort(["cd", "ca", "b", "z", "a"]), 
                    ["a", "b", "ca", "cd", "z"],
               [String], core_tests ) ;

-- group
equalityTest ( null(group(emptyIntList)), true,
               Boolean, core_tests ) ;
equalityTest ( map(head, group([1, 1, 2, 1, 2, 2])),     [1,2,1,2],
               [Integer], core_tests ) ;
equalityTest ( head(group([1, 1, 2, 1, 2, 2])),       [1,1],
               [Integer], core_tests ) ;
equalityTest ( map(head,group([1, 2, 1, 3])),        [1,2,1,3],
               [Integer], core_tests ) ;
equalityTest ( head(tail(group([1, 1, 2, 1, 2, 2]))),       [2],
               [Integer], core_tests ) ;
equalityTest ( map(listLength, group([1, 1, 2, 1, 2, 2])),      [2,1,1,2],
               [Integer], core_tests ) ;

-- intersperse
equalityTest ( intersperse(1, [2,3,4,5]), [2,1,3,1,4,1,5], [Integer], core_tests ) ;
equalityTest ( intersperse(1, [2]), [2], [Integer], core_tests ) ;
equalityTest ( intersperse(1, []), [], [Integer], core_tests ) ;

-- set operations
equalityTest ( union ([], []), [],
               [Integer], core_tests ) ;
equalityTest ( union ([1,2,3], []), [1,2,3],
               [Integer], core_tests ) ;
equalityTest ( union ([], [1,2,3]), [1,2,3],
               [Integer], core_tests ) ;
equalityTest ( union ([1,2,3], [4,5,6]), [1,2,3,4,5,6],
               [Integer], core_tests ) ;

equalityTest ( union ([1,2,3], [1,4,5,6]), [2,3,1,4,5,6],
               [Integer], core_tests ) ;
equalityTest ( union ([1,2,3], [3,4,5,6,1]), [2,3,4,5,6,1],
               [Integer], core_tests ) ;

equalityTest ( intersect ([], []), [],
               [Integer], core_tests ) ;
equalityTest ( intersect ([1,2,3], []), [],
               [Integer], core_tests ) ;
equalityTest ( intersect ([], [1,2,3]), [],
               [Integer], core_tests ) ;
equalityTest ( intersect ([1,2,3], [4,5,6]), [],
               [Integer], core_tests ) ;

equalityTest ( intersect ([1,2,3], [4,2,6]), [2],
               [Integer], core_tests ) ;
equalityTest ( intersect ([1,2,3], [4,2,3,6]), [2,3],
               [Integer], core_tests ) ;

equalityTest ( unions ([ [1,2], [2,3], [1,4,5,6] ] ), [1,2,3,4,5,6] ,
                [Integer], core_tests ) ;


-- eq
equalityTest ( emptyIntList == [], true, Boolean, core_tests) ;
equalityTest ( [1] == [1], true, Boolean, core_tests) ;
equalityTest ( [1,2] == [1,2], true, Boolean, core_tests) ;
equalityTest ( [1] == [2], false, Boolean, core_tests) ;
equalityTest ( [1] == [1,2], false, Boolean, core_tests) ;
equalityTest ( [1,2] == [], false, Boolean, core_tests) ;

-- neq
equalityTest ( emptyIntList != [], false, Boolean, core_tests) ;
equalityTest ( [1] != [1], false, Boolean, core_tests) ;
equalityTest ( [1,2] != [1,2], false, Boolean, core_tests) ;
equalityTest ( [1] != [2], true, Boolean, core_tests) ;
equalityTest ( [1] != [1,2], true, Boolean, core_tests) ;
equalityTest ( [1,2] != [], true, Boolean, core_tests) ;

