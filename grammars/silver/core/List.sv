grammar silver:core;

instance Eq a => Eq [a] {
  eq = \ x::[a] y::[a] ->
    case x, y of
    | h1::t1, h2::t2 -> h1 == h2 && t1 == t2
    | [], [] -> true
    | _, _ -> false
    end;
  neq = \ x::[a] y::[a] ->
    case x, y of
    | h1::t1, h2::t2 -> h1 != h2 || t1 != t2
    | [], [] -> false
    | _, _ -> true
    end;
}

instance Ord a => Ord [a] {
  lte = \ x::[a] y::[a] ->
    case x, y of
    | h1::t1, h2::t2 -> if h1 == h2 then t1 <= t2 else h1 < h2
    | [], _ -> true
    | _, _ -> false
    end;
}

instance Functor [] {
  map = \ f::(b ::= a) l::[a] ->
    if null(l) then []
    else f(head(l)) :: map(f, tail(l));
}

instance Apply [] {
  ap = apM;
}


instance Applicative [] {
  pure = \ x::a -> [x];
}

instance Bind [] {
  bind = \ x::[a] y::([b] ::= a) -> flatMap(y, x);
}

instance Monad [] {}

instance MonadFail [] {
  fail = \ _ -> [];
}

instance Alt [] {
  alt = appendList;
}

instance Plus [] {
  empty = [];
}

instance Alternative [] {}

instance MonadZero [] {}
instance MonadPlus [] {}

function mfixList
[a] ::= f::([a] ::= a)
{
  local x::[a] = f(head(x));
  return
    case x of
    | [] -> []
    | h :: _ -> h :: mfixList(compose(tail, f))
    end;
}

instance MonadFix [] {
  mfix = mfixList;
}

@{-
  Types with a notion of length.
-}
-- TODO: In Haskell, length is defined by the Foldable type class.
-- Consider moving this if we add Foldable in the future.
class Length a {
  length :: (Integer ::= a);
}

instance Length [a] {
  length = listLength;
}

@{--
  - Applies a function to each element of a list, and returns a list containing
  - all the results that are just. The same as Haskell's 'mapMaybe' and Rust's
  - filter_map.
  -}
fun filterMap [b] ::= f::(Maybe<b> ::= a)  lst::[a] =
  flatMap(
    \x::a -> case f(x) of
             | just(y) -> [y]
             | nothing() -> []
             end,
    lst);

@{--
 - Applies an operator right-associatively over a list.
 - (i.e. replaces cons with 'f', nil with 'i' in the list)
 -
 - @param f  The operator to apply
 - @param i  The "end element" to use in place of 'nil'
 - @param l  The list to fold
 - @return  The result of the function applied right-associatively to the list.
 -}
fun foldr b ::= f::(b ::= a b)  i::b  l::[a] =
  if null(l) then i
  else f(head(l), foldr(f, i, tail(l)));

@{--
 - Applies an operator left-associatively over a list.
 -
 - @param f  The operator to apply
 - @param i  The value to "start with"
 - @param l  The list to fold
 - @return  The result of the function applied left-associatively to the list.
 -}
fun foldl b ::= f::(b ::= b a)  i::b  l::[a] =
  if null(l) then i
  else foldl(f, f(i, head(l)), tail(l));

@{--
 - Right-fold, assuming there is always one element, and leaving that element
 - unchanged for single element lists. See @link[foldr].
 -}
fun foldr1 a ::= f::(a ::= a a)  l::[a] =
  if null(l) then error("Applying foldr1 to empty list.")
  else if null(tail(l)) then head(l)
  else f(head(l), foldr1(f, tail(l)));

@{-
  - @param f The fold function for combining an element and your accumulator
  - @param i The last element function to apply to the last single element in your list
  - @param l The list being folded over.
  - @return An element that is the result of your combining functions applied to the list elements.
  - Right-Fold, assuming there is always at least one element, and also takes in a function a->b to apply to the last element of a list, and applies that function to the last element.
-}
fun foldrLastElem b ::= f::(b ::= a b)  i::(b ::= a) l::[a] =
  case l of
  | [elem] -> i(elem)
  | h::t -> f(h, foldrLastElem(f,i,t))
  | [] -> error("You can't call foldrLastElem with an empty list")
  end;


@{--
 - Left-fold, assuming there is always one element, and leaving that element
 - unchanged for single element lists. See @link[foldl].
 -}
fun foldl1 a ::= f::(a ::= a a)  l::[a] =
  if null(l) then error("Applying foldl1 to empty list.")
  else foldl(f, head(l), tail(l));

@{--
 - Filter out elements of a list.
 -
 - @param f  The filter function
 - @param lst  The input list to filter
 - @return  Only those elements of 'lst' that 'f' returns true for, in the
 -   same order as they appeared in 'lst'
 -}
fun filter [a] ::= f::(Boolean ::= a) lst::[a] =
  if null(lst)
  then []
  else if f(head(lst))
       then head(lst) :: filter(f, tail(lst))
       else filter(f, tail(lst));

@{--
 - Monadic (actually Applicative) version of filter
 -
 - @param f  The filter function
 - @param lst  The input list to filter
 - @return  Only those elements of 'lst' that 'f' returns true for, in the
 -   same order as they appeared in 'lst'
 -}
fun filterM
Applicative m =>
m<[a]> ::= f::(m<Boolean> ::= a) lst::[a] =
  case lst of
  | [] -> pure([])
  | h :: t -> do {
      cond::Boolean <- f(h);
      rest::[a] <- filterM(f, t);
      return if cond then h :: rest else rest;
    }
  end;

@{--
 - Partition a list in two
 -
 - @param f  Decision function
 - @param lst  The list to partition
 - @return  A pair of all elements returning true, and all elements returning false.
 -}
function partition
Pair<[a] [a]> ::= f::(Boolean ::= a) lst::[a]
{
  local attribute recurse :: Pair<[a] [a]>;
  recurse = partition(f, tail(lst));

  return if null(lst) then ([],[])
         else if f(head(lst))
              then (head(lst) :: recurse.fst, recurse.snd)
              else (recurse.fst, head(lst) :: recurse.snd);
}

@{--
 - Determine if an element appears in a list.
 -
 - @param eq  The equality function to use
 - @param elem  The element to search for
 - @param lst  The list to search
 - @return  True if the equality function returns true for some element of the list,
 -   false otherwise.
 -}
fun containsBy Boolean ::= eq::(Boolean ::= a a)  elem::a  lst::[a] =
  (!null(lst)) && (eq(elem, head(lst)) || containsBy(eq, elem, tail(lst)));

@{--
 - Determine if an element appears in a list.
 -
 - @param elem  The element to search for
 - @param lst  The list to search
 - @return  True if == is true for some element of the list, false otherwise.
 -}
fun contains Eq a => Boolean ::= elem::a  lst::[a] = containsBy(eq, elem, lst);

@{--
 - Removes all duplicates from a list. O(n^2).
 -
 - @param eq  The equality function to use
 - @param xs  The list to remove duplicates from
 - @return  A list containing no duplicates, according to the equality function.
 -}
fun nubBy [a] ::= eq::(Boolean ::= a a)  xs::[a] =
  if null(xs) then []
  else head(xs) :: nubBy(eq, removeBy(eq, head(xs), tail(xs)));

@{--
 - Removes all duplicates from a list. O(n^2).
 -
 - @param xs  The list to remove duplicates from
 - @return  A list containing no duplicates, according to ==.
 -}
fun nub Eq a => [a] ::= xs::[a] = nubBy(eq, xs);

@{--
 - Removes all consecutive duplicates from a list. O(n).
 -
 - This can be used with `sortBy` to perform the same task as `nubBy`, but more
   efficiently.
 -
 - @param eq  The equality function to use
 - @param xs  The list to remove duplicates from
 - @return  A list containing no duplicates, according to the equality function.
 -}
fun uniqBy [a] ::= eq::(Boolean ::= a a)  xs::[a] =
  case xs of
  | [] -> []
  | hd :: tl ->
      if null(tl) then
        xs
      else if eq(hd, head(tl)) then
        uniqBy(eq, tl)
      else
        hd :: uniqBy(eq, tl)
  end;

@{--
 - Removes all consecutive duplicates from a list. O(n).
 -
 - This can be used with `sort` to perform the same task as `nub`, but more
   efficiently.
 -
 - @param xs  The list to remove consecutive duplicates from
 - @return  A list containing no consecutive duplicates, according to ==.
 -}
fun uniq Eq a => [a] ::= xs::[a] = uniqBy(eq, xs);

@{--
 - Removes all instances of an element from a list.
 -
 - @param eq  The equality function to use
 - @param x  The element to remove
 - @param xs  The list to remove the element from
 - @return  A list with no remaining instances of 'x' according to 'eq'
 -}
fun removeBy [a] ::= eq::(Boolean ::= a a)  x::a  xs::[a] =
  if null(xs) then []
  else (if eq(x,head(xs)) then [] else [head(xs)]) ++ removeBy(eq, x, tail(xs));

@{--
 - Removes all instances of an element from a list.
 -
 - @param x  The element to remove
 - @param xs  The list to remove the element from
 - @return  A list with no remaining instances of 'x' according to ==
 -}
fun remove Eq a => [a] ::= x::a  xs::[a] = removeBy(eq, x, xs);

@{--
 - Removes all instances of several elements from a list: xs - ys
 -
 - @param eq  The equality function to use
 - @param ys  The list of elements to remove
 - @param xs  The list to remove elements from
 - @return  A list with no remaining instances in 'ys' according to 'eq'
 -}
fun removeAllBy [a] ::= eq::(Boolean ::= a a)  ys::[a]  xs::[a] =
  if null(ys) then xs
  else removeAllBy(eq, tail(ys), removeBy(eq, head(ys), xs));

@{--
 - Removes all instances of several elements from a list: xs - ys
 -
 - @param ys  The list of elements to remove
 - @param xs  The list to remove elements from
 - @return  A list with no remaining instances in 'ys' according to 'eq'
 -}
fun removeAll Eq a => [a] ::= ys::[a]  xs::[a] = removeAllBy(eq, ys, xs);

@{--
 - Returns the initial elements of a list.
 -
 - @param lst  The list to examine
 - @return  The initial elements of 'lst'. If 'lst' is empty, crash.
 -}
fun init [a] ::= lst::[a] =
  if null(tail(lst))
  then []
  else head(lst)::init(tail(lst));

@{--
 - Returns the last element of a list.
 -
 - @param lst  The list to examine
 - @return  The last element of 'lst'. If 'lst' is empty, crash.
 -}
fun last a ::= lst::[a] =
  if null(tail(lst)) then head(lst)
  else last(tail(lst));

fun drop [a] ::= number::Integer lst::[a] =
  if null(lst) || number <= 0 then lst
  else drop(number-1, tail(lst));
fun take [a] ::= number::Integer lst::[a] =
  if null(lst) || number <= 0 then []
  else head(lst) :: take(number-1, tail(lst));
fun dropWhile [a] ::= f::(Boolean::=a) lst::[a] =
  if null(lst) || !f(head(lst)) then lst
  else dropWhile(f, tail(lst));
fun takeWhile [a] ::= f::(Boolean::=a) lst::[a] =
  if null(lst) || !f(head(lst)) then []
  else head(lst) :: takeWhile(f, tail(lst));
fun takeUntil [a] ::= f::(Boolean::=a) lst::[a] =
  if null(lst) || f(head(lst))
  then []
  else head(lst) :: takeUntil(f, tail(lst));

fun positionOfBy Integer ::= eq::(Boolean ::= a a) x::a xs::[a] = positionOfHelper(eq,x,xs,0);

fun positionOfHelper Integer ::= eq::(Boolean ::= a a) x::a xs::[a] currentPos::Integer =
  if null(xs) then -1
  else if eq(x, head(xs)) then currentPos
  else positionOfHelper(eq, x, tail(xs), currentPos+1);

fun positionOf Eq a => Integer ::= x::a xs::[a] = positionOfBy(eq, x, xs);

fun repeat [a] ::= v::a times::Integer =
  if times <= 0 then []
  else v :: repeat(v, times-1);

fun range [Integer] ::= lower::Integer upper::Integer =
  if lower >= upper then [] else lower :: range(lower + 1, upper);

fun zipWith [c] ::= f::(c ::= a b)  l1::[a]  l2::[b] =
  if null(l1) || null(l2) then []
  else f(head(l1), head(l2)) :: zipWith(f, tail(l1), tail(l2));

fun unzipWith [c] ::= f::(c ::= a b)  l::[(a, b)] =
  if null(l) then []
  else f(head(l).1, head(l).2) :: unzipWith(f, tail(l));

fun zip [(a, b)] ::= l1::[a]  l2::[b] =
  if null(l1) || null(l2) then []
  else (head(l1), head(l2)) :: zip(tail(l1), tail(l2));

function unzip
([a], [b]) ::= l::[(a, b)]
{
  local rest::([a], [b]) = unzip(tail(l));
  return if null(l) then ([], [])
         else (head(l).1 :: rest.1, head(l).2 :: rest.2);
}

fun zip3 [(a, b, c)] ::= l1::[a]  l2::[b]  l3::[c] =
  if null(l1) || null(l2) || null(l3) then []
  else (head(l1), head(l2), head(l3)) :: zip3(tail(l1), tail(l2), tail(l3));

function unzip3
([a], [b], [c]) ::= l::[(a, b, c)]
{
  local rest::([a], [b], [c]) = unzip3(tail(l));
  return if null(l) then ([], [], [])
         else (head(l).1 :: rest.1, head(l).2 :: rest.2, head(l).3 :: rest.3);
}

global enumerate :: ([(Integer, a)] ::= [a]) = enumerateFrom(0, _);
fun enumerateFrom [(Integer, a)] ::= i::Integer l::[a] =
  case l of
  | h :: t -> (i, h) :: enumerateFrom(i + 1, t)
  | [] -> []
  end;

fun reverse [a] ::= lst::[a] = reverseHelp(lst, []);
fun reverseHelp [a] ::= lst::[a] sofar::[a] =
  if null(lst) then sofar
  else reverseHelp(tail(lst), head(lst) :: sofar);

fun sortBy [a] ::= lte::(Boolean ::= a a) lst::[a] = sortByHelp(lte, lst, length(lst));

fun sortByKey Ord b => [a] ::= key::(b ::= a) lst::[a] =
  sortBy(\l::a  r::a -> key(l) <= key(r),
         lst);

fun sort Ord a => [a] ::= lst::[a] = sortByHelp(lte, lst, length(lst));

function sortByHelp -- do not use
[a] ::= lte::(Boolean ::= a a) lst::[a] upTo::Integer
{
  return if upTo == 0 then []
         else if upTo == 1 then [head(lst)]
         else mergeBy(lte, front_half, back_half);

  local attribute front_half :: [a];
  front_half = sortByHelp(lte, lst, middle);

  local attribute back_half :: [a];
  back_half = sortByHelp(lte, drop(middle, lst), upTo - middle);

  local attribute middle :: Integer;
  middle = toInteger(toFloat(upTo) / 2.0);
}
fun mergeBy [a] ::= lte::(Boolean ::= a a) l1::[a] l2::[a] =
  if null(l1) then l2
    else if null(l2) then l1
         else if lte(head(l1), head(l2))
              then head(l1) :: mergeBy(lte, tail(l1), l2)
              else head(l2) :: mergeBy(lte, l1, tail(l2));

function groupBy
[[a]] ::= eq::(Boolean ::= a a) l::[a]
{
  local attribute helpercall :: Pair<[a] [a]>;
  helpercall = groupByHelp(eq, head(l), l);

  return if null(l) then []
         else helpercall.fst :: if null(helpercall.snd) then []
                                else groupBy(eq, helpercall.snd);
}
function groupByHelp -- do not use
Pair<[a] [a]> ::= eq::(Boolean ::= a a) f::a l::[a]
{
  -- f is the representative element we're comparing with, but is not considered
  -- included when we're called.
  local attribute recurse :: Pair<[a] [a]>;
  recurse = groupByHelp(eq, f, tail(l));

  return if null(l) || !eq(f, head(l))
         then ([], l)
         else (head(l) :: recurse.fst, recurse.snd);
}

fun group Eq a => [[a]] ::= l::[a] = groupBy(eq, l);  

@{--
 - Inserts the separator in between all elements of the list.
 -}
fun intersperse [a] ::= sep::a xs::[a] =
  if null(xs) then []
  else if null(tail(xs)) then xs
  else head(xs) :: sep :: intersperse(sep, tail(xs));


-- Set operations
fun unionBy [a] ::= eq::(Boolean ::= a a) l::[a] r::[a] =
  if null(l) then r
  else
  (if containsBy(eq, head(l), r)
   then []
   else [head(l)])
  ++ unionBy(eq, tail(l), r);

fun union Eq a => [a] ::= l::[a] r::[a] = unionBy(eq, l, r);

fun intersectBy [a] ::= eq::(Boolean ::= a a) l::[a] r::[a] =
  if null(l) then []
  else
  (if containsBy(eq, head(l), r)
   then [head(l)]
   else [])
  ++ intersectBy(eq, tail(l), r);

fun intersect Eq a => [a] ::= l::[a] r::[a] = intersectBy(eq, l, r);

fun unionsBy [a] ::= eq::(Boolean ::= a a) ss::[[a]] = nubBy(eq, concat(ss));

fun unions Eq a => [a] ::= ss::[[a]] = nub(concat(ss));

fun powerSet [[a]] ::= xs::[a] =
  case xs of
  | h :: t ->
    let rest::[[a]] = powerSet(t)
    in rest ++ map(cons(h, _), rest)
    end
  | [] -> [[]]
  end;


-- Boolean list operations
fun all Boolean ::= l::[Boolean] = foldr(\ a::Boolean b::Boolean -> a && b, true, l);

fun any Boolean ::= l::[Boolean] = foldr(\ a::Boolean b::Boolean -> a || b, false, l);

--------------------------------------------------------------------------------

function nil
[a] ::=
{
  -- Foreign function expected to handle this here
  -- Needs a new implementation if non-java translation is made.
  return error("foreign function");
} foreign {
  "java" : return "common.ConsCell.nil";
}

function cons
[a] ::= h::a  t::[a]
{
  -- Foreign function expected to handle this here
  -- Needs a new implementation if non-java translation is made.
  return error("foreign function");
} foreign {
  "java" : return "new common.ConsCell(%?h?%, %?t?%)";
}

function appendList
[a] ::= l1::[a] l2::[a]
{
  return case l1 of
  | h :: t -> cons(h, append(t, l2))
  | [] -> l2
  end;
} foreign {
  "java" : return "common.AppendCell.append(%l1%, %?l2?%)";
}


function null
Boolean ::= l::[a]
{
  return case l of
  | [] -> true
  | _ :: _ -> false
  end;
} foreign {
  "java" : return "%l%.nil()";
}

function listLength  -- not called 'length' since this is a builtin language feature, but thats how you should call it.
Integer ::= l::[a]
{
  return case l of
  | _ :: t -> 1 + listLength(t)
  | [] -> 0
  end;
} foreign {
  "java" : return "Integer.valueOf(%l%.length())";
}

function head
a ::= l::[a]
{
  return case l of
  | h :: _ -> h
  | [] -> error("requested head of nil")
  end;
} foreign {
  "java" : return "%l%.head()";
}

function tail
[a] ::= l::[a]
{
  return case l of
  | _ :: t -> t
  | [] -> error("requested tail of nil")
  end;
} foreign {
  "java" : return "%l%.tail()";
}
