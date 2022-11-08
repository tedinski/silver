grammar silver:compiler:extension:datalog;

import silver:langutil;
import silver:langutil:pp;

synthesized attribute params :: [String];
synthesized attribute factHead :: String;
nonterminal Fact with factHead, params, pp;

synthesized attribute datalogID :: String;

class DatalogRepresentable a {
  @{-
    Represents value with it's datalog representation.
  -}
  datalogID :: (String ::= a);

}

-- Default instances.
-- instance attribute datalogID {} occurs on a => DatalogRepresentable a {
--   datalogID = (.datalogID);
-- }

-- instance attribute datalogID {} occurs on a => DatalogRepresentable Decorated a with i {
--   datalogID = (.datalogID);
-- }

instance DatalogRepresentable String {
  datalogID = id;
}

function getFromDecoratedRefs
Decorated a with i ::= str::String
{
  return error("Foreign Function: getFromDecoratedRefs");
} foreign {
  "java" : return "common.Datalog.fromDatalogID(%str%)";
}

function convertToDatalogIDDecoratedRef
String ::= inp::Decorated a with i
{
  return error("Foreign Function: convertToDatalogIDDecoratedRef");
} foreign {
  "java" : return "common.Datalog.toDatalogID(%inp%)";
}

instance DatalogRepresentable Decorated a with i {
  datalogID = convertToDatalogIDDecoratedRef;
}


synthesized attribute datalogOutFactNames :: [String];
synthesized attribute datalogSynthesizedFacts :: [[Fact]];
synthesized attribute datalogOutputFacts :: Either<String [(String, [Fact])]>;
inherited attribute datalogOutputFactsInh :: [(String, [Fact])];
monoid attribute datalogInput :: [String] with [],++;




@{--
 - Converts a string given into it to uppercase, using java's toUpperCase function.
 - @param str The string given to turn into uppercase
 - @return An outputted string with all letters turned uppercase.
-}
function toUpperCase
String ::= str::String
{
  return error("Not Yet Implemented: toUpperCase");
} foreign {
  "java" : return "new common.StringCatter(%str%.toString().toUpperCase())";
}


function capitalize
String ::= inp::String
{
  local first :: String = substring(0,1,inp);

  return
    if isUpper(first)
    then inp
    else toUpperCase(first) ++ substring(1,length(inp),inp);
}



abstract production factTwo
top::Fact ::= name::String first::String second::String
{
  top.factHead = capitalize(name);
  top.params = [first, second];
  top.pp = pp"${name}: ${first} <-> ${second}";
}


abstract production factThree
top::Fact ::= name::String first::String second::String third::String
{
  top.factHead = capitalize(name);
  top.params = [first, second, third];
  top.pp = pp"${name}: ${first} <-> ${second} <-> ${third}";
}


abstract production factN
top::Fact ::= name::String params::[String]
{
  top.factHead = capitalize(name);
  top.params = params;
  top.pp = pp"${name}: ${params}";
}



function filterFactsOnFirst
DatalogRepresentable a => [Fact] ::= mapLive::[Fact] lookupElem::a
{
  return filter(\elem::Fact -> head(elem.params) == datalogID(lookupElem), mapLive);
}


function factsTwoToSilverList
DatalogRepresentable a => [a] ::= facts::[Fact] silverElems::[a]
{
  return catMaybes
    (map(
      \elem::Fact ->
        find(
          \silverElem::a ->
            datalogID(silverElem) == head(elem.params),
          silverElems),
      facts));
}

function findSilverElem
DatalogRepresentable a => Maybe<a> ::= factStr :: String silverElems::[a]
{
  return find(\silverElem::a -> datalogID(silverElem) == factStr, silverElems);
}


function factsThreeToSilverList
DatalogRepresentable a, DatalogRepresentable b => [(a,b)] ::= facts::[Fact] silverElemsSecond::[a] silverElemsThird::[b]
{
  local outList::[Maybe<(a,b)>] = (map(
      \elem::Fact ->
      case elem.params of
      | first::second::[third] ->
        case (findSilverElem(second,silverElemsSecond), findSilverElem(third,silverElemsThird)) of
        | (just(f),just(s)) -> just((f,s))
        | (_,_) -> unsafeTracePrint(nothing(), s"Didnt find both elems of ${datalogID(second)} in ${show(50,map(datalogID(_),silverElemsSecond))}\nand ${datalogID(third)} in ${show(50,map(datalogID(_),silverElemsThird))}\n")
        end
      | _ -> unsafeTracePrint(nothing(), "Did not list of right shape\n")
      end,
      facts));
  return catMaybes(outList);
}


function lookupFactsThree
DatalogRepresentable a, DatalogRepresentable b, DatalogRepresentable c => [(b,c)] ::= map::[(String,[Fact])] factName::String elem::a silverElemsSecond::[b] silverElemsThird::[c]
{
  return factsThreeToSilverList(
    filterFactsOnFirst(mapsLookup(factName,map),datalogID(elem)),
    silverElemsSecond,
    silverElemsThird);
}
