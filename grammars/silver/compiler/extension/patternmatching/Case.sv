grammar silver:compiler:extension:patternmatching;

imports silver:util:treeset as ts;

imports silver:compiler:definition:core;
imports silver:compiler:definition:env;
imports silver:compiler:definition:type;
imports silver:compiler:modification:primitivepattern;
imports silver:compiler:modification:list;

--Get mwdaWrn production for completeness analysis
import silver:compiler:analysis:warnings:flow;
import silver:compiler:definition:flow:env;

import silver:compiler:definition:type:syntax only typerepTypeExpr;
import silver:compiler:modification:let_fix;

import silver:util:cmdargs hiding name;

terminal Case_kwd 'case' lexer classes {KEYWORD,RESERVED};
terminal Of_kwd 'of' lexer classes {KEYWORD,RESERVED};
terminal Arrow_kwd '->' lexer classes {SPECOP};
terminal Vbar_kwd '|' lexer classes {SPECOP};
terminal Opt_Vbar_t /\|?/ lexer classes {SPECOP}; -- optional Coq-style vbar.
terminal When_kwd 'when' lexer classes {KEYWORD,RESERVED};
terminal Matches_kwd 'matches' lexer classes {KEYWORD};

-- MR | ...
tracked nonterminal MRuleList with config, grammarName, unparse, env, frame, errors, freeVars, matchRuleList, matchRulePatternSize;
propagate config, grammarName, frame, env, errors, freeVars, matchRulePatternSize on MRuleList;

-- Turns MRuleList (of MatchRules) into [AbstractMatchRule]
synthesized attribute matchRuleList :: [AbstractMatchRule];
-- Notification of the number of expressions being matched upon
inherited attribute matchRulePatternSize :: Integer;

-- P -> E
tracked nonterminal MatchRule with config, grammarName, unparse, env, frame, errors, freeVars, matchRuleList, matchRulePatternSize;
tracked nonterminal AbstractMatchRule with unparse, frame, freeVars, headPattern, isVarMatchRule, expandHeadPattern, hasCondition;

-- The head pattern of a match rule
synthesized attribute headPattern :: Decorated Pattern;
-- Whether the head pattern of a match rule is a variable binder or not
synthesized attribute isVarMatchRule :: Boolean;
-- Turns A(B, C), D into B, C, D in the patterns list, with a list of named patterns to include.
synthesized attribute expandHeadPattern :: (AbstractMatchRule ::= [String]);
-- For completeness checking, we need to know if we have a condition
synthesized attribute hasCondition::Boolean;

synthesized attribute count::Integer;

-- P , ...
tracked nonterminal PatternList with config, grammarName, unparse, count, patternList, env, frame, errors, patternVars, patternVarEnv;
propagate config, grammarName, frame, env, errors on PatternList;

-- Turns PatternList into [Pattern]
synthesized attribute patternList :: [Decorated Pattern];


{- NOTE ON ERRORS: #HACK2012
 -
 - All of the real error checking should be done in PrimitiveMatch.sv on the
 - more primitive form of pattern matching. BUT, there are a few
 - kinds of errors that the pattern matching compiler will OBSCURE
 - and so we must check for them here.
 -
 - ANY error on MRuleList, MatchRule, PatternList, or Pattern should
 - be accompanied by a comment explaining why it's there, and not on
 - primitive match.
 -}


concrete production caseExpr_c
top::Expr ::= 'case' es::Exprs 'of' Opt_Vbar_t ml::MRuleList 'end'
{
  top.unparse = "case " ++ es.unparse ++ " of " ++ ml.unparse ++ " end";
  propagate config, grammarName, frame, env, freeVars;

  ml.matchRulePatternSize = length(es.rawExprs);
  top.errors <- ml.errors;
  
  -- TODO: this is the only use of .rawExprs. FIXME
  -- introduce the failure case here.
  forwards to 
    caseExpr(es.rawExprs, ml.matchRuleList, true,
      mkStrFunctionInvocation("silver:core:error",
        [stringConst(terminal(String_t, 
          "\"Error: pattern match failed at " ++ top.grammarName ++ ":" ++ getParsedOriginLocationOrFallback(top).unparse ++ "\\n\""))]),
      freshType());
}


--Argument `complete` controls whether we check for case completeness or not  (true -> check)
--This is used so generated case expressions can avoid the incomplete check
abstract production caseExpr
top::Expr ::= es::[Expr] ml::[AbstractMatchRule] complete::Boolean failExpr::Expr retType::Type
{
  top.unparse =
    "(case " ++ implode(", ", map((.unparse), es)) ++ " of " ++ 
    implode(" | ", map((.unparse), ml)) ++ " | _ -> " ++ failExpr.unparse ++
    " end :: " ++ prettyType(^retType) ++ ")";
  propagate frame;
  top.freeVars := concat(map(getFreeVars(top.frame, _), es) ++ map(getFreeVars(top.frame, _), ml) ++ [failExpr.freeVars]);

  {-Checking Pattern Completeness

    We want to check if a set of patterns covers all possible cases.
    For this, we need to consider closed and non-closed nonterminals
    separately.  We will NOT count match rules with conditions as
    contributing to completeness, as we will assume conditions are
    actually conditional, and the rule with a condition will sometimes
    match and sometimes not.
  -}
  local conditionlessRules::[AbstractMatchRule] =
        partition((.hasCondition), ml).snd;
  local conditionlessPatterns::[[Decorated Pattern]] =
        map(\ x::AbstractMatchRule ->
              case x of
              | matchRule(plst, _, _) -> plst
              end, conditionlessRules);
  local completenessCounterExample::Maybe<[Pattern]> =
        checkCompleteness(conditionlessPatterns, top.env, top.flowEnv);

  top.errors <-
      case completenessCounterExample of
      | just(lst) when complete ->
        [mwdaWrnFromOrigin(top,
                 "This pattern-matching is not exhaustive.  Here is an example of a " ++
                   "case that is not matched:  " ++ implode(", ", map((.unparse), lst)))]
      | _ -> []
      end;

  --If we have only conditional rules, it isn't complete
  top.errors <-
      if complete && length(conditionlessRules) == 0 && length(ml) > 0
      then [mwdaWrnFromOrigin(top,
               "This pattern-matching is not exhaustive because it only has conditional rules")]
      else [];


  {-Checking Pattern Overlaps

    We want to check if a set of patterns has cases which do not have
    any patterns to distinguish between them.  We do this by grouping
    patterns as if we were compiling a pattern match from a conventional
    (non-extensible) functional language, reducing until we have no
    patterns left.
  -}
  top.errors <- checkOverlappingPatterns(es, ml);


  {-
    With the addition of completeness checking, we cannot
    incrementally forward through a series of caseExpr, compiling
    toward primitive matching as we go.  That would lead to a lot of
    false incompletes.  Instead, we compile it in a function.

    We bind the expressions being matched with let expressions for
    efficiency.
  -}
  local names::[String] =
        map(\ x::Expr -> "__match_expr_" ++ toString(genInt()), es);
  local nameExprs::[Expr] =
        map(\ x::String -> baseExpr(qName(x)), names);
  nondecorated local compiledCase::Expr =
        compileCaseExpr(nameExprs, ml, ^failExpr, ^retType, top.env);
  nondecorated local fwdResult::Expr =
    foldr(\ p::(String, Expr) rest::Expr ->
            makeLet(p.1, freshType(), p.2, rest),
          compiledCase, zip(names, es));
  forwards to fwdResult;
}

function getFreeVars
attribute frame occurs on a,
attribute freeVars {frame} occurs on a =>
ts:Set<String> ::= frame::BlockContext x::a
{
  x.frame = ^frame;
  return x.freeVars;
}


--Get the initial segment of the match rules which all have the same
--pattern type (constructor or var) and the rest of the rules
fun initialSegmentPatternType
Pair<[AbstractMatchRule] [AbstractMatchRule]> ::= lst::[AbstractMatchRule] =
  case lst of
    --this probably shouldn't be called with an empty list, but catch it anyway
  | [] -> ([], [])
  | [mr] -> ([mr], [])
  | mr1::mr2::rest ->
    if mr1.isVarMatchRule == mr2.isVarMatchRule
    then --both have the same type of pattern
       let sub::Pair<[AbstractMatchRule] [AbstractMatchRule]> = initialSegmentPatternType(mr2::rest)
       in (mr1::sub.fst, sub.snd) end
    else --the first has a different type of pattern than the second
       ([mr1], mr2::rest)
  end;


{-
 - Split rules into separate groups based on segments of the same kind of pattern type
 - Assumes all match rules have at least one pattern; otherwise, you WILL get an error
 -
 - Consecutive variable patterns can go together, as they are simply
 -    turned into let expressions.
 - Consecutive non-forwarding patterns (including primitive patterns)
 -    can go together, since a value can only match one of them.
 - Consecutive instances of the same forwarding pattern can go together.
 -    Different forwarding productions need to go separately in case one
 -    would forward to the other (e.g. patterns `b() -> e1 | c() -> e2`
 -    where c() forwards to b() would match c() first if in the same
 -    primitive match).
-}
function splitPatternGroups
[[AbstractMatchRule]] ::= ml::[AbstractMatchRule] env::Env
{
  local firstPatt::Decorated Pattern = head(ml).headPattern;

  --First pattern is a variable
  local vars::[AbstractMatchRule] = takeWhile((.isVarMatchRule), ml);
  local varsRest::[[AbstractMatchRule]] =
        splitPatternGroups(dropWhile((.isVarMatchRule), ml), env);

  --Type of the patterns; "" if primitive
  local builtType::String = firstPatt.patternTypeName;

  --Primitive patterns, which cannot have forwarding productions and
  --   thus need a different type of check
  local primitives::[AbstractMatchRule] =
        takeWhile(\ r::AbstractMatchRule ->
                    r.headPattern.patternTypeName == "" &&
                    !r.isVarMatchRule, ml);
  local primitivesRest::[[AbstractMatchRule]] =
        splitPatternGroups(dropWhile(\ r::AbstractMatchRule ->
                                       r.headPattern.patternTypeName == "" &&
                                       !r.isVarMatchRule, ml),
                           env);

  --All nonforwarding production names of the current type
  local nonforwardingProds::[String] =
        map((.fullName), filter(\ d::ValueDclInfo -> !d.hasForward, getKnownProds(builtType, env)));

  --Initial segment where the patterns are nonforwarding productions
  local nonforwarding::[AbstractMatchRule] =
        takeWhile(\ r::AbstractMatchRule ->
                    contains(r.headPattern.patternSortKey,
                             nonforwardingProds), ml);
  local nonforwardingRest::[[AbstractMatchRule]] =
        splitPatternGroups(
           dropWhile(\ r::AbstractMatchRule ->
                       contains(r.headPattern.patternSortKey,
                                nonforwardingProds), ml), env);

  --Initial segment where the patterns are forwarding and all the same production
  local forwardingOnes::[AbstractMatchRule] =
        takeWhile(\ r::AbstractMatchRule ->
                    r.headPattern.patternSortKey == firstPatt.patternSortKey,
                  ml);
  local forwardingRest::[[AbstractMatchRule]] =
        splitPatternGroups(
           dropWhile(\ r::AbstractMatchRule ->
                       r.headPattern.patternSortKey == firstPatt.patternSortKey,
                     ml), env);

  return
     case ml of
     | [] -> []
     | _ ->
       if firstPatt.patternIsVariable
       then vars::varsRest
       else if builtType == "" && !firstPatt.patternIsVariable
       then primitives::primitivesRest
       else if contains(firstPatt.patternSortKey, nonforwardingProds)
       then nonforwarding::nonforwardingRest
       else forwardingOnes::forwardingRest
     end;
}


--Compile a case expression `case es of ml` down into primitive matches
function compileCaseExpr
Expr ::= es::[Expr] ml::[AbstractMatchRule] failExpr::Expr retType::Type
         env::Env
{
  --Split rules into segments of non-forwarding constructors, all same
  --   forwarding constructor, and variables based on first pattern
  local groups::[[AbstractMatchRule]] = splitPatternGroups(ml, env);

  nondecorated local compiledGroups::Expr =
        compilePatternGroups(es, groups, ^failExpr, ^retType, env);

  --Check if there is any match rule with empty patterns
  local anyEmptyRules::Boolean =
        any(map(\ m::AbstractMatchRule ->
                  case m of
                  | matchRule([], _, _) -> true
                  | _ -> false
                  end, ml));

  --Assume all the rules are devoid of patterns
  nondecorated local finalStep::Expr =
        foldr(\ mrule::AbstractMatchRule rest::Expr ->
                case mrule of
                | matchRule(_, nothing(), e) -> ^e
                --cond is a Boolean
                | matchRule(_, just((cond, nothing())), e) ->
                  ifThenElse('if', cond, 'then', ^e, 'else', rest)
                --cond is the expression for another match
                | matchRule(_, just((cond, just(patt))), e) ->
                  Silver_Expr {
                     case $Expr{cond} of
                     | $Pattern{patt} -> $Expr{^e}
                     | _ -> $Expr{rest}
                     end
                  }
                end,
              ^failExpr, ml);

  return
     case ml of
     | [] -> ^failExpr
     | _ -> if anyEmptyRules then finalStep else compiledGroups
     end;
}


--Compile a match where the sets of patterns are grouped based on
--having the same kind of first pattern (can go in the same primitive
--match together), create a series of primitive match expressions to
--implement the match
function compilePatternGroups
Expr ::= matchEs::[Expr] ruleGroups::[[AbstractMatchRule]] finalFail::Expr
         retType::Type env::Env
{
  nondecorated local compileRest::Expr =
    compilePatternGroups(matchEs, tail(ruleGroups), ^finalFail,
                         ^retType, env);

  local firstGroup::[AbstractMatchRule] =
        case ruleGroups of
        | [] -> error("Shouldn't access firstGroup with empty ruleGroups")
        | []::tl ->
          error("Shouldn't have empty list of patterns in compilePatternGroups")
        | hd::tl -> hd
        end;
  local firstPatt::Decorated Pattern = head(firstGroup).headPattern;
  local failName::String = "__match_fail_" ++ toString(genInt());
  nondecorated local firstMatchExpr::Expr =
    case matchEs of
    | [] ->
      error("Shouldn't call compilePatternGroups with empty match expressions")
    | e::tl -> e
    end;

  --Modifying the order of rules in the same group (from ruleGroups) is fine,
  --since we either have only the same constructor for a forwarding production
  --or multiple non-forwarding productions where a value can only match one of them
  local constructorGroups::[[AbstractMatchRule]] = groupMRules(firstGroup);
  local mappedPatterns::[PrimPattern] =
          map(allConCaseTransform(head(matchEs), tail(matchEs),
                                  baseExpr(qName(failName)),
                                  ^retType, _, env),
              constructorGroups);
  nondecorated local currentConCase::Expr =
    matchPrimitive(firstMatchExpr, typerepTypeExpr(^retType),
           foldPrimPatterns(mappedPatterns),
           baseExpr(qName(failName)));

  -- A quick note about that freshType() hack: putting it here means there's ONE fresh type
  -- generated, puching it inside 'bindHeadPattern' would generate multiple fresh types.
  -- So don't try that!
  local boundVarRules::[AbstractMatchRule] =
        map(bindHeadPattern(firstMatchExpr, freshType(), _), firstGroup);
  nondecorated local currentVarCase::Expr =
    compileCaseExpr(tail(matchEs), boundVarRules,
       baseExpr(qName(failName)),
       ^retType, env);

  nondecorated local bindFailName::Expr =
    makeLet(failName, ^retType, compileRest,
            if firstPatt.patternIsVariable
            then currentVarCase
            else currentConCase);

  return
     case ruleGroups of
     | [] -> ^finalFail
     | _::_ -> bindFailName
     end;
}

{--
 - Takes a set of matchrules that all match against the SAME CONSTRUCTOR and pushes
 - a complex case-expr within a primitive pattern that matches this constructor.
 -
 - @param currExpr  (The current expression to match against in the overall complex case-expr)
 - @param restExprs  (The remaining expressions to match against in the overall complex case-expr)
 - @param failCase  (The failure expression)
 - @param retType  (The return type of the overall case-expr, and thus this)
 - @param mrs  (Match rules that all share the same head-pattern)
 - @param env  (Known environment)
 -
 - @return  A primitive pattern matching the constructor, with the overall case-expr pushed down into it and compiled
 -}
function allConCaseTransform
PrimPattern ::= currExpr::Expr restExprs::[Expr] failCase::Expr
                retType::Type mrs::[AbstractMatchRule] env::Env
{
  local names :: [Name] = map(patternListVars, head(mrs).headPattern.patternSubPatternList);

  nondecorated local subcase::Expr =
    compileCaseExpr(
       map(exprFromName, names) ++ annoAccesses ++ restExprs,
       map(\ mr::AbstractMatchRule -> mr.expandHeadPattern(annos), mrs),
       ^failCase, ^retType, env);

  local annos :: [String] =
        nub(map(fst, flatMap((.patternNamedSubPatternList), map((.headPattern), mrs))));
  local annoAccesses :: [Expr] =
        map(\ n::String -> access(^currExpr, '.', qNameAttrOccur(qName(n))), annos);
  
  return
    -- Maybe this one is more reasonable? We need to test examples and see what happens...
    attachNote logicalLocationFromOrigin(head(mrs).headPattern) on
      case head(mrs).headPattern of
      | prodAppPattern_named(qn,_,_,_,_,_) -> 
        prodPattern(^qn, '(', convStringsToVarBinders(names), ')', '->', subcase)
      | intPattern(it) -> integerPattern(it, '->', subcase)
      | fltPattern(it) -> floatPattern(it, '->', subcase)
      | strPattern(it) -> stringPattern(it, '->', subcase)
      | truePattern(_) -> booleanPattern("true", '->', subcase)
      | falsePattern(_) -> booleanPattern("false", '->', subcase)
      | nilListPattern(_,_) -> nilPattern(subcase)
      | consListPattern(h,_,t) -> conslstPattern(head(names), head(tail(names)), subcase)
      | _ -> error("Can only have constructor patterns in allConCaseTransform:  " ++ head(mrs).headPattern.unparse)
      end
    end;
}




--Check for overlapping patterns, which show up by standard pattern-matching compilation
function checkOverlappingPatterns
[Message] ::= es::[Expr] ml::[AbstractMatchRule]
{
  local errors::[Message] =
    case ml of
    --check for multiple match rules, with no patterns/conditions left to distinguish them
    | matchRule([], _, e) :: _ :: _ ->
      if areUselessPatterns(ml)
      then [errFromOrigin(head(ml), "Pattern has overlapping cases!")]
      else []
    | _ -> []
    end;

  local partMRs :: Pair<[AbstractMatchRule] [AbstractMatchRule]> =
    partition((.isVarMatchRule), ml);
  local varRules :: [AbstractMatchRule] = partMRs.fst;
  local prodRules :: [AbstractMatchRule] = partMRs.snd;

  {--
   - All constructors?  Check children of each constructor together, plus rest
   -}
  local allConCase :: [Message] =
      let constructorGroups::[[AbstractMatchRule]] = groupMRules(prodRules) in
      let mappedErrs::[Message] =
          flatMap(allConCaseCheckOverlapping(es, _), constructorGroups) in
        errors ++ mappedErrs
      end end;

  {--
   - All variables? Drop the first pattern, and check the rest
   -}
  local allVarCase :: [Message] =
     errors ++
     checkOverlappingPatterns(tail(es), map(dropHeadPattern(_), ml));

  {--
    - Mixed con/var? Partition into segments
   -}
  local mixedCase :: [Message] = checkOverlappingMixedCaseMatches(es, ml);

  -- 4 cases: no patterns left, all constructors, all variables, or mixed con/var.
  -- errors cases: more patterns no scrutinees, more scrutinees no patterns, no scrutinees multiple rules
  return
    case ml of
    | matchRule([], c, e) :: _ -> errors
    -- No match rules, only possible through abstract syntax
    | [] -> []
    | _ -> if null(es) then []
           else if null(varRules) then allConCase
           else if null(prodRules) then allVarCase
           else mixedCase
    end;
}

{-
  Check for overlapping patterns when we are mixing constructor and
  variable patterns for first match.  We do this by partitioning the
  list into segments of only constructor or variable patterns in
  order, then checking each segment as its own match.
-}
fun checkOverlappingMixedCaseMatches [Message] ::= es::[Expr] ml::[AbstractMatchRule] =
  if null(ml)
  then []
  else let segments::Pair<[AbstractMatchRule] [AbstractMatchRule]> =
                     initialSegmentPatternType(ml)
       in
         checkOverlappingMixedCaseMatches(es, segments.snd) ++
         checkOverlappingPatterns(es, segments.fst)
       end;

{--
 - Expand the head of a match rule as if matched, and check for
 - overlapping patterns based on the expansion.
 -}
function allConCaseCheckOverlapping
[Message] ::= es::[Expr]  mrs::[AbstractMatchRule]
{
  -- TODO: potential source of buggy error messages. We're using head(mrs) as the source of
  -- authority for the length of pattern variables to match against. But each match rule may
  -- actually have a different length (and .expandHeadPattern just applies whatever is there)
  -- This is an erroneous condition, but it means we transform into a maybe-more erroneous condition.
  local names :: [Name] = map(patternListVars, head(mrs).headPattern.patternSubPatternList);

  attachNote logicalLocationFromOrigin(head(mrs).headPattern);
  local annos :: [String] =
        nub(map(fst, flatMap((.patternNamedSubPatternList), map((.headPattern), mrs))));
  local annoAccesses :: [Expr] =
        map(\ n::String -> access(head(es), '.', qNameAttrOccur(qName(n))), annos);

  local subCaseCheck::[Message] =
        checkOverlappingPatterns(
           map(exprFromName, names) ++ annoAccesses ++ tail(es),
           map(\ mr::AbstractMatchRule -> mr.expandHeadPattern(annos), mrs));
  -- TODO: head(mrs).location is probably not the correct thing to use here?? (generally)

  return subCaseCheck;
}





{-
  We check completeness with a function because we want to recursively
  check, which we cannot do with attributes alone.

  We need the environment to look up any nonterminal matches and see
  if the nonterminal is closed or not.

  We return nothing() if there are some patterns and the patterns are
  complete, and just(plst) if plst is an example of a missing pattern
  set (matching over multiple values at once).
-}
function checkCompleteness
Maybe<[Pattern]> ::= lst::[[Decorated Pattern]] env::Env
                     flowEnv::FlowEnv
{
  local pattGroups::([[Decorated Pattern]], [[Decorated Pattern]]) =
        partition(\ plst::[Decorated Pattern] -> head(plst).patternIsVariable, lst);
  local varGroup::[[Decorated Pattern]] = pattGroups.1;
  local consGroup::[[Decorated Pattern]] = pattGroups.2;

  local allPattLens::[Integer] = map(\ x::[Decorated Pattern] -> length(x), lst);
  local allSameLen::Boolean =
        if null(lst)
        then true
        else all(map(\ x::Integer -> x == head(allPattLens), allPattLens));
  local numPatts::Integer =
        if null(lst) || !allSameLen
        then 0
        else head(allPattLens);

  --We delegate checking based on the kind of pattern which is first in the list.
  local conPatts::[Decorated Pattern] = map(head, consGroup);
  local isPrimPatts::Boolean =
        foldr(\ a::Decorated Pattern b::Boolean -> b || a.isPrimitivePattern,
              false, conPatts);
  local isBoolPatts::Boolean =
        foldr(\ a::Decorated Pattern b::Boolean -> b || a.isBoolPattern,
              false, conPatts);
  local isListPatts::Boolean =
        foldr(\ a::Decorated Pattern b::Boolean -> b || a.isListPattern,
              false, conPatts);

  {-
    Each checking function checks completeness of the first patterns
    in the sets, which are of the appropriate type, including checking
    for variable patterns.  If the first patterns are complete, it
    then handles grouping the rest of the sets of patterns and
    checking if they are complete as well.  Correctly handling
    grouping is the reason we need to have a separate function for
    each kind of pattern.
  -}
  local boolComp::Maybe<[Pattern]> = checkBooleanCompleteness(consGroup, varGroup, env, flowEnv);
  local listComp::Maybe<[Pattern]> = checkListCompleteness(consGroup, varGroup, env, flowEnv);
  local ntComp::Maybe<[Pattern]> = checkNonterminalCompleteness(consGroup, varGroup, env, flowEnv);
  local primComp::Maybe<[Pattern]> = checkPrimitiveCompleteness(consGroup, varGroup, env, flowEnv);

  return
     if numPatts == 0 || !allSameLen
     then nothing()
     else if isBoolPatts
          then boolComp
          else if isListPatts
               then listComp
               else if isPrimPatts
                    then primComp
                    else if length(consGroup) > 0
                         then ntComp
                         else --If we somehow end up with all vars to start, just check the rest
                              case checkCompleteness(map(tail, lst), env, flowEnv) of
                              | nothing() -> nothing()
                              | just(plst) -> just(wildcPattern('_')::plst)
                              end;
}

{-
  We need blanks for (1) output when a production is missing and (2)
  for expanding a variable pattern list to be the same length as an
  expanded list from a head pattern with subpatterns.
-}
fun generateWildcards [Pattern] ::= n::Integer = repeat(wildcPattern('_'), n);

{-
  Sometimes we need to decorate a list of wildcard patterns for the
  type system to pass as an expanded list for completeness checking to
  replace a variable.  We should never need to access anything on
  these, so passing in bottom values for the attributes is fine.
-}
fun decoratePattList [Decorated Pattern] ::= lst::[Pattern] =
  map(\ p::Pattern -> decorate p with {
      grammarName = error("not needed");
      config = error("not needed");
      frame = error("not needed");
      env = error("not needed");
      patternVarEnv = error("not needed");
    }, lst);

--Group sets of patterns by the first pattern in each set
--The core groupBy function doesn't work because it groups contiguous
--   sets, and the patterns might not be contiguous.
fun groupAllPattsByHead [[[Decorated Pattern]]] ::= pattLists::[[Decorated Pattern]] =
  if null(pattLists)
  then []
  else case groupAllPattsByHeadHelp(head(pattLists), tail(pattLists)) of
       | (thisGroup, others) ->
         (head(pattLists)::thisGroup)::groupAllPattsByHead(others)
       end;
fun groupAllPattsByHeadHelp
Pair<[[Decorated Pattern]] [[Decorated Pattern]]> ::=
    item::[Decorated Pattern] rest::[[Decorated Pattern]] =
  case rest of
  | [] -> ([], [])
  | h::t -> case groupAllPattsByHeadHelp(item, t) of
            | (grp, rst) ->
              if head(item).patternSortKey == head(h).patternSortKey
              then (h::grp, rst)
              else (grp, h::rst)
            end
  end;

--This checks the primitive patterns all have the same type and generates an
--   example of a primitive value which is not covered by the given patterns
function generatePrimitiveMissingPattern
Maybe<Pattern> ::= patts::[Decorated Pattern]
{
  local ints::[Integer] =
        foldr(\ p::Decorated Pattern l::[Integer] ->
                case p of
                | intPattern(int_t) -> toInteger(int_t.lexeme)::l
                | _ -> l
                end, [], patts);
  local flts::[Float] =
        foldr(\ p::Decorated Pattern l::[Float] ->
                case p of
                | fltPattern(flt_t) -> toFloat(flt_t.lexeme)::l
                | _ -> l
                end, [], patts);
  local strs::[String] =
        foldr(\ p::Decorated Pattern l::[String] ->
                case p of              --remove quotation marks
                | strPattern(str_t) -> substring(1, length(str_t.lexeme) - 1, str_t.lexeme)::l
                | _ -> l
                end, [], patts);
  return case ints, flts, strs of
         | _::_, [], [] -> just(generateMissingIntegerPattern(ints, 0))
         | [], _::_, [] -> just(generateMissingFloatPattern(flts, 0.0))
         | [], [], _::_ -> just(generateMissingStringPattern(strs, ""))
         | _, _, _ -> nothing() --type error, so don't generate a completeness error
         end;
}

fun generateMissingIntegerPattern Pattern ::= lst::[Integer] initial::Integer =
  if containsBy(\ a::Integer b::Integer -> a == b, initial, lst)
  then generateMissingIntegerPattern(lst, initial + 1)
  else intPattern(terminal(Int_t, toString(initial), bogusLoc()));
fun generateMissingFloatPattern Pattern ::= lst::[Float] initial::Float =
  if containsBy(\ a::Float b::Float -> a == b, initial, lst)
  then generateMissingFloatPattern(lst, initial + 1.0)
  else fltPattern(terminal(Float_t, toString(initial), bogusLoc()));
fun generateMissingStringPattern Pattern ::= lst::[String] initial::String =
  if containsBy(\ a::String b::String -> a == b, initial, lst)
  then generateMissingStringPattern(lst, initial ++ "*")
  else strPattern(terminal(String_t, "\"" ++ initial ++ "\"", bogusLoc()));

--First pattern in each set in conPatts is a primitive
--The first match can only be completed by a variable
function checkPrimitiveCompleteness
Maybe<[Pattern]> ::= conPatts::[[Decorated Pattern]] varPatts::[[Decorated Pattern]]
                     env::Env flowEnv::FlowEnv
{
  local firstPatts::[Decorated Pattern] = map(head, conPatts);
  local firstPattMissing::Maybe<Pattern> =
        generatePrimitiveMissingPattern(firstPatts);
  local numPatts::Integer = length(head(conPatts));

  local grouped::[ [[Decorated Pattern]] ] = groupAllPattsByHead(conPatts);
  local subcallCons::Maybe<[Pattern]> =
        foldr(\ patts::[[Decorated Pattern]] rest::Maybe<[Pattern]> ->
                case rest of
                | nothing() ->
                  case checkCompleteness(map(tail, patts) ++ map(tail, varPatts),
                                         env, flowEnv) of
                  | just(plst) -> just(^head(head(patts))::plst)
                  | nothing() -> nothing()
                  end
                | just(plst) -> just(plst)
                end,
              nothing(), grouped);
  local subcall::Maybe<[Pattern]> =
        case subcallCons of
        | just(plst) -> just(plst)
        | nothing() ->
          --If we have a case not covered by a pattern, we want to fill that in rather than '_'
          --This gives us better error messages for missing patterns
          case checkCompleteness(map(tail, varPatts), env, flowEnv), firstPattMissing of
          | just(plst), just(fp) -> just(fp::plst)
          | just(plst), nothing() -> just(wildcPattern('_')::plst)
          | nothing(), _ -> nothing()
          end
        end;

  return if length(varPatts) > 0
         then subcall
         else case firstPattMissing of
              | just(p) -> just(p::generateWildcards(numPatts - 1))
              | nothing() -> nothing() --only possible if there is a typing error
              end;
}

--First pattern in each set in consPatts is a Boolean pattern
--The first match can be completed by a variable or patterns for true and false
function checkBooleanCompleteness
Maybe<[Pattern]> ::= conPatts::[[Decorated Pattern]] varPatts::[[Decorated Pattern]]
                     env::Env flowEnv::FlowEnv
{
  --create groups for true and false
  local grouped::([[Decorated Pattern]], [[Decorated Pattern]]) =
        partition(\ plst::[Decorated Pattern] -> head(plst).patternSortKey == "true", conPatts);
  local numPatts::Integer = length(head(conPatts));

  local foundTrue::Boolean = length(grouped.1) > 0;
  local foundFalse::Boolean = length(grouped.2) > 0;
  local foundVar::Boolean = length(varPatts) > 0;

  --Check the completeness of the rest of the patterns where 'true' or a variable was first
  local trueSubcall::Maybe<[Pattern]> =
        checkCompleteness(map(\ plst::[Decorated Pattern] -> tail(plst), grouped.1) ++
                          map(\ plst::[Decorated Pattern] -> tail(plst), varPatts),
                          env, flowEnv);
  --Check the completeness of the rest of the patterns where 'false' or a variable was first
  local falseSubcall::Maybe<[Pattern]> =
        checkCompleteness(map(\ plst::[Decorated Pattern] -> tail(plst), grouped.2) ++
                          map(\ plst::[Decorated Pattern] -> tail(plst), varPatts),
                          env, flowEnv);
  --What's missing from subcalls, including the first pattern
  local subcallResult::Maybe<[Pattern]> =
        case trueSubcall of
        | just(lst) -> just(truePattern('true')::lst)
        | nothing() ->
          case falseSubcall of
          | just(lst) -> just(falsePattern('false')::lst)
          | nothing() ->
            --If completed by vars, need to check vars case is complete as well
            if foundTrue && foundFalse
            then nothing()
            else checkCompleteness(varPatts, env, flowEnv)
          end
        end;

  return if foundVar
         then subcallResult
         else if foundTrue
              then if foundFalse
                   then subcallResult
                   else just(falsePattern('false')::generateWildcards(numPatts - 1))
              else just(truePattern('true')::generateWildcards(numPatts - 1));
}

--First pattern in each set in consPatts is a list pattern
--The first match can be completed by a variable or patterns for cons and nil
function checkListCompleteness
Maybe<[Pattern]> ::= conPatts::[[Decorated Pattern]] varPatts::[[Decorated Pattern]]
                     env::Env flowEnv::FlowEnv
{
  --create groups for nil and cons
  local grouped::([[Decorated Pattern]], [[Decorated Pattern]]) =
        partition(\ plst::[Decorated Pattern] -> head(plst).patternSortKey == "silver:core:nil", conPatts);
  local numPatts::Integer = length(head(conPatts));

  local foundNil::Boolean = length(grouped.1) > 0;
  local foundCons::Boolean = length(grouped.2) > 0;
  local foundVar::Boolean = length(varPatts) > 0;

  --Check the completeness of the rest of the patterns where 'nil' or a variable was first
  local nilSubcall::Maybe<[Pattern]> =
        checkCompleteness(map(\ plst::[Decorated Pattern] -> tail(plst), grouped.1) ++
                          map(\ plst::[Decorated Pattern] -> tail(plst), varPatts),
                          env, flowEnv);
  --Check the completeness of the rest of the patterns where 'cons' or a variable was first
  local consSubcall::Maybe<[Pattern]> =
        --We check the subpatterns for the head and tail of the list and the overall tail together
        checkCompleteness(map(\ plst::[Decorated Pattern] ->
                                head(plst).patternSubPatternList ++ tail(plst), grouped.2) ++
                          map(\ plst::[Decorated Pattern] ->
                                decoratePattList(generateWildcards(2)) ++ tail(plst), varPatts),
                          env, flowEnv);
  --What's missing from subcalls, including the first pattern
  local subcallResult::Maybe<[Pattern]> =
        case nilSubcall of
        | just(lst) -> just(nilListPattern('[', ']')::lst)
        | nothing() ->
          case consSubcall of
          --If the missing subpattern is also a cons, wrap it in parentheses to display correctly
          --Otherwise `(a::b)::c` displays as `a::b::c`, which means something different
          | just(consListPattern(hd1, _, tl1)::tl::lst) ->
            just(consListPattern(
                    nestedPatterns('(', consListPattern(^hd1, '::', ^tl1), ')'),
                    '::', tl)::lst)
          | just(hd::tl::lst) ->
            just(consListPattern(hd, '::', tl)::lst)
          | just(_) -> error("List must include patterns for at least head and tail")
          | nothing() ->
            --If completed by vars, need to check vars case is complete as well
            if foundNil && foundCons
            then nothing()
            else checkCompleteness(varPatts, env, flowEnv)
          end
        end;

  return if foundVar
         then subcallResult
         else if foundNil
              then if foundCons
                   then subcallResult
                   else just(consListPattern(wildcPattern('_'), '::',
                                             wildcPattern('_'))::
                             generateWildcards(numPatts - 1))
              else just(nilListPattern('[', ']')::generateWildcards(numPatts - 1));
}

--First pattern in each set in consPatts is a nonterminal pattern
--The first match can be completed by a variable or, for a non-closed nonterminal,
--   by having a pattern for each non-forwarding production
function checkNonterminalCompleteness
Maybe<[Pattern]> ::= conPatts::[[Decorated Pattern]] varPatts::[[Decorated Pattern]]
                     env::Env flowEnv::FlowEnv
{
  local numPatts::Integer = length(head(conPatts));

  --All the patterns ought to have the same type.
  local builtTypes::[String] =
        nubBy(\ a::String b::String -> a == b, map((.patternTypeName), map(head, conPatts)));
  local builtType::String = head(builtTypes);

  --Test whether all the required productions are represented in the productions
  local requiredProds::[String] = getNonforwardingProds(builtType, flowEnv);
  local groupedPatts::[ [[Decorated Pattern]] ] =
        groupAllPattsByHead(conPatts);
  local constructorReps::[Decorated Pattern] =
        map(\ plst::[[Decorated Pattern]] -> head(head(plst)), groupedPatts);
  local allRepresented::Maybe<Pattern> =
        checkAllProdsRepresented(constructorReps, requiredProds, env);

  local hasVar::Boolean = length(varPatts) > 0 && length(head(varPatts)) > 0;
  local isVarCompleted::Boolean = hasVar && allRepresented.isJust;

  --Test whether the children and rests of the list are complete, but only for required productions
  --We don't care whether other productions are complete because they forward to required productions
  local reqGroupedPatts::[ [[Decorated Pattern]] ] =
        filter(\ plst::[[Decorated Pattern]] ->
                 contains(head(head(plst)).patternSortKey, requiredProds), groupedPatts);
  local groupsWithVars::[ [[Decorated Pattern]] ] =
        map(\ plst::[[Decorated Pattern]] -> plst ++ varPatts, reqGroupedPatts);
  local subcallResult::Maybe<[Pattern]> =
        case checkAllProdGroupsComplete(reqGroupedPatts, varPatts, env, flowEnv) of
        | just(plst) -> just(plst)
        | nothing() ->
          --check if it was var completed, and, if so, if the var patterns are complete
          if isVarCompleted
          then
             --If we have a case not covered by a pattern, we want to fill that in rather than '_'
             --This gives us better error messages for missing patterns
             case checkCompleteness(map(tail, varPatts), env, flowEnv), allRepresented of
             | nothing(), _ -> nothing()
             | just(plst), nothing() -> just(wildcPattern('_')::plst)
             | just(plst), just(p) -> just(p::plst)
             end
          else nothing()
        end;

  --To find out if the nonterminal is closed or not, we need to look it up
  local nt::QName = qName(builtType);
  nt.env = env;
  local isClosed::Boolean =
        case nt.lookupType.dcls of
        | ntDcl(_, _, _, closed, _) :: _ -> closed
        | _ -> false -- default, if the lookup fails
        end;

  -- TODO:  named argument patterns are not handled yet
  return
     --If we are building multiple types or have unknown productions,
     --   we have a type error, so don't check completeness
     if length(builtTypes) != 1
     then nothing()
     else if isClosed && !hasVar
               --This is a hack to pass up a message about closed nonterminals as a pattern
          then just(varPattern(name("<default case for closed nonterminal>"))::generateWildcards(numPatts - 1))
          else if hasVar
               then subcallResult
               else case allRepresented of
                    | just(p) -> just(p::generateWildcards(numPatts - 1))
                    | nothing() -> subcallResult
                    end;
}

--Check every set of patterns in conGrps is complete, when varPatts is added to it
function checkAllProdGroupsComplete
Maybe<[Pattern]> ::= conGrps::[ [[Decorated Pattern]] ] varPatts::[[Decorated Pattern]]
                     env::Env flowEnv::FlowEnv
{
  local hdProdPatt::Decorated Pattern = head(head(head(conGrps)));
  local numChildren::Integer = length(hdProdPatt.patternSubPatternList);

  --Check the completeness of the children of the current production, joined with the rest of the pattern list
  local expandedVars::[[Decorated Pattern]] =
        --We need to drop the head and add wildcards for the number of children
        map(\ plst::[Decorated Pattern] ->
            decoratePattList(generateWildcards(numChildren)) ++ tail(plst), varPatts);
  local grpWithVars::[[Decorated Pattern]] =
        map(\ plst::[Decorated Pattern] ->
              head(plst).patternSubPatternList ++ tail(plst), head(conGrps)) ++
        expandedVars;
  local hdComplete::Maybe<[Pattern]> = checkCompleteness(grpWithVars, env, flowEnv);

  return
     case conGrps of
     | [] -> nothing()
     | _::rest ->
       case hdComplete, hdProdPatt of
       | just(plst), prodAppPattern_named(qname, _, _, _, _, _) ->
         just(prodAppPattern(^qname, '(', buildPatternList(take(numChildren, plst), bogusLoc()),
                             ')')::drop(numChildren, plst))
       | just(_), _ -> error("Should not have anything but prodAppPattern_named here")
       | nothing(), _ -> checkAllProdGroupsComplete(rest, varPatts, env, flowEnv)
       end
     end;
}

--check that all required productions are present
function checkAllProdsRepresented
Maybe<Pattern> ::= givenPatts::[Decorated Pattern] requiredProds::[String] env::Env
{
  {-
    We walk down through requiredProds rather than pattGroups.  We
    only care that everything in requiredProds is covered; we don't
    care about anything else which shows up in pattGroups
    (e.g. forwarding productions).
  -}
  local firstProdName::String = head(requiredProds);
  local firstProdQName::QName = qName(firstProdName);
  local pattFound::Boolean =
        foldr(\ p::Decorated Pattern b::Boolean ->
                b || p.patternSortKey == firstProdName,
              false, givenPatts);

  firstProdQName.env = env;
  local firstProdNumArgs::Integer = firstProdQName.lookupValue.typeScheme.typerep.arity;
  nondecorated local wildcards::PatternList =
    buildPatternList(repeat(wildcPattern('_'), firstProdNumArgs), bogusLoc());

  return
     case requiredProds of
     | [] -> nothing()
     | _::rest ->
       if pattFound
       then checkAllProdsRepresented(givenPatts, rest, env)
       else just(prodAppPattern(^firstProdQName, '(', wildcards, ')'))
     end;
}




--Match Rules
concrete production mRuleList_one
top::MRuleList ::= m::MatchRule
{
  top.unparse = m.unparse;

  top.matchRuleList = m.matchRuleList;
}

concrete production mRuleList_cons
top::MRuleList ::= h::MatchRule '|' t::MRuleList
{
  top.unparse = h.unparse ++ " | " ++ t.unparse;
  
  top.matchRuleList = h.matchRuleList ++ t.matchRuleList;
}

concrete production matchRule_c
top::MatchRule ::= pt::PatternList '->' e::Expr
{
  top.unparse = pt.unparse ++ " -> " ++ e.unparse;
  propagate grammarName, frame, config, env;

  top.errors := pt.errors; -- e.errors is examined later, after transformation.
  top.freeVars := ts:removeAll(pt.patternVars, e.freeVars);
  
  top.errors <-
    if length(pt.patternList) == top.matchRulePatternSize then []
    else [errFromOrigin(pt, "case expression matching against " ++ toString(top.matchRulePatternSize) ++ " values, but this rule has " ++ toString(length(pt.patternList)) ++ " patterns")];

  pt.patternVarEnv = [];

  top.matchRuleList = [matchRule(pt.patternList, nothing(), ^e)];
}

concrete production matchRuleWhen_c
top::MatchRule ::= pt::PatternList 'when' cond::Expr '->' e::Expr
{
  top.unparse = pt.unparse ++ " when " ++ cond.unparse ++ " -> " ++ e.unparse;
  propagate grammarName, frame, config, env;

  top.errors := pt.errors; -- e.errors is examined later, after transformation, as is cond.errors
  top.freeVars := ts:removeAll(pt.patternVars, cond.freeVars ++ e.freeVars);
  
  top.errors <-
    if length(pt.patternList) == top.matchRulePatternSize then []
    else [errFromOrigin(pt, "case expression matching against " ++ toString(top.matchRulePatternSize) ++ " values, but this rule has " ++ toString(length(pt.patternList)) ++ " patterns")];

  pt.patternVarEnv = [];

  top.matchRuleList = [matchRule(pt.patternList, just((^cond, nothing())), ^e)];
}

concrete production matchRuleWhenMatches_c
top::MatchRule ::= pt::PatternList 'when' cond::Expr 'matches' p::Pattern '->' e::Expr
{
  top.unparse = pt.unparse ++ " when " ++ cond.unparse ++ " matches " ++ p.unparse ++ " -> " ++ e.unparse;
  propagate grammarName, frame, config, env;

  top.errors := pt.errors; -- e.errors is examined later, after transformation, as is cond.errors
  top.freeVars := ts:removeAll(pt.patternVars, cond.freeVars ++ ts:removeAll(p.patternVars, e.freeVars));
  
  top.errors <-
    if length(pt.patternList) == top.matchRulePatternSize then []
    else [errFromOrigin(pt, "case expression matching against " ++ toString(top.matchRulePatternSize) ++ " values, but this rule has " ++ toString(length(pt.patternList)) ++ " patterns")];

  pt.patternVarEnv = [];
  p.patternVarEnv = pt.patternVars;

  top.matchRuleList = [matchRule(pt.patternList, just((^cond, just(^p))), ^e)];
}

abstract production matchRule
top::AbstractMatchRule ::= pl::[Decorated Pattern]
     --Condition, if it exists, is either a Boolean expression or a
     --   pair of an expression and a pattern for it to match
     cond::Maybe<Pair<Expr Maybe<Pattern>>> e::Expr
{
  top.unparse =
    implode(", ", map((.unparse), pl)) ++
    case cond of
    | just((c, just(p))) -> " when " ++ c.unparse ++ " matches " ++ p.unparse
    | just((c, nothing())) -> " when " ++ c.unparse
    | nothing() -> ""
    end ++
    " -> " ++ e.unparse;
  propagate frame;

  top.freeVars := ts:removeAll(concat(map((.patternVars), pl)),
    case cond of
    | just((e1, just(p))) -> getFreeVars(top.frame, e1) ++ ts:removeAll(p.patternVars, e.freeVars)
    | just((e1, nothing())) -> getFreeVars(top.frame, e1) ++ e.freeVars
    | nothing() -> e.freeVars
    end);
  top.headPattern = head(pl);
  -- If pl is null, and we're consulted, then we're missing patterns, pretend they're _
  top.isVarMatchRule = null(pl) || head(pl).patternIsVariable;
  -- For this, we safely know that pl is not null:
  top.expandHeadPattern = 
    \ named::[String] ->
      matchRule(
        head(pl).patternSubPatternList ++
        map(
          \ n::String ->
            fromMaybe(
              decorate wildcPattern('_')
                with { grammarName = error("not needed"); frame = head(pl).frame; config=head(pl).config; env=head(pl).env; patternVarEnv = []; },
              lookup(n, head(pl).patternNamedSubPatternList)),
          named) ++
        tail(pl),
        cond, ^e);

  top.hasCondition = cond.isJust;
}

concrete production patternList_one
top::PatternList ::= p::Pattern
{
  top.unparse = p.unparse;
  top.count = 1;

  top.patternVars = p.patternVars;
  p.patternVarEnv = top.patternVarEnv;
  
  top.patternList = [p];
}
concrete production patternList_snoc
top::PatternList ::= ps::PatternList ',' p::Pattern 
{
  top.unparse = ps.unparse ++ ", " ++ p.unparse;
  
  forwards to appendPatternList(^ps, patternList_one(^p));
}
abstract production patternList_more
top::PatternList ::= p::Pattern ',' ps1::PatternList
{
  top.unparse = p.unparse ++ (if ps1.unparse == "" then "" else ", " ++ ps1.unparse);
  top.count = 1 + ps1.count;

  top.patternVars = p.patternVars ++ ps1.patternVars;
  p.patternVarEnv = top.patternVarEnv;
  ps1.patternVarEnv = p.patternVarEnv ++ p.patternVars;
  
  top.patternList = p :: ps1.patternList;
}

-- lol, dangling comma bug TODO
concrete production patternList_nil
top::PatternList ::=
{
  top.unparse = "";
  top.count = 0;

  top.patternVars = [];
  top.patternList = [];
}

----------------------------------------------------
-- Added Functions
----------------------------------------------------
function appendPatternList
PatternList ::= p1::PatternList p2::PatternList
{
  return
    case p1 of
    | patternList_more(h, _, t) ->
      patternList_more(^h, ',', appendPatternList(^t, ^p2))
    | patternList_one(h) ->
      patternList_more(^h, ',', ^p2)
    | patternList_nil() -> ^p2
    end;
}

function patternListVars
Name ::= p::Decorated Pattern
{
  local n :: String =
    case p of
    | varPattern(pvn) -> "__sv_pv_" ++ toString(genInt()) ++ "_" ++ pvn.name
    | h -> "__sv_tmp_pv_" ++ toString(genInt())
    end;
  return name(n);
}
fun convStringsToVarBinders VarBinders ::= s::[Name] =
  if null(s) then nilVarBinder()
  else if null(tail(s)) then oneVarBinder(varVarBinder(head(s)))
  else consVarBinder(varVarBinder(head(s)), ',', convStringsToVarBinders(tail(s)));
fun exprFromName Expr ::= n::Name = baseExpr(qNameId(n));

fun foldPrimPatterns PrimPatterns ::= l::[PrimPattern] =
  if null(tail(l)) then onePattern(head(l))
  else consPattern(head(l), '|', foldPrimPatterns(tail(l)));

{--
 - Remove the first pattern from the rule, and put a let binding of it into
 - the expression.
 -
 - Would like to make this an attribute instead of a function, but
 - (a) we don't have lambdas yet, and the attr would need to be a function value
 - (b) we don't have a nice way of applying to all element of a list of functions
 -     e.g. right now we 'map(this(x, y, _), list)'
 -}
function bindHeadPattern
AbstractMatchRule ::= headExpr::Expr  headType::Type  absRule::AbstractMatchRule
{
  attachNote logicalLocationFromOrigin(absRule);

  -- If it's '_' we do nothing, otherwise, bind away!
  return case absRule of
  | matchRule(headPat :: restPat, cond, e) ->
    case headPat.patternVariableName of
    | just(pvn) ->
      matchRule(
        restPat,
        case cond of
        | just((c, p)) -> just((makeLet(pvn, ^headType, ^headExpr, c), p))
        | nothing() -> nothing()
        end,
        makeLet(pvn, ^headType, ^headExpr, ^e))
    | nothing() -> matchRule(restPat, cond, ^e)
    end
  | r -> ^r -- Don't crash when we see a rule with too few patterns (should be an error)
  end;
}

{-
 - Drop the first pattern from a match rule
-}
function dropHeadPattern
AbstractMatchRule ::= absRule::AbstractMatchRule
{
  return case absRule of
  | matchRule(headPat :: restPat, cond, e) ->
    matchRule(restPat, cond, ^e)
  | r -> ^r -- Don't crash when we see a rule with too few patterns (should be an error)
  end;
}

fun makeLet Expr ::= s::String t::Type e::Expr o::Expr =
  letp(
    assignExpr(
      name(s), '::', typerepTypeExpr(t), '=', e),
    o);

instance Eq AbstractMatchRule {
  eq = \ a::AbstractMatchRule b::AbstractMatchRule ->
    a.headPattern.patternSortKey == b.headPattern.patternSortKey;
}
instance Ord AbstractMatchRule {
  lte = \ a::AbstractMatchRule b::AbstractMatchRule ->
    a.headPattern.patternSortKey <= b.headPattern.patternSortKey;
}
{--
 - Given a list of match rules, examine the "head pattern" of each.
 - Sort and group by the key of this head pattern.
 -
 - i.e. [cons, nil, cons] becomes [[cons, cons], [nil]] (where 'cons' is the key of the head pattern)
 -}
fun groupMRules [[AbstractMatchRule]] ::= l::[AbstractMatchRule] = group(sort(l));

{--
 - Given a list of match rules, which are presumed to match empty
 - patterns (this is not checked), turn them into nested
 - conditionals.
 -}
fun buildMatchWhenConditionals Expr ::= ml::[AbstractMatchRule] failExpr::Expr =
  case ml of
  | matchRule(_, just((c, nothing())), e) :: tl ->
    Silver_Expr {
      if $Expr{c}
      then $Expr{^e}
      else $Expr{buildMatchWhenConditionals(tl, failExpr)}
    }
  | matchRule(_, just((c, just(p))), e) :: tl ->
    Silver_Expr {
      case $Expr{c} of
      | $Pattern{p} -> $Expr{^e}
      | _ -> $Expr{buildMatchWhenConditionals(tl, failExpr)}
      end
    }
  | matchRule(_, nothing(), e) :: tl -> ^e
  | [] -> failExpr
  end;

{--
 - Check whether there are patterns that overlap in a list of match
 - rules which are presumed to match empty patterns (this is not
 - checked here).
 -
 - An answer of true definitively means there are useless patterns.
 - An answer of false means there may be, but it would require
 - analysis of the conditions on the patterns to determine whether
 - they are actually useless.  We do not do that.
 -}
fun areUselessPatterns Boolean ::= ml::[AbstractMatchRule] =
  case ml of
  | matchRule(_, just(_), _) :: tl ->
    areUselessPatterns(tl)
  | matchRule(_, nothing(), _) :: _ :: _ -> true
  | matchRule(_, nothing(), _) :: [] -> false
  | [] -> false
  end;


