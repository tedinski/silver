grammar silver:extension:implicit_monads;

--import silver:definition:type:syntax only typerepTypeExpr;

terminal MCase_kwd 'mcase' lexer classes {KEYWORD, RESERVED};


synthesized attribute patternType::Type occurs on Pattern;
synthesized attribute patternTypeList::[Type] occurs on PatternList;

attribute patternTypeList, upSubst, downSubst occurs on MRuleList;
attribute patternTypeList occurs on MatchRule;


aspect production caseExpr_c
top::Expr ::= 'case' es::Exprs 'of' vbar::Opt_Vbar_t ml::MRuleList 'end'
{
  {-
    We just need to take the type off the first pattern to compare for
    things used monadically in matching--if this type doesn't match
    the other types, we'll have an error, so we won't output anything,
    and if this type doesn't have any structure, none of them have any
    structure, since unstructured ones only come from unstructured
    patterns.
  -}
  ml.downSubst = top.downSubst;
  local monadInExprs::Pair<Boolean Type> =
    monadicallyUsedExpr(es.rawExprs, ml.patternTypeList, top.env, ml.upSubst);
  local monadInClauses::Pair<Boolean Type> =
    foldl((\p::Pair<Boolean Type> a::AbstractMatchRule ->
            if p.fst
            then p
            else if isMonad(decorate a with {env=top.env; downSubst=ml.upSubst;}.mtyperep)
                 then pair(true, decorate a with {env=top.env; downSubst=ml.upSubst;}.mtyperep)
                 else p),
          pair(false, errorType()), --error as filler; won't be used
          ml.matchRuleList);

  local basicFailure::Expr = mkStrFunctionInvocation(top.location, "core:error",
                               [stringConst(terminal(String_t, 
                                  "\"Error: pattern match failed at " ++ top.grammarName ++
                                  " " ++ top.location.unparse ++ "\\n\""),
                                location=top.location)]);
  {-
    This will add in a Fail() for an appropriate monad (if the
    expression is well-typed) whenever we are matching against a monad
    or any clause returns a monad.  This does not cover the case where
    a monad type is expected out and the clauses are incomplete.  That
    one will still fail, but I think that will be a rare case.  We
    would need to pass down an expected type for that to work, and we
    haven't done that here.

    Inserting fails breaks down if the current monad's fail is
    expecting something other than a string, integer, float, or list,
    as we don't really have ways to come up with basic fail arguments
    for anything more complex.
  -}
  local failure::Expr = if monadInExprs.fst
                        then case monadFailArgument(monadInExprs.snd, top.location) of
                             | just(x) ->
                               Silver_Expr {
                                 $Expr{monadFail(monadInExprs.snd, top.location)}($Expr{x})
                               }
                             | nothing() -> basicFailure
                             end
                        else if monadInClauses.fst
                             then case monadFailArgument(monadInClauses.snd, top.location) of
                                  | just(x) ->
                                    Silver_Expr {
                                      $Expr{monadFail(monadInClauses.snd, top.location)}($Expr{x})
                                    }
                                  | nothing() -> basicFailure
                                  end
                             else basicFailure;
  --read the comment on the function below if you want to know what it is
  local attribute monadStuff::Pair<[Pair<Type Pair<Expr String>>] [Expr]>;
  monadStuff = monadicMatchTypesNames(es.rawExprs, ml.patternTypeList, top.env, ml.upSubst, 1);
  local monadLocal::Expr =
    buildMonadicBinds(monadStuff.fst,
                      caseExpr(monadStuff.snd,
                               ml.matchRuleList, failure,
                               freshType(), location=top.location));
  top.monadRewritten = monadLocal.monadRewritten;
}
--find if any of the expressions are being matched as their inner type
--if returns (true, ty), ty will be used to find the correct Fail()
function monadicallyUsedExpr
Pair<Boolean Type> ::= elst::[Expr] tylst::[Type] env::Decorated Env sub::Substitution
{
  return case elst, tylst of
              | [], _ -> pair(false, errorType())
              | _, [] -> pair(false, errorType())
              | e::etl, t::ttl ->
                if isMonad(decorate e with {env=env; downSubst=sub;}.mtyperep) &&
                  !isMonad(performSubstitution(t, sub))
                then pair(true, decorate e with {env=env; downSubst=sub;}.mtyperep)
                else monadicallyUsedExpr(etl, ttl, env, sub)
              end;
}
--make a list of the expression types, expressions and names for binding them as
--   well as a new list of expressions for the forward to use
function monadicMatchTypesNames
Pair<[Pair<Type Pair<Expr String>>] [Expr]> ::=
elst::[Expr] tylst::[Type] env::Decorated Env sub::Substitution index::Integer
{
  local attribute subcall::Pair<[Pair<Type Pair<Expr String>>] [Expr]>;
  subcall = case elst, tylst of
            | _::etl, _::ttl -> monadicMatchTypesNames(etl, ttl, env, sub, index+1)
            end;
  local newName::String = "binding_matched_expression_in_case" ++ toString(index);
  return case elst, tylst of
         | [], _ -> pair([], [])
         | _, [] -> pair([], elst)
         | e::etl, t::ttl ->
           if isMonad(decorate e with {env=env; downSubst=sub;}.mtyperep) &&
             !isMonad(performSubstitution(t, sub))
           then pair(pair(decorate e with {env=env; downSubst=sub;}.mtyperep, pair(e, newName)) :: subcall.fst,
                     baseExpr(qName(bogusLoc(), newName), location=bogusLoc()) :: subcall.snd)
           else pair(subcall.fst, e::subcall.snd)
         end;
}
--take a list of things to bind and the name to use in binding them, as well as
--   a base for the binding, and create an expression with all of them bound
function buildMonadicBinds
Expr ::= bindlst::[Pair<Type Pair<Expr String>>] base::Expr
{
  return case bindlst of
         | [] -> base
         | pair(ty,pair(e,n))::rest ->
           Silver_Expr{ $Expr{monadBind(ty, bogusLoc())}
            ($Expr{e},
             $Expr{
               lambdap(
                 productionRHSCons(productionRHSElem(name(n, bogusLoc()),
                                                     '::',
                                                     typerepTypeExpr(monadInnerType(ty),
                                                                     location=bogusLoc()),
                                                     location=bogusLoc()),
                                   productionRHSNil(location=bogusLoc()),
                                   location=bogusLoc()),
                 buildMonadicBinds(rest, base),
                 location=bogusLoc())})}
         end;
}
--case expression that expands, using mplus, to possibly take multiple cases
concrete production mcaseExpr_c
top::Expr ::= 'mcase' es::Exprs 'of' vbar::Opt_Vbar_t ml::MRuleList 'end'
{
  top.unparse = "mcase " ++ es.unparse ++ " of " ++ ml.unparse ++ " end";

  {-
    This will fail if we don't have a monad type somewhere, even if
    the output type is expected to be a monad.  For example, if the
    expected output type is [a], we might expect mcase to map over all
    the patterns and give us all the ones that match in a list, which
    we won't do if there wasn't a list somewhere here in the first
    place.
  -}
  ml.downSubst = top.downSubst;
  local monadInExprs::Pair<Boolean Type> =
    monadicallyUsedExpr(es.rawExprs, ml.patternTypeList, top.env, ml.upSubst);
  local monadInClauses::Pair<Boolean Type> =
    foldl((\p::Pair<Boolean Type> a::AbstractMatchRule ->
            if p.fst
            then p
            else if isMonad(decorate a with {env=top.env; downSubst=ml.upSubst;}.mtyperep)
                 then pair(true, decorate a with {env=top.env; downSubst=ml.upSubst;}.mtyperep)
                 else p),
          pair(false, errorType()), --error as filler; won't be used
          ml.matchRuleList);
  local monad::Type = if monadInExprs.fst
                      then monadInExprs.snd
                      else monadInClauses.snd;
  local mplus::Expr = monadPlus(monad, bogusLoc());
  local mzero::Expr = monadZero(monad, bogusLoc());

  --new names for using lets to bind the incoming expressions
  local newNames::[String] = map(\x::Expr -> "__mcase_var_" ++ toString(genInt()), es.rawExprs);
  local nameExprs::[Expr] = map(\x::String -> baseExpr(qName(bogusLoc(), x), location=bogusLoc()),
                                newNames);
  local caseExprs::[Expr] = map(\x::AbstractMatchRule -> 
                                 caseExpr(nameExprs, [x], mzero, freshType(), location=bogusLoc()),
                                ml.matchRuleList);
  local mplused::Expr = foldl(\rest::Expr current::Expr -> 
                               Silver_Expr{
                                 $Expr{mplus}($Expr{rest}, $Expr{current})
                               },
                              head(caseExprs), tail(caseExprs));
  local letBound::Expr = foldr(\p::Pair<Expr String> rest::Expr ->
                                makeLet(bogusLoc(), p.snd, freshType(), p.fst, rest),
                               mplused, zipWith(pair, es.rawExprs, newNames));

  forwards to if isMonad(monad)
              then if canBeMCased(monad)
                   then letBound
                   else errorExpr([err(top.location, "Monad type " ++
                                   prettyType(performSubstitution(monad, top.finalSubst)) ++
                                   " cannot be used in an mcase as it does not have " ++
                                   "MPlus/MZero defined")], location=top.location)
              else errorExpr([err(top.location, "Need a monad type somewhere in " ++
                                                "an mcase, but did not find one")],
                             location=top.location);
}

aspect production mRuleList_one
top::MRuleList ::= m::MatchRule
{
  top.patternTypeList = m.patternTypeList;
  top.upSubst = top.downSubst;
}

aspect production mRuleList_cons
top::MRuleList ::= h::MatchRule vbar::Vbar_kwd t::MRuleList
{
  top.patternTypeList = h.patternTypeList;
  --need to unify here with t.patternTypeList so, when we reach the case, if there is a
  --   monad pattern farther down where the first one is a wildcard/variable, we'll find
  --   it and not incorrectly identify something as being used non-monadically
  --top.upSubst = foldl(\s::Substitution p::Pair<Type Type> ->
  --                     decorate check(p.fst, p.snd) with {downSubst=s;}.upSubst,
  --                    t.upSubst, zipWith(pair, h.patternTypeList, t.patternTypeList));
  --t.downSubst = top.downSubst;
}

aspect production matchRule_c
top::MatchRule ::= pt::PatternList arr::Arrow_kwd e::Expr
{
  top.patternTypeList = pt.patternTypeList;
}

aspect production patternList_one
top::PatternList ::= p::Pattern
{
--  top.errors := p.errors;

  top.patternTypeList = [p.patternType];
}
aspect production patternList_more
top::PatternList ::= p::Pattern ',' ps1::PatternList
{
--  top.errors := p.errors ++ ps1.errors;

  top.patternTypeList = p.patternType :: ps1.patternTypeList;
}

aspect production patternList_nil
top::PatternList ::=
{
--  top.errors := [];

  top.patternTypeList = [];
}



attribute env, downSubst, merrors, mtyperep occurs on AbstractMatchRule;

aspect production matchRule
top::AbstractMatchRule ::= pl::[Decorated Pattern] cond::Maybe<Expr> e::Expr
{
  e.env = top.env;
  e.downSubst = top.downSubst;
  top.merrors := []; --merrors from e should be picked up in primitive matching
  top.mtyperep = e.mtyperep;
}

