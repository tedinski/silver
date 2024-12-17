grammar silver:compiler:extension:implicit_monads;

--import silver:compiler:definition:type:syntax only typerepTypeExpr;

terminal MCase_kwd 'case_any' lexer classes {KEYWORD, RESERVED};


synthesized attribute patternType::Type occurs on Pattern;
synthesized attribute patternTypeList::[Type] occurs on PatternList;

attribute patternTypeList, mUpSubst, mDownSubst occurs on MRuleList;
attribute patternTypeList occurs on MatchRule;


aspect production caseExpr_c
top::Expr ::= 'case' es::Exprs 'of' vbar::Opt_Vbar_t ml::MRuleList 'end'
{
  ml.mDownSubst = top.mDownSubst;
  local monadInExprs::Boolean =
    monadicallyUsedExpr(es.rawExprs, top.env, ml.mUpSubst, top.frame,
                        top.grammarName, top.compiledGrammars, top.config, top.flowEnv,
                        top.expectedMonad, false);
  local monadInClauses::Boolean =
    foldl((\b::Boolean a::AbstractMatchRule ->
            b ||
            let ty::Type = decorate a with {mDownSubst=ml.mUpSubst; temp_env=top.env; temp_frame=top.frame;
                                   temp_grammarName=top.grammarName; temp_compiledGrammars=top.compiledGrammars;
                                   temp_config=top.config; temp_flowEnv=top.flowEnv;
                                   temp_finalSubst=ml.mUpSubst; temp_downSubst=ml.mUpSubst;
                                   expectedMonad=top.expectedMonad;}.mtyperep
            in
              isMonad(ty, top.env) &&
              monadsMatch(ty, top.expectedMonad, ml.mUpSubst).fst && fst(monadsMatch(ty, top.expectedMonad, ml.mUpSubst))
            end),
          false,
          ml.matchRuleList);

  local loc::Location = getParsedOriginLocationOrFallback(ambientOrigin());
  nondecorated local basicFailure::Expr =
    mkStrFunctionInvocation("silver:core:error",
      [stringConst(terminal(String_t, 
         "\"Error: pattern match failed at " ++ top.grammarName ++
         " " ++ loc.unparse ++ "\\n\""))]);
  {-
    Inserting fails breaks down if the current monad's fail is
    expecting something other than a string, integer, float, or list,
    as we don't really have ways to come up with basic fail arguments
    for anything more complex.
  -}
  nondecorated local failure::Expr =
    if isMonadFail(top.expectedMonad, top.env)
    then monadFail()
    else basicFailure;
  {-
    This sets up the actual output type.  If there's a monad, the
    return type given to the case expression is M(freshtype); if not,
    the return type is just a fresh type.
  -}
  nondecorated local outty::Type =
    if monadInExprs
    then monadOfType(top.expectedMonad, freshType())
    else if monadInClauses
         then monadOfType(top.expectedMonad, freshType())
         else if isMonadFail(top.expectedMonad, top.env)
              then monadOfType(top.expectedMonad, freshType())
              else freshType(); --absolutely nothing is a monad
  --read the comment on the function below if you want to know what it is
  local attribute monadStuff::([(Type, Expr, String)], [Expr]);
  monadStuff = monadicMatchTypesNames(redeces.monadDecExprs, ml.patternTypeList, [], top.env,
                                      ml.mUpSubst, top.expectedMonad, 1);
  local attribute redeces::Exprs = ^es;
  redeces.mDownSubst = ml.mUpSubst;
  redeces.downSubst = ml.mUpSubst;
  redeces.finalSubst = ml.mUpSubst;
  redeces.env = top.env;
  redeces.frame = top.frame;
  redeces.grammarName = top.grammarName;
  redeces.compiledGrammars = top.compiledGrammars;
  redeces.config = top.config;
  redeces.flowEnv = top.flowEnv;
  redeces.expectedMonad = top.expectedMonad;

  {-
    We rewrite by pulling the monad-typed expressions on which we are matching
    out, putting them into lets over the case expression, then rewriting that.
    This second rewriting step turns the lets into binds, binding the monadic
    expressions into the case that is not matching on monads, which then
    rewrites everything within the match rules.
  -}
  local monadLocal::Expr =
        foldr(\ p::(Type, Expr, String) rest::Expr ->
                makeLet(p.3, monadInnerType(p.1), p.2, rest),
              caseExpr(monadStuff.snd,
                 ml.matchRuleList, !isMonadFail(top.expectedMonad, top.env), failure,
                 outty),
              monadStuff.1);
  monadLocal.mDownSubst = ml.mUpSubst;
  monadLocal.frame = top.frame;
  monadLocal.grammarName = top.grammarName;
  monadLocal.compiledGrammars = top.compiledGrammars;
  monadLocal.config = top.config;
  monadLocal.env = top.env;
  monadLocal.flowEnv = top.flowEnv;
  monadLocal.downSubst = ml.mUpSubst;
  monadLocal.finalSubst = top.finalSubst;
  monadLocal.expectedMonad = top.expectedMonad;
  monadLocal.decSiteVertexInfo = nothing();
  monadLocal.alwaysDecorated = false;
  monadLocal.appDecSiteVertexInfo = nothing();
  monadLocal.dispatchFlowDeps = [];
  monadLocal.isRoot = false;
  top.monadRewritten = monadLocal.monadRewritten;
  top.mtyperep = monadLocal.mtyperep;
  top.mUpSubst = monadLocal.mUpSubst;

  monadLocal.monadicallyUsed = false;
  --We get the monadic names out of the expressions bound in here and the rest off the fake forward (monadLocal)
  top.monadicNames =
     foldr(\x::Pair<Expr Type> l::[Expr] ->
             let a::Decorated Expr with MonadInhs =
                decorate x.fst with {env=top.env; mDownSubst=top.mDownSubst;
                                     frame=top.frame; grammarName=top.grammarName; downSubst=top.mDownSubst;
                                     finalSubst=top.mDownSubst; compiledGrammars=top.compiledGrammars;
                                     config=top.config; decSiteVertexInfo = nothing(); alwaysDecorated = false;
                                     appDecSiteVertexInfo = nothing(); dispatchFlowDeps = []; flowEnv=top.flowEnv; expectedMonad=top.expectedMonad;
                                     isRoot=top.isRoot;}
             in if isMonad(a.mtyperep, top.env) && monadsMatch(a.mtyperep, top.expectedMonad, top.mDownSubst).fst &&
                   !isMonad(performSubstitution(x.snd, top.mDownSubst), top.env)
                then decorate x.fst with {env=top.env; mDownSubst=top.mDownSubst;
                                     frame=top.frame; grammarName=top.grammarName; downSubst=top.mDownSubst;
                                     finalSubst=top.mDownSubst; compiledGrammars=top.compiledGrammars;
                                     config=top.config; flowEnv=top.flowEnv; monadicallyUsed=true;
                                     expectedMonad=top.expectedMonad;
                                     decSiteVertexInfo = nothing(); alwaysDecorated = false;
                                     appDecSiteVertexInfo = nothing(); dispatchFlowDeps = []; isRoot=top.isRoot;}.monadicNames
                else []
             end ++ l,
           monadLocal.monadicNames, zipWith(\x::Expr y::Type -> (x,y), es.rawExprs, ml.patternTypeList));
}
--find if any of the expressions are being matched as their inner type
--if returns (true, ty), ty will be used to find the correct Fail()
fun monadicallyUsedExpr
Boolean ::= elst::[Expr] env::Env sub::Substitution f::BlockContext gn::String
  cg::EnvTree<Decorated RootSpec> c::Decorated CmdArgs fe::FlowEnv em::Type
  iR::Boolean =
  case elst of
  | [] -> false
  | e::etl ->
    let etyp::Type = decorate e with {env=env; mDownSubst=sub; frame=f; grammarName=gn;
                                      downSubst=sub; finalSubst=sub;
                                      compiledGrammars=cg; config=c; alwaysDecorated = false; flowEnv=fe;
                                      expectedMonad=em; isRoot=iR;}.mtyperep
    in
      fst(monadsMatch(etyp, em, sub)) ||  monadicallyUsedExpr(etl, env, sub, f, gn, cg, c, fe, em, iR)
    end
  end;
--make a list of the expression types, rewritten expressions and names for
--   binding them as well as a new list of expressions for the forward to use
--use a name from names when that is not empty; when empty, use a new name
function monadicMatchTypesNames
([(Type, (Expr, String))], [Expr]) ::=
      elst::[Decorated Expr with MonadInhs]
      tylst::[Type] names::[String] env::Env sub::Substitution em::Type
      index::Integer
{
  local attribute subcall::([(Type, Expr, String)], [Expr]);
  subcall = case elst, tylst of
            | _::etl, _::ttl -> monadicMatchTypesNames(etl, ttl, ntail, env, sub, ^em, index + 1)
            | [], [] -> error("Should not access subcall in monadicMatchTypesNames with empty lists")
            | _, _ -> error("Both lists in monadicMatchTypesNames must be the same length")
            end;
  local ntail::[String] = if null(names) then [] else tail(names);
  local newName::String = if null(names)
                          then "__sv_expression_in_case" ++ toString(index) ++ "_" ++ toString(genInt())
                          else head(names);
  return case elst, tylst of
         | [], _ -> ([], [])
         | _, [] -> ([], map(new, elst))
         | decE::etl, t::ttl ->
           let ety::Type = decE.mtyperep
           in
             if isMonad(ety, env) && fst(monadsMatch(ety, ^em, sub))
             then ((ety, decE.monadRewritten, newName) :: subcall.1,
                   baseExpr(qName(newName)) :: subcall.2)
             else (subcall.1, ^decE::subcall.2)
           end
         end;
}

{-We need to essentially set up our own compilation here for
  monadRewritten because Ted doesn't like duplicating generated code.
  Putting the monad default fail into a let with a monad type is
  turning into a bind over the matching, so everything matching
  fails.-}
aspect production caseExpr
top::Expr ::= es::[Expr] ml::[AbstractMatchRule] complete::Boolean failExpr::Expr retType::Type {
  forward monadLocal = monadCompileCaseExpr(es, ml, ^failExpr, ^retType, top.env);

  top.monadRewritten = monadLocal.monadRewritten;

  top.merrors <- checkOverlappingPatterns(es, ml);
}


{-
  We need to compile the case expression for monad rewriting to take
  advantage of primitive matching's monad rewriting for patterns, but
  without ending up rewriting any lets which will turn out poorly with
  rewriting.  For example, the standard compilation involving
  rewriting to "let __fail = <expr> in <actual match>", which will not
  work for us if our failure expression has a monadic type, as it
  often does.

  This is essentially the standard compilation, but without inserting
  failure lets.

  If there are ever any size problems with the translation here,
  introduce a new production (probably named mLet) which would be a
  let but with monadRewritten being just a let, no checking of types
  and binding them in.  That would be safe, but would still require
  copying the function format from the patternmatching extension.
-}
function monadCompileCaseExpr
Expr ::= es::[Expr] ml::[AbstractMatchRule] failExpr::Expr retType::Type env::Env
{
  --Split rules into segments of non-forwarding constructors, all same
  --   forwarding constructor, and variables based on first pattern
  local groups::[[AbstractMatchRule]] = splitPatternGroups(ml, env);

  nondecorated local compiledGroups::Expr =
        monadCompilePatternGroups(es, groups, ^failExpr, ^retType, env);

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
                     | _ -> $Expr{^failExpr}
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
--
--The same as the compilePatternGroups function from the patternmatching extension,
--   but without using lets which would end up being problematic in our implicit use
function monadCompilePatternGroups
Expr ::= matchEs::[Expr] ruleGroups::[[AbstractMatchRule]] finalFail::Expr
         retType::Type env::Env
{
  nondecorated local compileRest::Expr =
    monadCompilePatternGroups(matchEs, tail(ruleGroups), ^finalFail,
                              ^retType, env);

  local firstGroup::[AbstractMatchRule] =
        case ruleGroups of
        | [] -> error("Shouldn't access firstGroup with empty ruleGroups")
        | []::tl ->
          error("Shouldn't have empty list of patterns in monadCompilePatternGroups")
        | hd::tl -> hd
        end;
  local firstPatt::Decorated Pattern = head(firstGroup).headPattern;
  nondecorated local firstMatchExpr::Expr =
    case matchEs of
    | [] ->
      error("Shouldn't call monadCompilePatternGroups with empty match expressions")
    | e::tl -> e
    end;

  --Modifying the order of rules in the same group (from ruleGroups) is fine,
  --since we either have only the same constructor for a forwarding production
  --or multiple non-forwarding productions where a value can only match one of them
  local constructorGroups::[[AbstractMatchRule]] = groupMRules(firstGroup);
  local mappedPatterns::[PrimPattern] =
          map(monadAllConCaseTransform(head(matchEs), tail(matchEs),
                                       compileRest, ^retType, _, env),
              constructorGroups);
  nondecorated local currentConCase::Expr =
    matchPrimitive(firstMatchExpr, typerepTypeExpr(^retType),
           foldPrimPatterns(mappedPatterns),
           compileRest);

  -- A quick note about that freshType() hack: putting it here means there's ONE fresh type
  -- generated, puching it inside 'bindHeadPattern' would generate multiple fresh types.
  -- So don't try that!
  local boundVarRules::[AbstractMatchRule] =
        map(bindHeadPattern(firstMatchExpr, freshType(), _), firstGroup);
  nondecorated local currentVarCase::Expr =
    monadCompileCaseExpr(tail(matchEs), boundVarRules,
       compileRest, ^retType, env);

  return
     case ruleGroups of
     | [] -> ^finalFail
     | _::_ -> if firstPatt.patternIsVariable
               then currentVarCase
               else currentConCase
     end;
}



{-
  Turn matching on all constructors into primitive matching.
-}
function monadAllConCaseTransform
PrimPattern ::= currExpr::Expr restExprs::[Expr]  failCase::Expr  retType::Type  mrs::[AbstractMatchRule] env::Env
{
  local names :: [Name] = map(patternListVars, head(mrs).headPattern.patternSubPatternList);

  nondecorated local subcase::Expr =
    monadCompileCaseExpr(
      map(exprFromName, names) ++ annoAccesses ++ restExprs,
      map(\ mr::AbstractMatchRule -> mr.expandHeadPattern(annos), mrs),
      ^failCase, ^retType, env);

  local annos :: [String] =
    nub(map(fst, flatMap((.patternNamedSubPatternList), map((.headPattern), mrs))));
  local annoAccesses :: [Expr] =
    map(\ n::String -> access(^currExpr, '.', qNameAttrOccur(qName(n))), annos);
  
  -- Maybe this one is more reasonable? We need to test examples and see what happens...
  local l :: Location = getParsedOriginLocationOrFallback(head(mrs).headPattern);

  return
    case head(mrs).headPattern of
    | prodAppPattern_named(qn,_,_,_,_,_) -> 
        prodPattern(^qn, '(', convStringsToVarBinders(names), ')', terminal(Arrow_kwd, "->", l), subcase)
    | intPattern(it) -> integerPattern(it, terminal(Arrow_kwd, "->", l), subcase)
    | fltPattern(it) -> floatPattern(it, terminal(Arrow_kwd, "->", l), subcase)
    | strPattern(it) -> stringPattern(it, terminal(Arrow_kwd, "->", l), subcase)
    | truePattern(_) -> booleanPattern("true", terminal(Arrow_kwd, "->", l), subcase)
    | falsePattern(_) -> booleanPattern("false", terminal(Arrow_kwd, "->", l), subcase)
    | nilListPattern(_,_) -> nilPattern(subcase)
    | consListPattern(h,_,t) -> conslstPattern(head(names), head(tail(names)), subcase)
    | _ -> error("Can only have constructor patterns in monadAllConCaseTransform")
    end;
}

--case expression that expands, using mplus, to possibly take multiple cases
concrete production mcaseExpr_c
top::Expr ::= 'case_any' es::Exprs 'of' vbar::Opt_Vbar_t ml::MRuleList 'end'
{
  top.unparse = "case_any " ++ es.unparse ++ " of " ++ ml.unparse ++ " end";
  propagate config, grammarName, frame, env;

  top.merrors := [];
  top.merrors <- if isMonadPlus_instance then [] else [errFromOrigin(top, notMonadPlus)];

  ml.mDownSubst = top.mDownSubst;
  local monadInExprs::Boolean =
        monadicallyUsedExpr(es.rawExprs, top.env, ml.mUpSubst, top.frame,
                            top.grammarName, top.compiledGrammars, top.config, top.flowEnv,
                            top.expectedMonad, false);

  nondecorated local mplus::Expr = monadPlus();
  nondecorated local mzero::Expr = monadZero();

  local isMonadPlus_instance::Boolean = isMonadPlus(top.expectedMonad, top.env);
  local notMonadPlus::String =
        monadToString(top.expectedMonad) ++ " is not an instance of " ++
        "MonadPlus and cannot be used with case_any";

  --we need fresh names for the expressions being matched on, which we will use to only evaluate them once
  local newNames::[String] = map(\ x::Expr -> "__sv_mcase_var_" ++ toString(genInt()), es.rawExprs);
  local params::[Pair<String Type>] = zip(newNames, ml.patternTypeList);
  local nameExprs::[Expr] = map(\x::String -> baseExpr(qName(x)),
                                newNames);

  --Build a separate case expression for each match rule with mzero as the failure
  local caseExprs::[Expr] =
        map(\ x::AbstractMatchRule ->
             caseExpr(nameExprs, [x], false, mzero, top.mtyperep),
            ml.matchRuleList);
  --Rewrite the case expressions, wrapped in lambdas to provide the names
  local rewrittenCaseExprs::[Expr] =
         map(\ x::Expr ->
               decorate buildMultiLambda(params, x) with
                 {mDownSubst = top.mDownSubst;
                  frame = top.frame;
                  grammarName = top.grammarName;
                  compiledGrammars = top.compiledGrammars;
                  config = top.config;
                  env = top.env;
                  flowEnv = top.flowEnv;
                  downSubst = top.mDownSubst;
                  finalSubst = top.mDownSubst;
                  expectedMonad = top.expectedMonad;
                  decSiteVertexInfo = nothing();
                  alwaysDecorated = false;
                  appDecSiteVertexInfo = nothing();
                  dispatchFlowDeps = [];
                  isRoot = top.isRoot;
                 }.monadRewritten,
             caseExprs);
  --Take the rewritten functions and apply them to the names to get expressions of a monad type
  local appliedCaseExprs::[Expr] =
        map(\ x::Expr -> buildApplication(x, nameExprs),
            rewrittenCaseExprs);
  --In some cases, they might not return monadic types, so we need to check and add return
  local typecheckedCaseExprs::[Expr] =
        map(\ x::Expr ->
              let ty::Type = decorate x with
                             {flowEnv = top.flowEnv; env = top.env; config=top.config;
                              compiledGrammars=top.compiledGrammars; grammarName=top.grammarName;
                              frame=top.frame; downSubst=top.mDownSubst; finalSubst=top.mDownSubst;
                              decSiteVertexInfo = top.decSiteVertexInfo;
                              appDecSiteVertexInfo = top.appDecSiteVertexInfo; dispatchFlowDeps = []; isRoot=top.isRoot;
                             }.typerep
              in
                if isMonad(ty, top.env) && monadsMatch(ty, top.expectedMonad, top.mDownSubst).fst
                then x
                else buildApplication(monadReturn(), [x])
              end,
            appliedCaseExprs);
  --Mplus the rewritten-and-applied case expressions together
  nondecorated local mplused::Expr =
    foldl(\rest::Expr current::Expr -> 
           Silver_Expr{
             $Expr{mplus}($Expr{rest}, $Expr{current})
           },
          head(typecheckedCaseExprs), tail(typecheckedCaseExprs));
  --Use bind and lambdas to change the names of everything being matched on to only evaluate it once
  nondecorated local applied::Expr =
    mcaseBindsApps(es.rawExprs, newNames, mplused,
                   top.env, ml.mUpSubst, top.frame, top.grammarName,
                   top.compiledGrammars, top.config, top.flowEnv,
                   top.expectedMonad, top.isRoot);

  top.monadRewritten = applied;
  top.mUpSubst = ml.mUpSubst;
  top.mtyperep = monadOfType(top.expectedMonad, freshType());

  --We need to forward to an errorExpr rather than the rewritten version to avoid flow errors
  --Because this should only be used in implicit equations, it should be fine
  forwards to errorExpr([errFromOrigin(top,
                             "Can only use case_any in implicit equations")]);
}

{-
  We walk down exprs and names to either bind head(exprs) using
  head(names) for it if it is monadic, otherwise simply applying it to
  a lambda to change the name.
-}
function mcaseBindsApps
Expr ::= exprs::[Expr] names::[String] base::Expr
         env::Env sub::Substitution f::BlockContext
         gn::String cg::EnvTree<Decorated RootSpec> c::Decorated CmdArgs
         fe::FlowEnv em::Type iR::Boolean
{
  nondecorated local subcall::Expr =
    mcaseBindsApps(tail(exprs), tail(names), ^base,
                   env, sub, ^f, gn, cg, c, fe, ^em, iR);
  return
     if null(exprs)
     then ^base
     else let ety::Type = decorate head(exprs) with
                             {env=env; mDownSubst=sub; frame=^f; grammarName=gn;
                              downSubst=sub; finalSubst=sub;
                              compiledGrammars=cg; config=c; flowEnv=fe;
                              expectedMonad=^em;
                              isRoot = iR; decSiteVertexInfo = nothing(); alwaysDecorated = false;
                              appDecSiteVertexInfo = nothing();
                              dispatchFlowDeps = []; }.mtyperep
           in
             if isMonad(ety, env) && fst(monadsMatch(ety, ^em, sub))
             then buildApplication(
                    monadBind(),
                    [if ety.isDecorated
                      then mkStrFunctionInvocation("silver:core:new", [head(exprs)])
                      else head(exprs),
                      buildLambda(head(names), monadInnerType(ety), subcall)])
             else buildApplication(buildLambda(head(names), dropDecorated(ety), subcall),
                                   [head(exprs)])
           end;
}




synthesized attribute monadDecExprs::[Decorated Expr with MonadInhs];
attribute monadDecExprs, mDownSubst, expectedMonad occurs on Exprs;

aspect production exprsEmpty
top::Exprs ::=
{
  top.monadDecExprs = [];
}
aspect production exprsSingle
top::Exprs ::= e::Expr
{
  e.expectedMonad = top.expectedMonad;
  e.mDownSubst = top.mDownSubst;
  top.monadDecExprs = [e];
}
aspect production exprsCons
top::Exprs ::= e1::Expr ',' e2::Exprs
{
  e1.expectedMonad = top.expectedMonad;
  e1.mDownSubst = top.mDownSubst;
  e2.expectedMonad = top.expectedMonad;
  e2.mDownSubst = top.mDownSubst;
  top.monadDecExprs = e1::e2.monadDecExprs;
}



--There are several thing we need for mtyperep on e which don't occur on match rules
--Therefore we need to pass them here
inherited attribute temp_flowEnv::FlowEnv;
inherited attribute temp_env::Env;
inherited attribute temp_config::Decorated CmdArgs;
inherited attribute temp_compiledGrammars::EnvTree<Decorated RootSpec>;
inherited attribute temp_grammarName::String;
inherited attribute temp_frame::BlockContext;
inherited attribute temp_finalSubst::Substitution;
inherited attribute temp_downSubst::Substitution;
attribute temp_flowEnv, temp_compiledGrammars, temp_grammarName occurs on MatchRule, MRuleList;
attribute mDownSubst occurs on MatchRule;


aspect production mRuleList_one
top::MRuleList ::= m::MatchRule
{
  m.temp_compiledGrammars = top.temp_compiledGrammars;
  m.temp_flowEnv = top.temp_flowEnv;
  m.temp_grammarName = top.temp_grammarName;
  m.mDownSubst = top.mDownSubst;

  top.patternTypeList = m.patternTypeList;
  top.mUpSubst = top.mDownSubst;
}

aspect production mRuleList_cons
top::MRuleList ::= h::MatchRule vbar::Vbar_kwd t::MRuleList
{
  h.temp_compiledGrammars = top.temp_compiledGrammars;
  h.temp_flowEnv = top.temp_flowEnv;
  h.temp_grammarName = top.temp_grammarName;
  h.mDownSubst = top.mDownSubst;

  t.temp_compiledGrammars = top.temp_compiledGrammars;
  t.temp_flowEnv = top.temp_flowEnv;
  t.temp_grammarName = top.temp_grammarName;
  t.mDownSubst = top.mDownSubst;

  top.patternTypeList = h.patternTypeList;
  --need to unify here with t.patternTypeList so, when we reach the case, if there is a
  --   monad pattern farther down where the first one is a wildcard/variable, we'll find
  --   it and not incorrectly identify something as being used non-monadically
  top.mUpSubst = foldl(\s::Substitution p::Pair<Type Type> ->
                       decorate check(p.fst, p.snd) with {downSubst=s;}.upSubst,
                      t.mUpSubst, zip(h.patternTypeList, t.patternTypeList));
}

aspect production matchRule_c
top::MatchRule ::= pt::PatternList arr::Arrow_kwd e::Expr
{
  local ne::Expr = ^e;
  ne.flowEnv = top.temp_flowEnv;
  ne.env = top.env;
  ne.config = top.config;
  ne.compiledGrammars = top.temp_compiledGrammars;
  ne.grammarName = top.temp_grammarName;
  ne.frame = top.frame;
  ne.finalSubst = top.mDownSubst;
  ne.downSubst = top.mDownSubst;
  ne.decSiteVertexInfo = nothing();
  ne.appDecSiteVertexInfo = nothing();
  ne.alwaysDecorated = false;
  ne.dispatchFlowDeps = [];
  ne.isRoot = false;

  top.patternTypeList = pt.patternTypeList;

  top.notExplicitAttributes := ne.notExplicitAttributes;
}

aspect production matchRuleWhen_c
top::MatchRule ::= pt::PatternList 'when' cond::Expr arr::Arrow_kwd e::Expr
{
  local ncond::Expr = ^cond;
  ncond.flowEnv = top.temp_flowEnv;
  ncond.env = top.env;
  ncond.config = top.config;
  ncond.compiledGrammars = top.temp_compiledGrammars;
  ncond.grammarName = top.temp_grammarName;
  ncond.frame = top.frame;
  ncond.finalSubst = top.mDownSubst;
  ncond.downSubst = top.mDownSubst;
  ncond.decSiteVertexInfo = nothing();
  ncond.alwaysDecorated = false;
  ncond.appDecSiteVertexInfo = nothing();
  ncond.dispatchFlowDeps = [];
  ncond.isRoot = false;
  local ne::Expr = ^e;
  ne.flowEnv = top.temp_flowEnv;
  ne.env = top.env;
  ne.config = top.config;
  ne.compiledGrammars = top.temp_compiledGrammars;
  ne.grammarName = top.temp_grammarName;
  ne.frame = top.frame;
  ne.finalSubst = top.mDownSubst;
  ne.downSubst = top.mDownSubst;
  ne.decSiteVertexInfo = nothing();
  ne.alwaysDecorated = false;
  ne.appDecSiteVertexInfo = nothing();
  ne.dispatchFlowDeps = [];
  ne.isRoot = false;

  top.patternTypeList = pt.patternTypeList;

  top.notExplicitAttributes := ncond.notExplicitAttributes ++ ne.notExplicitAttributes;
}

aspect production matchRuleWhenMatches_c
top::MatchRule ::= pt::PatternList 'when' cond::Expr 'matches' p::Pattern arr::Arrow_kwd e::Expr
{
  local ncond::Expr = ^cond;
  ncond.flowEnv = top.temp_flowEnv;
  ncond.env = top.env;
  ncond.config = top.config;
  ncond.compiledGrammars = top.temp_compiledGrammars;
  ncond.grammarName = top.temp_grammarName;
  ncond.frame = top.frame;
  ncond.finalSubst = top.mDownSubst;
  ncond.downSubst = top.mDownSubst;
  ncond.decSiteVertexInfo = nothing();
  ncond.alwaysDecorated = false;
  ncond.appDecSiteVertexInfo = nothing();
  ncond.dispatchFlowDeps = [];
  ncond.isRoot = false;
  local ne::Expr = ^e;
  ne.flowEnv = top.temp_flowEnv;
  ne.env = top.env;
  ne.config = top.config;
  ne.compiledGrammars = top.temp_compiledGrammars;
  ne.grammarName = top.temp_grammarName;
  ne.frame = top.frame;
  ne.finalSubst = top.mDownSubst;
  ne.downSubst = top.mDownSubst;
  ne.decSiteVertexInfo = nothing();
  ne.alwaysDecorated = false;
  ne.appDecSiteVertexInfo = nothing();
  ne.dispatchFlowDeps = [];
  ne.isRoot = false;

  top.patternTypeList = pt.patternTypeList;

  top.notExplicitAttributes := ncond.notExplicitAttributes ++ ne.notExplicitAttributes;
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



attribute temp_flowEnv, temp_env, temp_config, temp_compiledGrammars, temp_grammarName,
          temp_frame, temp_finalSubst, temp_downSubst occurs on AbstractMatchRule;

attribute mDownSubst, merrors, mtyperep, expectedMonad occurs on AbstractMatchRule;

aspect production matchRule
top::AbstractMatchRule ::= pl::[Decorated Pattern] cond::Maybe<(Expr, Maybe<Pattern>)> e::Expr
{
  local ne::Expr = ^e;
  ne.flowEnv = top.temp_flowEnv;
  ne.env = top.temp_env;
  ne.config = top.temp_config;
  ne.compiledGrammars = top.temp_compiledGrammars;
  ne.grammarName = top.temp_grammarName;
  ne.frame = top.temp_frame;
  ne.finalSubst = top.temp_finalSubst;
  ne.downSubst = top.temp_downSubst;
  ne.decSiteVertexInfo = nothing();
  ne.alwaysDecorated = false;
  ne.appDecSiteVertexInfo = nothing();
  ne.dispatchFlowDeps = [];
  ne.isRoot = false;

  ne.mDownSubst = top.mDownSubst;
  ne.expectedMonad = top.expectedMonad;
  top.merrors := []; --merrors from e should be picked up in primitive matching
  top.mtyperep = ne.mtyperep;

  top.notExplicitAttributes := ne.notExplicitAttributes;
}

