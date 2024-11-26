grammar silver:compiler:extension:implicit_monads;

--whether an expression needs to be bound into its immediate parent
--I think this is for let insertion, but I'll leave it here anyway
inherited attribute monadicallyUsed::Boolean occurs on Expr;
--a collection of names/attribute accesses that are monadically used
--it's a list of expressions for attribute accesses
--I think this is for let insertion too
synthesized attribute monadicNames::[Expr] occurs on Expr, AppExpr, AppExprs, AnnoExpr, AnnoAppExprs;

attribute monadRewritten<Expr>, merrors, mtyperep, mDownSubst, mUpSubst, expectedMonad occurs on Expr;
propagate @expectedMonad on Expr;


type MonadInhs = {
  downSubst, finalSubst, frame, grammarName, decSiteVertexInfo, alwaysDecorated, appDecSiteVertexInfo, dispatchFlowDeps, isRoot,
  compiledGrammars, config, env, flowEnv, expectedMonad, mDownSubst
};

flowtype merrors {
  downSubst, finalSubst, frame, grammarName, decSiteVertexInfo, alwaysDecorated, appDecSiteVertexInfo, dispatchFlowDeps, isRoot,
  compiledGrammars, config, env, flowEnv, expectedMonad, mDownSubst
} on Expr;


--list of the attributes accessed in an explicit expression not allowed there
--this is turned into a list of appropriate error messages at the equation
monoid attribute notExplicitAttributes::[Decorated QNameAttrOccur];
attribute notExplicitAttributes occurs on Expr, AppExprs, AnnoAppExprs, MRuleList, Exprs, MatchRule, AbstractMatchRule, AssignExpr;
propagate notExplicitAttributes on Expr, AppExprs, AnnoAppExprs, MRuleList, Exprs, AssignExpr excluding forwardAccess;


aspect default production
top::Expr ::=
{
  top.merrors := [];
}


aspect production errorExpr
top::Expr ::= e::[Message]
{
  top.merrors := e;
  propagate mDownSubst, mUpSubst;
  top.mtyperep = errorType();
  top.monadicNames = [];
  top.monadRewritten = errorExpr(e);
}

aspect production errorReference
top::Expr ::= msg::[Message]  @q::QName
{
  top.merrors := msg;
  propagate mDownSubst, mUpSubst;
  top.mtyperep = errorType();
  top.monadicNames = [];
  top.monadRewritten = baseExpr(^q);
}

aspect production childReference
top::Expr ::= @q::QName
{
  top.merrors := [];
  propagate mDownSubst, mUpSubst;
  top.mtyperep = if isDecorable(q.lookupValue.typeScheme.typerep, top.env)
                 then q.lookupValue.typeScheme.asDecoratedType
                 else q.lookupValue.typeScheme.monoType;
  top.monadicNames = if top.monadicallyUsed
                     then [baseExpr(^q)]
                     else [];
  top.monadRewritten = baseExpr(^q);
}

aspect production lhsReference
top::Expr ::= @q::QName
{
  top.merrors := [];
  propagate mDownSubst, mUpSubst;
  top.mtyperep = q.lookupValue.typeScheme.asDecoratedType;
  top.monadicNames = if top.monadicallyUsed
                     then [baseExpr(^q)]
                     else [];
  top.monadRewritten = baseExpr(^q);
}

aspect production localReference
top::Expr ::= @q::QName
{
  top.merrors := [];
  propagate mDownSubst, mUpSubst;
  top.mtyperep = if isDecorable(q.lookupValue.typeScheme.typerep, top.env)
                 then q.lookupValue.typeScheme.asDecoratedType
                 else q.lookupValue.typeScheme.monoType;
  top.monadicNames = if top.monadicallyUsed
                     then [baseExpr(^q)]
                     else [];
  top.monadRewritten = baseExpr(^q);
}

aspect production nondecLocalReference
top::Expr ::= @q::QName
{
  top.merrors := [];
  propagate mDownSubst, mUpSubst;
  top.mtyperep = q.lookupValue.typeScheme.monoType;
  top.monadicNames = if top.monadicallyUsed
                     then [baseExpr(^q)]
                     else [];
  top.monadRewritten = baseExpr(^q);
}

aspect production forwardReference
top::Expr ::= @q::QName
{
  top.merrors := [];
  propagate mDownSubst, mUpSubst;
  -- An LHS (and thus, forward) is *always* a decorable (nonterminal) type.
  top.mtyperep = q.lookupValue.typeScheme.asDecoratedType;
  top.monadicNames = if top.monadicallyUsed
                     then [baseExpr(^q)]
                     else [];
  top.monadRewritten = baseExpr(^q);
}

aspect production productionReference
top::Expr ::= @q::QName
{
  top.merrors := [];
  propagate mDownSubst, mUpSubst;
  top.mtyperep = q.lookupValue.typeScheme.typerep;
  top.monadicNames = if top.monadicallyUsed
                     then [baseExpr(^q)]
                     else [];
  top.monadRewritten = baseExpr(^q);
}

aspect production functionReference
top::Expr ::= @q::QName
{
  top.merrors := [];
  propagate mDownSubst, mUpSubst;
  top.mtyperep = q.lookupValue.typeScheme.typerep;
  top.monadicNames = if top.monadicallyUsed
                     then [baseExpr(^q)]
                     else [];
  top.monadRewritten = baseExpr(^q);
}

aspect production classMemberReference
top::Expr ::= @q::QName
{
  top.merrors := [];
  propagate mDownSubst, mUpSubst;
  top.mtyperep = q.lookupValue.typeScheme.typerep;
  top.monadicNames = if top.monadicallyUsed
                     then [baseExpr(^q)]
                     else [];
  top.monadRewritten = baseExpr(^q);
}

aspect production globalValueReference
top::Expr ::= @q::QName
{
  top.merrors := [];
  propagate mDownSubst, mUpSubst;
  top.mtyperep = q.lookupValue.typeScheme.typerep;
  top.monadicNames = if top.monadicallyUsed
                     then [baseExpr(^q)]
                     else [];
  top.monadRewritten = baseExpr(^q);
}

aspect production forwardParentReference
top::Expr ::= 'forwardParent'
{
  top.merrors := [];
  propagate mDownSubst, mUpSubst;
  -- An LHS (and thus, forward parent) is *always* a decorable (nonterminal) type.
  top.mtyperep = top.typerep;
  top.monadicNames = [];
  top.monadRewritten = ^top;
}

aspect production application
top::Expr ::= e::Expr '(' es::AppExprs ',' anns::AnnoAppExprs ')'
{
  {-
    We bind e in here because this would otherwise forward to an error.
    Everything else will work out fine by rewriting in a forward other than this.
    Errors might not be great if we have different monads here and in arguments;
       once partial application works, we could just do the whole rewriting here
  -}
  local ne::Expr = ^e;
  ne.mDownSubst = top.mDownSubst;
  ne.env = top.env;
  ne.flowEnv = top.flowEnv;
  ne.config = top.config;
  ne.compiledGrammars = top.compiledGrammars;
  ne.grammarName = top.grammarName;
  ne.frame = top.frame;
  ne.finalSubst = top.finalSubst;
  ne.downSubst = top.downSubst;
  ne.alwaysDecorated = false;
  ne.decSiteVertexInfo = nothing();
  ne.appDecSiteVertexInfo = nothing();
  ne.dispatchFlowDeps = [];
  ne.isRoot = false;
  local nes::AppExprs = ^es;
  nes.mDownSubst = ne.mUpSubst;
  nes.flowEnv = top.flowEnv;
  nes.env = top.env;
  nes.config = top.config;
  nes.compiledGrammars = top.compiledGrammars;
  nes.grammarName = top.grammarName;
  nes.frame = top.frame;
  nes.finalSubst = top.finalSubst;
  nes.downSubst = top.downSubst;
  nes.alwaysDecorated = false;
  nes.decSiteVertexInfo = nothing();
  nes.dispatchFlowDeps = [];
  nes.appProd = nothing();
  nes.appIndexOffset = 0;
  nes.appExprTypereps = reverse(performSubstitution(ne.mtyperep, ne.mUpSubst).inputTypes);
  nes.appExprApplied = ne.unparse;
  nes.monadArgumentsAllowed = acceptableMonadFunction(e);
  local nanns::AnnoAppExprs = ^anns;
  nanns.mDownSubst = nes.mUpSubst;
  nanns.flowEnv = top.flowEnv;
  nanns.env = top.env;
  nanns.config = top.config;
  nanns.compiledGrammars = top.compiledGrammars;
  nanns.grammarName = top.grammarName;
  nanns.frame = top.frame;
  nanns.finalSubst = top.finalSubst;
  nanns.downSubst = top.downSubst;
  nanns.appExprApplied = ne.unparse;
  nanns.remainingFuncAnnotations = anns.remainingFuncAnnotations;
  nanns.funcAnnotations = anns.funcAnnotations;
  nanns.monadArgumentsAllowed = acceptableMonadFunction(e);
  nanns.previousArgs = nes.monadRewritten;

  ne.expectedMonad = top.expectedMonad;
  nes.expectedMonad = top.expectedMonad;
  nanns.expectedMonad = top.expectedMonad;

  top.merrors := ne.merrors ++ nes.merrors ++ nanns.merrors;
  top.mUpSubst = nanns.mUpSubst;

  nondecorated local substTy::Type = performSubstitution(ne.mtyperep, top.mUpSubst);
  local ety :: Type =
        if isMonad(substTy, top.env) &&
           monadsMatch(top.expectedMonad, substTy, top.mDownSubst).fst
        then monadInnerType(substTy)
        else substTy;
  local areMonadicArgs::Boolean =
      !null(nes.monadTypesLocations) || any(map(\ p::(Type, QName, Boolean) -> p.3, nanns.monadAnns));
  local funIsMonadic::Boolean =
      isMonad(substTy, top.env) && monadsMatch(top.expectedMonad, substTy, top.mUpSubst).fst;
  local funResultIsMonad::Boolean =
      isMonad(ety.outputType, top.env) && monadsMatch(ety.outputType, top.expectedMonad, top.mUpSubst).fst;

  --needs to add a monad to the result if there are monadic args or the function is monadic
  top.mtyperep =
      if areMonadicArgs || funIsMonadic
      then if funResultIsMonad
           then ety.outputType
           else monadOfType(top.expectedMonad, ety.outputType)
      else ety.outputType;

  ne.monadicallyUsed = funIsMonadic;
  top.monadicNames = ne.monadicNames ++ nes.monadicNames;

  --whether we need to wrap the ultimate function call in monadRewritten in a Return
  local wrapReturn::Boolean =
        --monadic args  or monadic function and not a monad result
        (areMonadicArgs || funIsMonadic)    &&  !funResultIsMonad;

  {-
    Monad translation creates a lambda to apply to all the arguments
    plus the function (to get fresh names for everything), then
    creates a body that binds all the monadic arguments into the final
    function application.

    For example, if we have
       fun(a, b, c, d)
    where a and d are monadic, then we translate into
       (\a1 a2 a3 a4 f. a1 >>= (\a1. a4 >>= (\a4. f(a1, a2, a3, a4))))(a, b, c, d, fun)
    Reusing ai in the bind for the ith argument simplifies doing the
    application inside all the binds.
  -}
  nondecorated local lambda_fun::Expr =
    buildMonadApplicationLambda(nes.realTypes, nes.monadTypesLocations,
       nanns.monadAnns, top.expectedMonad, ^ety, funIsMonadic, wrapReturn);
  nondecorated local expanded_args::AppExprs =
    snocAppExprs(nanns.fullArgs, ',', presentAppExpr(ne.monadRewritten));
  top.monadRewritten =
      if areMonadicArgs || funIsMonadic
      then applicationExpr(lambda_fun, '(', expanded_args, ')')
      else application(ne.monadRewritten, '(', nes.monadRewritten, ',', nanns.monadRewritten, ')');
}


aspect production functionInvocation
top::Expr ::= @e::Expr @es::AppExprs @anns::AnnoAppExprs
{
  top.merrors := forwardParent.merrors;
  top.mUpSubst = forwardParent.mUpSubst;
  top.mtyperep = forwardParent.mtyperep;
  top.monadRewritten = forwardParent.monadRewritten;

  top.monadicNames = forwardParent.monadicNames;
}

aspect production dispatchApplication
top::Expr ::= @e::Expr @es::AppExprs @anns::AnnoAppExprs
{
  top.merrors := forwardParent.merrors;
  top.mUpSubst = forwardParent.mUpSubst;
  top.mtyperep = forwardParent.mtyperep;
  top.monadRewritten = forwardParent.monadRewritten;

  top.monadicNames = forwardParent.monadicNames;
}

--build the lambda to apply to all the original arguments plus the function
function buildMonadApplicationLambda
Expr ::= realtys::[Type] monadTysLocs::[Pair<Type Integer>] monadAnns::[(Type, QName, Boolean)]
         expectedMonad::Type funType::Type bindFun::Boolean wrapReturn::Boolean
{
  nondecorated local funargs::AppExprs = buildFunArgs(length(realtys));
  nondecorated local funannargs::AnnoAppExprs = buildFunAnnArgs(monadAnns, length(realtys) + 1);
  nondecorated local params::LambdaRHS =
    buildMonadApplicationParams(realtys ++ map(fst, monadAnns), 1,
        if bindFun then monadOfType(^expectedMonad, ^funType) else ^funType);
  local actualMonadAnns::[(Type, Integer)] =
      foldr(\ here::(Type, QName, Boolean) rest::([(Type, Integer)], Integer) ->
              if here.3
              then ((here.1, rest.2)::rest.1, rest.2 - 1)
              else (rest.1, rest.2 -1),
            ([], length(realtys) + length(monadAnns)), monadAnns).1;
  nondecorated local body::Expr =
    buildMonadApplicationBody(monadTysLocs ++ actualMonadAnns, funargs, funannargs,
                              head(monadTysLocs).fst, ^funType, bindFun, wrapReturn);
  return lambdap(params, body);
}
--build the parameters for the lambda applied to all the original arguments plus the function
fun buildMonadApplicationParams LambdaRHS ::= realtys::[Type] currentLoc::Integer funType::Type =
  if null(realtys)
  then lambdaRHSCons(lambdaRHSElemIdTy(name("f"),
                                           '::',
                                           typerepTypeExpr(funType)),
                         lambdaRHSNil())
  else lambdaRHSCons(lambdaRHSElemIdTy(name("a"++toString(currentLoc)),
                                           '::',
                                           typerepTypeExpr(dropDecorated(head(realtys)))),
                         buildMonadApplicationParams(tail(realtys), currentLoc+1, funType));
--build the arguments for the application inside all the binds
--currentIndex is the numerical index of the argument for the name (a<currentIndex>, like a3)
fun buildFunArgs AppExprs ::= currentIndex::Integer =
  if currentIndex == 0
  then emptyAppExprs()
  else snocAppExprs(buildFunArgs(currentIndex - 1), ',',
                    presentAppExpr(baseExpr(qName("a"++toString(currentIndex)))));
--build the annotation arguments for the application inside all the binds
--annotations are the annotations given to the original call
--currentIndex is the numerical index of the argument for the name (a<currentIndex>, like a3)
fun buildFunAnnArgs AnnoAppExprs ::= annotations::[(Type, QName, Boolean)] currentIndex::Integer =
  case annotations of
  | [] -> emptyAnnoAppExprs()
  | (ty, q, _)::rest ->
    snocAnnoAppExprs(buildFunAnnArgs(rest, currentIndex + 1), ',',
       annoExpr(q, '=',
          presentAppExpr(baseExpr(qName("a" ++ toString(currentIndex))))))
  end;
--build the body of the lambda which includes all the binds
function buildMonadApplicationBody
Expr ::= monadTysLocs::[Pair<Type Integer>] funargs::AppExprs annargs::AnnoAppExprs
         monadType::Type funTy::Type bindFun::Boolean wrapReturn::Boolean
{
  nondecorated local sub::Expr =
    buildMonadApplicationBody(tail(monadTysLocs), ^funargs, ^annargs,
       ^monadType, ^funTy, bindFun, wrapReturn);
  nondecorated local argty::Type = head(monadTysLocs).fst;
  nondecorated local bind::Expr = monadBind();
  nondecorated local binding::LambdaRHS =
    lambdaRHSCons(lambdaRHSElemIdTy(name("a"++toString(head(monadTysLocs).snd)),
                                        '::', 
                                        typerepTypeExpr(monadInnerType(argty))),
                      lambdaRHSNil());
  nondecorated local bindargs::AppExprs =
    snocAppExprs(
       oneAppExprs(presentAppExpr(
                      baseExpr(qName("a"++toString(head(monadTysLocs).snd))))),
       ',',
        presentAppExpr(lambdap(binding, sub)));

  nondecorated local step::Expr = applicationExpr(bind, '(', bindargs, ')');

  --the function is always going to be bound into the name "f", so we hard code that here
  nondecorated local baseapp::Expr =
    application(baseExpr(qName("f")),
                '(', ^funargs, ',', ^annargs, ')');
  nondecorated local funapp::Expr =
    if wrapReturn
    then Silver_Expr { $Expr {monadReturn()}($Expr {baseapp}) }
    else baseapp;
  nondecorated local funbinding::LambdaRHS =
    lambdaRHSCons(lambdaRHSElemIdTy(name("f"), '::',
       typerepTypeExpr(^funTy)),
       lambdaRHSNil());
  nondecorated local funbindargs::AppExprs =
    snocAppExprs(
       oneAppExprs(presentAppExpr(
                      baseExpr(qName("f")))),
       ',',
        presentAppExpr(lambdap(funbinding, funapp)));
  nondecorated local fullfun::Expr =
    if bindFun
    then applicationExpr(bind, '(', funbindargs, ')')
    else funapp;

  return if null(monadTysLocs)
         then fullfun
         else step;
}


aspect production partialApplication
top::Expr ::= @e::Expr @es::AppExprs @anns::AnnoAppExprs
{
  top.merrors := error("merrors not defined on partial applications");
  top.mUpSubst = error("mUpSubst not defined on partial applications");

  top.monadicNames = error("monadicNames not defined on partial applications");

  top.mtyperep = error("mtyperep not defined on partial applications, but sholud be in the future");
  top.monadRewritten = error("monadRewritten not defined on partial applications, but should be in the future");
}

aspect production errorApplication
top::Expr ::= @e::Expr @es::AppExprs @anns::AnnoAppExprs
{
  top.merrors := [];

  top.monadicNames = [];

  top.mUpSubst = top.mDownSubst;
  top.mtyperep = errorType();
  top.monadRewritten = ^top;
}

aspect production noteAttachment
top::Expr ::= 'attachNote' note::Expr 'on' e::Expr 'end'
{
  top.merrors := e.merrors;

  e.mDownSubst = top.mDownSubst;
  top.mUpSubst = e.mUpSubst;

  top.mtyperep = e.mtyperep;

  e.monadicallyUsed = top.monadicallyUsed;
  top.monadicNames = e.monadicNames;

  top.monadRewritten = noteAttachment('attachNote', ^note, 'on', e.monadRewritten, 'end');
}

aspect production forwardAccess
top::Expr ::= e::Expr '.' 'forward'
{
  local ne::Expr = ^e;
  ne.downSubst = top.mDownSubst;
  ne.mDownSubst = top.mDownSubst;
  top.mUpSubst = ne.mUpSubst;
  ne.finalSubst = top.finalSubst;
  ne.expectedMonad = top.expectedMonad;
  ne.frame = top.frame;
  ne.grammarName = top.grammarName;
  ne.compiledGrammars = top.compiledGrammars;
  ne.config = top.config;
  ne.env = top.env;
  ne.flowEnv = top.flowEnv;
  ne.decSiteVertexInfo = nothing();
  ne.alwaysDecorated = false;
  ne.appDecSiteVertexInfo = nothing();
  ne.dispatchFlowDeps = [];
  ne.isRoot = false;
  ne.monadicallyUsed = false; --this needs to change when we decorated monadic trees

  --apparently there isn't a downSubst equation normally?
  local res_e::Expr = ^e;
  res_e.downSubst = top.downSubst;
  res_e.finalSubst = top.finalSubst;
  res_e.frame = top.frame;
  res_e.grammarName = top.grammarName;
  res_e.compiledGrammars = top.compiledGrammars;
  res_e.config = top.config;
  res_e.env = top.env;
  res_e.flowEnv = top.flowEnv;
  res_e.decSiteVertexInfo = nothing();
  res_e.alwaysDecorated = false;
  res_e.appDecSiteVertexInfo = nothing();
  res_e.dispatchFlowDeps = [];
  res_e.isRoot = false;
  top.notExplicitAttributes := res_e.notExplicitAttributes;

  top.merrors := ne.errors;
  top.mtyperep = ne.mtyperep;

  top.monadicNames = ne.monadicNames;
  top.monadRewritten = forwardAccess(ne.monadRewritten, '.', 'forward');
}

aspect production errorAccessHandler
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  e.monadicallyUsed = false; --this needs to change when we decorate monadic trees
  top.monadicNames = if top.monadicallyUsed
                     then [access(^e, '.', ^q)] ++ e.monadicNames
                     else e.monadicNames;

  top.merrors := [];
  top.merrors <- case q.attrDcl of
                 | restrictedSynDcl(_, _, _) -> []
                 | restrictedInhDcl(_, _, _) -> []
                 | implicitSynDcl(_, _, _) -> []
                 | implicitInhDcl(_, _, _) -> []
                 | annoDcl(_, _, _) -> []
                 | _ -> [errFromOrigin(top, "Attributes accessed in implicit equations must " ++
                                           "be either implicit or restricted; " ++ q.unparse ++
                                           " is neither")]
                 end;

  --Why do we rewrite here, in an error production?  We can get here from the basic access
  --   production based on normal typechecking failing even though our typechecking will
  --   succeed, and we then need to be able to go back.
  nondecorated local eUnDec::Expr =
    if e.mtyperep.isDecorated
    then Silver_Expr{ silver:core:new($Expr {e.monadRewritten}) }
    else e.monadRewritten;
  nondecorated local noMonad::Expr = access(e.monadRewritten, '.', ^q);
  nondecorated local isEMonad::Expr =
    Silver_Expr {
      $Expr {monadBind()}
      ($Expr {eUnDec},
       (\x::$TypeExpr {typerepTypeExpr(monadInnerType(e.mtyperep))} ->
          $Expr {monadReturn()}
          (x.$QName {qName(q.name)})
       )
      )
    };
  nondecorated local isBothMonad::Expr =
    Silver_Expr {
      $Expr {monadBind()}
      ($Expr {eUnDec},
       (\x::$TypeExpr {typerepTypeExpr(monadInnerType(e.mtyperep))} ->
          (x.$QName {qName(q.name)})
       )
      )
    };
  top.monadRewritten = if isMonad(e.mtyperep, top.env) &&
                          fst(monadsMatch(e.mtyperep, top.expectedMonad, top.mUpSubst))
                       then if isMonad(q.typerep, top.env) &&
                               fst(monadsMatch(q.typerep, top.expectedMonad, top.mUpSubst))
                            then isBothMonad
                            else isEMonad
                       else noMonad;

  top.mtyperep = if isMonad(e.mtyperep, top.env) &&
                    fst(monadsMatch(e.mtyperep, top.expectedMonad, top.mUpSubst))
                 then if isMonad(q.typerep, top.env) &&
                         fst(monadsMatch(q.typerep, top.expectedMonad, top.mUpSubst))
                      then q.typerep
                      else monadOfType(top.expectedMonad, q.typerep)
                 else q.typerep;
  propagate @mDownSubst, @mUpSubst;

  top.notExplicitAttributes <- e.notExplicitAttributes ++
                               if q.found
                               then case q.attrDcl of
                                    | restrictedSynDcl(_, _, _) -> []
                                    | restrictedInhDcl(_, _, _) -> []
                                    | annoDcl(_, _, _) -> []
                                    | _ -> [q]
                                    end
                               else [];
}

aspect production annoAccessHandler
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  e.monadicallyUsed = false; --this needs to change when we decorate monadic trees
  top.monadicNames = if top.monadicallyUsed
                     then [access(^e, '.', ^q)] ++ e.monadicNames
                     else e.monadicNames;

  nondecorated local eUnDec::Expr =
    if e.mtyperep.isDecorated
    then Silver_Expr{ silver:core:new($Expr {e.monadRewritten}) }
    else e.monadRewritten;
  nondecorated local noMonad::Expr = access(e.monadRewritten, '.', ^q);
  nondecorated local isEMonad::Expr =
    Silver_Expr {
      $Expr {monadBind()}
      ($Expr {eUnDec},
       (\x::$TypeExpr {typerepTypeExpr(monadInnerType(e.mtyperep))} ->
          $Expr {monadReturn()}
          (x.$QName {qName(q.name)})
       )
      )
    };
  nondecorated local isBothMonad::Expr =
    Silver_Expr {
      $Expr {monadBind()}
      ($Expr {eUnDec},
       (\x::$TypeExpr {typerepTypeExpr(monadInnerType(e.mtyperep))} ->
          (x.$QName {qName(q.name)})
       )
      )
    };
  top.monadRewritten = if isMonad(e.mtyperep, top.env) &&
                          fst(monadsMatch(e.mtyperep, top.expectedMonad, top.mUpSubst))
                       then if isMonad(q.typerep, top.env) &&
                               fst(monadsMatch(q.typerep, top.expectedMonad, top.mUpSubst))
                            then isBothMonad
                            else isEMonad
                       else noMonad;

  top.mtyperep = if isMonad(e.mtyperep, top.env) &&
                    fst(monadsMatch(e.mtyperep, top.expectedMonad, top.mUpSubst))
                 then if isMonad(q.typerep, top.env) &&
                         fst(monadsMatch(q.typerep, top.expectedMonad, top.mUpSubst))
                      then q.typerep
                      else monadOfType(top.expectedMonad, q.typerep)
                 else q.typerep;

  propagate @mDownSubst, @mUpSubst;
  top.merrors := [];
  {-
    Note that we don't treat annotations as having a plicitness (restricted,
    implicit, explicit) like attributes because they are arguments to a
    constructor like any other argument, only named.  Then they have a different
    character than attributes and plicitness does not make sense for them.
  -}
}

aspect production synDataAccessHandler
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  e.monadicallyUsed = false; --this needs to change when we decorate monadic trees
  top.monadicNames = if top.monadicallyUsed
                     then [access(^e, '.', ^q)] ++ e.monadicNames
                     else e.monadicNames;

  nondecorated local eUnDec::Expr =
    if e.mtyperep.isDecorated
    then Silver_Expr{ silver:core:new($Expr {e.monadRewritten}) }
    else e.monadRewritten;
  nondecorated local noMonad::Expr = access(e.monadRewritten, '.', ^q);
  nondecorated local isEMonad::Expr =
    Silver_Expr {
      $Expr {monadBind()}
      ($Expr {eUnDec},
       (\x::$TypeExpr {typerepTypeExpr(monadInnerType(e.mtyperep))} ->
          $Expr {monadReturn()}
          (x.$QName {qName(q.name)})
       )
      )
    };
  nondecorated local isBothMonad::Expr =
    Silver_Expr {
      $Expr {monadBind()}
      ($Expr {eUnDec},
       (\x::$TypeExpr {typerepTypeExpr(monadInnerType(e.mtyperep))} ->
          (x.$QName {qName(q.name)})
       )
      )
    };
  top.monadRewritten = if isMonad(e.mtyperep, top.env) &&
                          fst(monadsMatch(e.mtyperep, top.expectedMonad, top.mUpSubst))
                       then if isMonad(q.typerep, top.env) &&
                               fst(monadsMatch(q.typerep, top.expectedMonad, top.mUpSubst))
                            then isBothMonad
                            else isEMonad
                       else noMonad;

  top.mtyperep = if isMonad(e.mtyperep, top.env) &&
                    fst(monadsMatch(e.mtyperep, top.expectedMonad, top.mUpSubst))
                 then if isMonad(q.typerep, top.env) &&
                         fst(monadsMatch(q.typerep, top.expectedMonad, top.mUpSubst))
                      then q.typerep
                      else monadOfType(top.expectedMonad, q.typerep)
                 else q.typerep;

  propagate @mDownSubst, @mUpSubst;
  top.merrors := [];
  top.merrors <- case q.attrDcl of
                 | restrictedSynDcl(_, _, _) -> []
                 | restrictedInhDcl(_, _, _) -> []
                 | implicitSynDcl(_, _, _) -> []
                 | implicitInhDcl(_, _, _) -> []
                 | annoDcl(_, _, _) -> []
                 | _ -> [errFromOrigin(top, "Attributes accessed in implicit equations must " ++
                                           "be either implicit or restricted; " ++ q.unparse ++
                                           " is neither")]
                 end;

  top.notExplicitAttributes <- e.notExplicitAttributes ++
                               if q.found
                               then case q.attrDcl of
                                    | restrictedSynDcl(_, _, _) -> []
                                    | restrictedInhDcl(_, _, _) -> []
                                    | annoDcl(_, _, _) -> []
                                    | _ -> [q]
                                    end
                               else [];
}

aspect production terminalAccessHandler
top::Expr ::= @e::Expr @q::QNameAttrOccur
{

  top.merrors := e.merrors;
  propagate @mDownSubst, @mUpSubst;

  e.monadicallyUsed = false; --this needs to change when we decorate monadic trees
  top.monadicNames = if top.monadicallyUsed
                     then [access(^e, '.', ^q)] ++ e.monadicNames
                     else e.monadicNames;

  nondecorated local eUnDec::Expr =
    if e.mtyperep.isDecorated
    then Silver_Expr{ silver:core:new($Expr {e.monadRewritten}) }
    else e.monadRewritten;
  nondecorated local noMonad::Expr = access(e.monadRewritten, '.', ^q);
  nondecorated local isEMonad::Expr =
    Silver_Expr {
      $Expr {monadBind()}
      ($Expr {eUnDec},
       (\x::$TypeExpr {typerepTypeExpr(monadInnerType(e.mtyperep))} ->
          $Expr {monadReturn()}
          (x.$QName {qName(q.name)})
       )
      )
    };
  top.monadRewritten = if isMonad(e.mtyperep, top.env) &&
                          fst(monadsMatch(e.mtyperep, top.expectedMonad, top.mUpSubst))
                       then isEMonad
                       else noMonad;

  top.mtyperep = if isMonad(e.mtyperep, top.env) &&
                    fst(monadsMatch(e.mtyperep, top.expectedMonad, top.mUpSubst))
                 then monadOfType(top.expectedMonad, baseType)
                 else baseType;

  nondecorated local baseType::Type =
    if q.name == "lexeme" || q.name == "filename"
    then stringType()
    else if q.name == "line" || q.name == "column"
    then intType()
    else if q.name == "location"
    then nonterminalType("silver:core:Location", [], true, false)
    else errorType();
}

aspect production synDecoratedAccessHandler
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  e.monadicallyUsed = false; --this needs to change when we decorate monadic trees
  top.monadicNames = if top.monadicallyUsed
                     then [access(^e, '.', ^q)] ++ e.monadicNames
                     else e.monadicNames;

  nondecorated local eUnDec::Expr =
    if e.mtyperep.isDecorated
    then Silver_Expr{ silver:core:new($Expr {e.monadRewritten}) }
    else e.monadRewritten;
  nondecorated local noMonad::Expr = access(e.monadRewritten, '.', ^q);
  nondecorated local isEMonad::Expr =
    Silver_Expr {
      $Expr {monadBind()}
      ($Expr {eUnDec},
       (\x::$TypeExpr {typerepTypeExpr(monadInnerType(e.mtyperep))} ->
          $Expr {monadReturn()}
          (x.$QName {qName(q.name)})
       )
      )
    };
  nondecorated local isBothMonad::Expr =
    Silver_Expr {
      $Expr {monadBind()}
      ($Expr {eUnDec},
       (\x::$TypeExpr {typerepTypeExpr(monadInnerType(e.mtyperep))} ->
          (x.$QName {qName(q.name)})
       )
      )
    };
  top.monadRewritten = if isMonad(e.mtyperep, top.env) &&
                          fst(monadsMatch(e.mtyperep, top.expectedMonad, top.mUpSubst))
                       then if isMonad(q.typerep, top.env) &&
                               fst(monadsMatch(q.typerep, top.expectedMonad, top.mUpSubst))
                            then isBothMonad
                            else isEMonad
                       else noMonad;

  top.mtyperep = if isMonad(e.mtyperep, top.env) &&
                    fst(monadsMatch(e.mtyperep, top.expectedMonad, top.mUpSubst))
                 then if isMonad(q.typerep, top.env) &&
                         fst(monadsMatch(q.typerep, top.expectedMonad, top.mUpSubst))
                      then q.typerep
                      else monadOfType(top.expectedMonad, q.typerep)
                 else q.typerep;

  propagate @mDownSubst, @mUpSubst;
  top.merrors := e.merrors;
  top.merrors <- case q.attrDcl of
                 | restrictedSynDcl(_, _, _) -> []
                 | restrictedInhDcl(_, _, _) -> []
                 | implicitSynDcl(_, _, _) -> []
                 | implicitInhDcl(_, _, _) -> []
                 | annoDcl(_, _, _) -> []
                 | _ -> [errFromOrigin(top, "Attributes accessed in implicit equations must " ++
                                           "be either implicit or restricted; " ++ q.unparse ++
                                           " is neither")]
                 end;

  top.notExplicitAttributes <- e.notExplicitAttributes ++
                               if q.found
                               then case q.attrDcl of
                                    | restrictedSynDcl(_, _, _) -> []
                                    | restrictedInhDcl(_, _, _) -> []
                                    | annoDcl(_, _, _) -> []
                                    | _ -> [q]
                                    end
                               else [];
}

aspect production inhDecoratedAccessHandler
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  e.monadicallyUsed = false; --this needs to change when we decorate monadic trees
  top.monadicNames = if top.monadicallyUsed
                     then [access(^e, '.', ^q)] ++ e.monadicNames
                     else e.monadicNames;

  nondecorated local eUnDec::Expr =
    if e.mtyperep.isDecorated
    then Silver_Expr{ silver:core:new($Expr {e.monadRewritten}) }
    else e.monadRewritten;
  nondecorated local noMonad::Expr = access(e.monadRewritten, '.', ^q);
  nondecorated local isEMonad::Expr =
    Silver_Expr {
      $Expr {monadBind()}
      ($Expr {eUnDec},
       (\x::$TypeExpr {typerepTypeExpr(monadInnerType(e.mtyperep))} ->
          $Expr {monadReturn()}
          (x.$QName {qName(q.name)})
       )
      )
    };
  nondecorated local isBothMonad::Expr =
    Silver_Expr {
      $Expr {monadBind()}
      ($Expr {eUnDec},
       (\x::$TypeExpr {typerepTypeExpr(monadInnerType(e.mtyperep))} ->
          (x.$QName {qName(q.name)})
       )
      )
    };
  top.monadRewritten = if isMonad(e.mtyperep, top.env) &&
                          fst(monadsMatch(e.mtyperep, top.expectedMonad, top.mUpSubst))
                       then if isMonad(q.typerep, top.env) &&
                               fst(monadsMatch(q.typerep, top.expectedMonad, top.mUpSubst))
                            then isBothMonad
                            else isEMonad
                       else noMonad;

  top.mtyperep = if isMonad(e.mtyperep, top.env) &&
                    fst(monadsMatch(e.mtyperep, top.expectedMonad, top.mUpSubst))
                 then if isMonad(q.typerep, top.env) &&
                         fst(monadsMatch(q.typerep, top.expectedMonad, top.mUpSubst))
                      then q.typerep
                      else monadOfType(top.expectedMonad, q.typerep)
                 else q.typerep;

  propagate @mDownSubst, @mUpSubst;
  top.merrors := e.merrors;
  top.merrors <- case q.attrDcl of
                 | restrictedSynDcl(_, _, _) -> []
                 | restrictedInhDcl(_, _, _) -> []
                 | implicitSynDcl(_, _, _) -> []
                 | implicitInhDcl(_, _, _) -> []
                 | annoDcl(_, _, _) -> []
                 | _ -> [errFromOrigin(top, "Attributes accessed in implicit equations must " ++
                                           "be either implicit or restricted; " ++ q.unparse ++
                                           " is neither")]
                 end;

  top.notExplicitAttributes <- e.notExplicitAttributes ++
                               if q.found
                               then case q.attrDcl of
                                    | restrictedSynDcl(_, _, _) -> []
                                    | restrictedInhDcl(_, _, _) -> []
                                    | annoDcl(_, _, _) -> []
                                    | _ -> [q]
                                    end
                               else [];
}

-- TODO: restricted translation attributes?
aspect production transDecoratedAccessHandler
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  e.monadicallyUsed = false; --this needs to change when we decorate monadic trees
  top.monadicNames = if top.monadicallyUsed
                     then [access(^e, '.', ^q)] ++ e.monadicNames
                     else e.monadicNames;

  propagate @mDownSubst, @mUpSubst;
  top.merrors := [];
  top.merrors <- case q.attrDcl of
                 -- TODO: restricted translation attributes?
                 -- | restrictedSynDcl(_, _, _) -> []
                 -- | restrictedInhDcl(_, _, _) -> []
                 | _ -> [errFromOrigin(top, "Attributes accessed in implicit equations must " ++
                                           "be either implicit or restricted; " ++ q.unparse ++
                                           " is neither")]
                 end;

  nondecorated local eUnDec::Expr =
    if e.mtyperep.isDecorated
    then Silver_Expr{ silver:core:new($Expr {e.monadRewritten}) }
    else e.monadRewritten;
  nondecorated local noMonad::Expr = access(e.monadRewritten, '.', ^q);
  nondecorated local isEMonad::Expr =
    Silver_Expr {
      $Expr {monadBind()}
      ($Expr {eUnDec},
       (\x::$TypeExpr {typerepTypeExpr(monadInnerType(e.mtyperep))} ->
          $Expr {monadReturn()}
          (x.$QName {qName(q.name)})
       )
      )
    };
  top.monadRewritten = if isMonad(e.mtyperep, top.env) &&
                          fst(monadsMatch(e.mtyperep, top.expectedMonad, top.mUpSubst))
                       then isEMonad
                       else noMonad;

  top.mtyperep = if isMonad(e.mtyperep, top.env) &&
                    fst(monadsMatch(e.mtyperep, top.expectedMonad, top.mUpSubst))
                 then monadOfType(top.expectedMonad, q.typerep)
                 else q.typerep;

  top.notExplicitAttributes <- e.notExplicitAttributes ++
                               if q.found
                               then case q.attrDcl of
                                    -- TODO: restricted translation attributes?
                                    -- | restrictedSynDcl(_, _, _) -> []
                                    -- | restrictedInhDcl(_, _, _) -> []
                                    | _ -> [q]
                                    end
                               else [];
}

aspect production unknownDclAccessHandler
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  top.monadicNames = [];

   --Why do we rewrite here, in an error production?  We can get here from the basic access
  --   production based on normal typechecking failing even though our typechecking will
  --   succeed, and we then need to be able to go back.
  nondecorated local eUnDec::Expr =
    if e.mtyperep.isDecorated
    then Silver_Expr{ silver:core:new($Expr {e.monadRewritten}) }
    else e.monadRewritten;
  nondecorated local noMonad::Expr = access(e.monadRewritten, '.', ^q);
  nondecorated local isEMonad::Expr =
    Silver_Expr {
      $Expr {monadBind()}
      ($Expr {eUnDec},
       (\x::$TypeExpr {typerepTypeExpr(monadInnerType(e.mtyperep))} ->
          $Expr {monadReturn()}
          (x.$QName {qName(q.name)})
       )
      )
    };
  nondecorated local isBothMonad::Expr =
    Silver_Expr {
      $Expr {monadBind()}
      ($Expr {eUnDec},
       (\x::$TypeExpr {typerepTypeExpr(monadInnerType(e.mtyperep))} ->
          (x.$QName {qName(q.name)})
       )
      )
    };
  top.monadRewritten = if isMonad(e.mtyperep, top.env) &&
                          fst(monadsMatch(e.mtyperep, top.expectedMonad, top.mUpSubst))
                       then if isMonad(q.typerep, top.env) &&
                               fst(monadsMatch(q.typerep, top.expectedMonad, top.mUpSubst))
                            then isBothMonad
                            else isEMonad
                       else noMonad;

  top.mtyperep = if isMonad(e.mtyperep, top.env) &&
                    fst(monadsMatch(e.mtyperep, top.expectedMonad, top.mUpSubst))
                 then if isMonad(q.typerep, top.env) &&
                         fst(monadsMatch(q.typerep, top.expectedMonad, top.mUpSubst))
                      then q.typerep
                      else monadOfType(top.expectedMonad, q.typerep)
                 else q.typerep;

  top.merrors := e.merrors;
  top.merrors <- case q.attrDcl of
                 | restrictedSynDcl(_, _, _) -> []
                 | restrictedInhDcl(_, _, _) -> []
                 | implicitSynDcl(_, _, _) -> []
                 | implicitInhDcl(_, _, _) -> []
                 | annoDcl(_, _, _) -> []
                 | _ -> [errFromOrigin(top, "Attributes accessed in implicit equations must " ++
                                           "be either implicit or restricted; " ++ q.unparse ++
                                           " is neither")]
                 end;
  propagate @mDownSubst, @mUpSubst;

  top.notExplicitAttributes <- e.notExplicitAttributes ++
                               if q.found
                               then case q.attrDcl of
                                    | restrictedSynDcl(_, _, _) -> []
                                    | restrictedInhDcl(_, _, _) -> []
                                    | annoDcl(_, _, _) -> []
                                    | _ -> [q]
                                    end
                               else [];
}

aspect production inhUndecoratedAccessErrorHandler
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  e.monadicallyUsed = false; --this needs to change when we decorate monadic trees
  top.monadicNames = if top.monadicallyUsed
                     then [access(^e, '.', ^q)] ++ e.monadicNames
                     else e.monadicNames;

  propagate @mDownSubst, @mUpSubst;
  top.merrors := [];
  top.merrors <- case q.attrDcl of
                 -- TODO: restricted translation attributes?
                 -- | restrictedSynDcl(_, _, _) -> []
                 -- | restrictedInhDcl(_, _, _) -> []
                 | _ -> [errFromOrigin(top, "Attributes accessed in implicit equations must " ++
                                           "be either implicit or restricted; " ++ q.unparse ++
                                           " is neither")]
                 end;

  --Why do we rewrite here, in an error production?  We can get here from the basic access
  --   production based on normal typechecking failing even though our typechecking will
  --   succeed, and we then need to be able to go back.
  nondecorated local eUnDec::Expr =
    if e.mtyperep.isDecorated
    then Silver_Expr{ silver:core:new($Expr {e.monadRewritten}) }
    else e.monadRewritten;
  nondecorated local noMonad::Expr = access(e.monadRewritten, '.', ^q);
  nondecorated local isEMonad::Expr =
    Silver_Expr {
      $Expr {monadBind()}
      ($Expr {eUnDec},
       (\x::$TypeExpr {typerepTypeExpr(monadInnerType(e.mtyperep))} ->
          $Expr {monadReturn()}
          (x.$QName {qName(q.name)})
       )
      )
    };
  top.monadRewritten = if isMonad(e.mtyperep, top.env) &&
                          fst(monadsMatch(e.mtyperep, top.expectedMonad, top.mUpSubst))
                       then isEMonad
                       else noMonad;

  top.mtyperep = if isMonad(e.mtyperep, top.env) &&
                    fst(monadsMatch(e.mtyperep, top.expectedMonad, top.mUpSubst))
                 then monadOfType(top.expectedMonad, q.typerep)
                 else q.typerep;

  top.notExplicitAttributes <- e.notExplicitAttributes ++
                               if q.found
                               then [q]
                               else [];
}

-- TODO: restricted translation attributes?
aspect production transUndecoratedAccessErrorHandler
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  e.monadicallyUsed = false; --this needs to change when we decorate monadic trees
  top.monadicNames = if top.monadicallyUsed
                     then [access(^e, '.', ^q)] ++ e.monadicNames
                     else e.monadicNames;

  propagate @mDownSubst, @mUpSubst;
  top.merrors := [];
  top.merrors <- case q.attrDcl of
                 -- TODO: restricted translation attributes?
                 -- | restrictedSynDcl(_, _, _) -> []
                 -- | restrictedInhDcl(_, _, _) -> []
                 | _ -> [errFromOrigin(top, "Attributes accessed in implicit equations must " ++
                                           "be either implicit or restricted; " ++ q.unparse ++
                                           " is neither")]
                 end;

  --Why do we rewrite here, in an error production?  We can get here from the basic access
  --   production based on normal typechecking failing even though our typechecking will
  --   succeed, and we then need to be able to go back.
  nondecorated local eUnDec::Expr =
    if e.mtyperep.isDecorated
    then Silver_Expr{ silver:core:new($Expr {e.monadRewritten}) }
    else e.monadRewritten;
  nondecorated local noMonad::Expr = access(e.monadRewritten, '.', ^q);
  nondecorated local isEMonad::Expr =
    Silver_Expr {
      $Expr {monadBind()}
      ($Expr {eUnDec},
       (\x::$TypeExpr {typerepTypeExpr(monadInnerType(e.mtyperep))} ->
          $Expr {monadReturn()}
          (x.$QName {qName(q.name)})
       )
      )
    };
  top.monadRewritten = if isMonad(e.mtyperep, top.env) &&
                          fst(monadsMatch(e.mtyperep, top.expectedMonad, top.mUpSubst))
                       then isEMonad
                       else noMonad;

  top.mtyperep = if isMonad(e.mtyperep, top.env) &&
                    fst(monadsMatch(e.mtyperep, top.expectedMonad, top.mUpSubst))
                 then monadOfType(top.expectedMonad, q.typerep)
                 else q.typerep;

  top.notExplicitAttributes <- e.notExplicitAttributes ++
                               if q.found
                               then case q.attrDcl of
                                    -- TODO: restricted translation attributes?
                                    -- | restrictedSynDcl(_, _, _) -> []
                                    -- | restrictedInhDcl(_, _, _) -> []
                                    | _ -> [q]
                                    end
                               else [];
}

aspect production decorateExprWith
top::Expr ::= 'decorate' e::Expr 'with' '{' inh::ExprInhs '}'
{
  {-
    We assume no one is both using monadic stuff and explicitly decorating
    monads, so anything that is a monad gets bound in to have its insides
    decorated.
  -}
  propagate mDownSubst, mUpSubst;
  top.merrors := e.merrors;

  e.monadicallyUsed = if isMonad(e.mtyperep, top.env) && monadsMatch(e.mtyperep, top.expectedMonad, top.mDownSubst).fst
                      then true
                      else false;
  top.monadicNames = e.monadicNames ++ inh.monadicNames;

  top.mtyperep = if isMonad(e.mtyperep, top.env) && monadsMatch(e.mtyperep, top.expectedMonad, top.mDownSubst).fst
                 then monadOfType(
                   e.mtyperep,
                   decoratedType(
                     performSubstitution(monadInnerType(e.mtyperep), e.mUpSubst),
                     inhSetType(sort(nub(inh.suppliedInhs)))))
                 else decoratedType(performSubstitution(e.mtyperep, e.mUpSubst), inhSetType(sort(nub(inh.suppliedInhs))));

  local newname::String = "__sv_bind_" ++ toString(genInt());
  nondecorated local params::LambdaRHS =
    lambdaRHSCons(lambdaRHSElemIdTy(name(newname),
                                        '::',
                                        typerepTypeExpr(monadInnerType(e.mtyperep))),
                      lambdaRHSNil());
  nondecorated local eUnDec::Expr =
    if e.mtyperep.isDecorated
    then Silver_Expr {new($Expr {e.monadRewritten})}
    else e.monadRewritten;
  top.monadRewritten =
     if isMonad(e.mtyperep, top.env) && monadsMatch(e.mtyperep, top.expectedMonad, top.mDownSubst).fst
     then Silver_Expr {
            $Expr{monadBind()}
              ($Expr{eUnDec},
               $Expr{lambdap(params,
                      Silver_Expr{
                        $Expr{monadReturn()}
                        ($Expr{decorateExprWith('decorate',
                               baseExpr(qName(newname)),
                               'with', '{', inh.monadRewritten, '}')})
                      })})
          }
     else decorateExprWith('decorate', e.monadRewritten, 'with',
                           '{', inh.monadRewritten, '}');
}

attribute monadRewritten<ExprInhs>, merrors, mDownSubst, mUpSubst, monadicNames, expectedMonad occurs on ExprInhs;
attribute monadRewritten<ExprInh>, merrors, mDownSubst, mUpSubst, monadicNames, expectedMonad occurs on ExprInh;

propagate mDownSubst, mUpSubst, expectedMonad on ExprInhs, ExprInh;

aspect production exprInhsEmpty
top::ExprInhs ::= 
{
  top.merrors := [];

  top.monadicNames = [];

  top.monadRewritten = exprInhsEmpty();
}

aspect production exprInhsOne
top::ExprInhs ::= lhs::ExprInh
{
  top.merrors := lhs.merrors;

  top.monadicNames = lhs.monadicNames;

  top.monadRewritten = exprInhsOne(lhs.monadRewritten);
}

aspect production exprInhsCons
top::ExprInhs ::= lhs::ExprInh inh::ExprInhs
{
  top.merrors := lhs.merrors ++ inh.merrors;

  top.monadicNames = lhs.monadicNames ++ inh.monadicNames;

  top.monadRewritten = exprInhsCons(lhs.monadRewritten, inh.monadRewritten);
}

aspect production exprInh
top::ExprInh ::= lhs::ExprLHSExpr '=' e::Expr ';'
{
  top.merrors := e.merrors;

  e.monadicallyUsed = false;
  top.monadicNames = e.monadicNames;

  top.monadRewritten = exprInh(^lhs, '=', e.monadRewritten, ';');
}


aspect production decorationSiteExpr
top::Expr ::= '@' e::Expr
{
  top.mtyperep = e.mtyperep.decoratedType;
  top.merrors := e.merrors;
  top.monadicNames = e.monadicNames;
  top.monadRewritten = decorationSiteExpr('@', e.monadRewritten);
  e.monadicallyUsed = false;

  local attribute errCheck1 :: TypeCheck; errCheck1.finalSubst = top.finalSubst;
  e.mDownSubst = top.mDownSubst;
  errCheck1.downSubst = e.mUpSubst;
  top.mUpSubst = errCheck1.upSubst;
  errCheck1 = check(e.typerep, decoratedType(freshType(), inhSetType([])));
  top.merrors <-
       if errCheck1.typeerror
       then [errFromOrigin(top, "Operand to @ must be a reference with no inherited attributes.  Instead it is of type " ++ errCheck1.leftpp)]
       else [];
}

aspect production trueConst
top::Expr ::= 'true'
{
  propagate mDownSubst, mUpSubst;
  top.mtyperep = boolType();
  top.merrors := [];
  top.monadicNames = [];
  top.monadRewritten = trueConst('true');
}

aspect production falseConst
top::Expr ::= 'false'
{
  propagate mDownSubst, mUpSubst;
  top.mtyperep = boolType();
  top.merrors := [];
  top.monadicNames = [];
  top.monadRewritten = falseConst('false');
}

-- These aspects for and/or provide special-case monadic short circuit evaluation semantics,
-- if the second operand corresponds to failure.
aspect production and
top::Expr ::= e1::Expr '&&' e2::Expr
{
  -- TODO: Need to re-decorate here, to avoid hidden transitive deps flow analysis issue.
  -- See https://github.com/melt-umn/silver/issues/812
  forward ne1 = ^e1;
  forward ne2 = ^e2;

  top.merrors := ne1.merrors ++ ne2.merrors;
  top.merrors <-
      if isMonad(ne1.mtyperep, top.env)
      then if monadsMatch(top.expectedMonad, ne1.mtyperep, top.mDownSubst).fst
           then []
           else [errFromOrigin(top, "Can only use " ++ monadToString(top.expectedMonad) ++
                           " implicitly in this '&&', not " ++ monadToString(ne1.mtyperep))]
      else [];
  top.merrors <-
      if isMonad(ne2.mtyperep, top.env)
      then if monadsMatch(top.expectedMonad, ne2.mtyperep, top.mDownSubst).fst
           then []
           else [errFromOrigin(top, "Can only use " ++ monadToString(top.expectedMonad) ++
                           " implicitly in this '&&', not " ++ monadToString(ne2.mtyperep))]
      else [];

  local ec1::TypeCheck = if isMonad(ne1.mtyperep, top.env) && monadsMatch(top.expectedMonad, ne1.mtyperep, top.mDownSubst).fst
                         then check(monadInnerType(ne1.mtyperep), boolType())
                         else check(ne1.mtyperep, boolType());
  local ec2::TypeCheck = if isMonad(ne2.mtyperep, top.env) && monadsMatch(top.expectedMonad, ne2.mtyperep, top.mDownSubst).fst
                         then check(monadInnerType(ne2.mtyperep), boolType())
                         else check(ne2.mtyperep, boolType());
  ec1.finalSubst = top.finalSubst;
  ec2.finalSubst = top.finalSubst;
  ne1.mDownSubst = top.mDownSubst;
  ne2.mDownSubst = ne1.mUpSubst;
  ec1.downSubst = ne2.mUpSubst;
  ec2.downSubst = ec1.upSubst;
  top.mUpSubst = ec2.upSubst;
  top.mtyperep = if isMonad(ne1.mtyperep, top.env) && monadsMatch(top.expectedMonad, ne1.mtyperep, top.mDownSubst).fst
                 then ne1.mtyperep --assume it will be well-typed
                 else if isMonad(ne2.mtyperep, top.env) && monadsMatch(top.expectedMonad, ne2.mtyperep, top.mDownSubst).fst
                      then ne2.mtyperep
                      else boolType();

  ne1.monadicallyUsed = isMonad(ne1.mtyperep, top.env) && monadsMatch(top.expectedMonad, ne1.mtyperep, top.mDownSubst).fst;
  ne2.monadicallyUsed = isMonad(ne2.mtyperep, top.env) && monadsMatch(top.expectedMonad, ne2.mtyperep, top.mDownSubst).fst;
  top.monadicNames = ne1.monadicNames ++ ne2.monadicNames;

  nondecorated local e1UnDec::Expr =
    if ne1.mtyperep.isDecorated
    then Silver_Expr {silver:core:new( $Expr {ne1.monadRewritten})}
    else ne1.monadRewritten;
  nondecorated local e2UnDec::Expr =
    if ne2.mtyperep.isDecorated
    then Silver_Expr {silver:core:new( $Expr {ne2.monadRewritten})}
    else ne2.monadRewritten;
  --e1 >>= ( (\x y -> if x then y else Return(false))(_, e2) )
  nondecorated local bindBoth::Expr =
    Silver_Expr {
      $Expr {monadBind()}
      ($Expr {e1UnDec},
       (\x::$TypeExpr {typerepTypeExpr(monadInnerType(ne2.mtyperep))}
         y::$TypeExpr {typerepTypeExpr(dropDecorated(ne2.mtyperep))} ->
          if x then y else $Expr {monadReturn()}(false)) (_, $Expr {e2UnDec}))
    };
  --e1 >>= ( (\x y -> Return(x && y))(_, e2) )
  nondecorated local bind1::Expr =
    Silver_Expr {
      $Expr {monadBind()}
      ($Expr {e1UnDec},
       (\x::$TypeExpr {typerepTypeExpr(monadInnerType(ne1.mtyperep))}
         y::$TypeExpr {typerepTypeExpr(dropDecorated(ne2.mtyperep))} ->
        $Expr {monadReturn()}
        (x && y))(_, $Expr {e2UnDec}))
    };
  --if e1 then e2 else Return(false)
  nondecorated local bind2::Expr =
    Silver_Expr {
      if $Expr {e1UnDec} then $Expr {e2UnDec} else $Expr {monadReturn()}(false)
    };
  top.monadRewritten = if isMonad(ne1.mtyperep, top.env) && monadsMatch(top.expectedMonad, ne1.mtyperep, top.mDownSubst).fst
                       then if isMonad(ne2.mtyperep, top.env) && monadsMatch(top.expectedMonad, ne2.mtyperep, top.mDownSubst).fst
                            then bindBoth
                            else bind1
                       else if isMonad(ne2.mtyperep, top.env) && monadsMatch(top.expectedMonad, ne2.mtyperep, top.mDownSubst).fst
                            then bind2
                            else and(ne1.monadRewritten, '&&', ne2.monadRewritten);
}

aspect production or
top::Expr ::= e1::Expr '||' e2::Expr
{
  -- TODO: Need to re-decorate here, to avoid hidden transitive deps flow analysis issue.
  -- See https://github.com/melt-umn/silver/issues/812
  forward ne1 = ^e1;
  forward ne2 = ^e2;

  top.merrors := ne1.merrors ++ ne2.merrors;
  top.merrors <-
      if isMonad(ne1.mtyperep, top.env)
      then if monadsMatch(top.expectedMonad, ne1.mtyperep, top.mDownSubst).fst
           then []
           else [errFromOrigin(top, "Can only use " ++ monadToString(top.expectedMonad) ++
                           " implicitly in this '||', not " ++ monadToString(ne1.mtyperep))]
      else [];
  top.merrors <-
      if isMonad(ne2.mtyperep, top.env)
      then if monadsMatch(top.expectedMonad, ne2.mtyperep, top.mDownSubst).fst
           then []
           else [errFromOrigin(top, "Can only use " ++ monadToString(top.expectedMonad) ++
                           " implicitly in this '||', not " ++ monadToString(ne2.mtyperep))]
      else [];

  local ec1::TypeCheck = if isMonad(ne1.mtyperep, top.env) && monadsMatch(top.expectedMonad, ne1.mtyperep, top.mDownSubst).fst
                         then check(monadInnerType(ne1.mtyperep), boolType())
                         else check(ne1.mtyperep, boolType());
  local ec2::TypeCheck = if isMonad(ne2.mtyperep, top.env) && monadsMatch(top.expectedMonad, ne2.mtyperep, top.mDownSubst).fst
                         then check(monadInnerType(ne2.mtyperep), boolType())
                         else check(ne2.mtyperep, boolType());
  ec1.finalSubst = top.finalSubst;
  ec2.finalSubst = top.finalSubst;
  ne1.mDownSubst = top.mDownSubst;
  ne2.mDownSubst = ne1.mUpSubst;
  ec1.downSubst = ne2.mUpSubst;
  ec2.downSubst = ec1.upSubst;
  top.mUpSubst = ec2.upSubst;
  top.mtyperep = if isMonad(ne1.mtyperep, top.env) && monadsMatch(top.expectedMonad, ne1.mtyperep, top.mDownSubst).fst
                then ne1.mtyperep --assume it will be well-typed
                else if isMonad(ne2.mtyperep, top.env) && monadsMatch(top.expectedMonad, ne2.mtyperep, top.mDownSubst).fst
                     then ne2.mtyperep
                     else boolType();

  ne1.monadicallyUsed = isMonad(ne1.mtyperep, top.env) && monadsMatch(top.expectedMonad, ne1.mtyperep, top.mDownSubst).fst;
  ne2.monadicallyUsed = isMonad(ne2.mtyperep, top.env) && monadsMatch(top.expectedMonad, ne2.mtyperep, top.mDownSubst).fst;
  top.monadicNames = ne1.monadicNames ++ ne2.monadicNames;

  nondecorated local e1UnDec::Expr =
    if ne1.mtyperep.isDecorated
    then Silver_Expr {silver:core:new( $Expr {ne1.monadRewritten})}
    else ne1.monadRewritten;
  nondecorated local e2UnDec::Expr =
    if ne2.mtyperep.isDecorated
    then Silver_Expr {silver:core:new( $Expr {ne2.monadRewritten})}
    else ne2.monadRewritten;
  --e1 >>= ( (\x y -> if x then Return(true) else y)(_, e2) )
  nondecorated local bindBoth::Expr =
    Silver_Expr {
      $Expr {monadBind()}
      ($Expr {e1UnDec},
       (\x::$TypeExpr {typerepTypeExpr(monadInnerType(ne2.mtyperep))}
         y::$TypeExpr {typerepTypeExpr(dropDecorated(ne2.mtyperep))} ->
          if x then $Expr {monadReturn()}(true) else y) (_, $Expr {e2UnDec}))
    };
  --e1 >>= ( (\x y -> Return(x || y))(_, e2) )
  nondecorated local bind1::Expr =
    Silver_Expr {
      $Expr {monadBind()}
      ($Expr {e1UnDec},
       (\x::$TypeExpr {typerepTypeExpr(monadInnerType(ne1.mtyperep))}
         y::$TypeExpr {typerepTypeExpr(dropDecorated(ne2.mtyperep))} ->
        $Expr {monadReturn()}
        (x || y))(_, $Expr {e2UnDec}))
    };
  --if e1 then Return(true) else e2
  nondecorated local bind2::Expr =
    Silver_Expr {
      if $Expr {e1UnDec} then $Expr {monadReturn()}(true) else $Expr {e2UnDec}
    };
  top.monadRewritten = if isMonad(ne1.mtyperep, top.env) && monadsMatch(top.expectedMonad, ne1.mtyperep, top.mDownSubst).fst
                       then if isMonad(ne2.mtyperep, top.env) && monadsMatch(top.expectedMonad, ne2.mtyperep, top.mDownSubst).fst
                            then bindBoth
                            else bind1
                       else if isMonad(ne2.mtyperep, top.env) && monadsMatch(top.expectedMonad, ne2.mtyperep, top.mDownSubst).fst
                            then bind2
                            else or(ne1.monadRewritten, '||', ne2.monadRewritten);
}

concrete production ifThen
top::Expr ::= 'if' e1::Expr 'then' e2::Expr 'end' --this is easier than anything else to do
{
  top.unparse = "if " ++ e1.unparse  ++ " then " ++ e2.unparse ++ " end";
  propagate config, grammarName, compiledGrammars, frame, env, flowEnv, finalSubst;

  top.merrors <-
      if isMonad(e1.mtyperep, top.env) && monadsMatch(top.expectedMonad, e1.mtyperep, top.mDownSubst).fst
      then if monadsMatch(top.expectedMonad, e1.mtyperep, top.mDownSubst).fst
           then []
           else [errFromOrigin(top, "Can only use " ++ monadToString(top.expectedMonad) ++
                           " implicitly in this 'if-then', not " ++ monadToString(e1.mtyperep))]
      else [];
  top.merrors <-
      if isMonadFail(top.expectedMonad, top.env)
      then []
      else [errFromOrigin(top, monadToString(top.expectedMonad) ++
                " is not an instance of MonadFail and cannot be used with if-then")];

  local ec::TypeCheck = if isMonad(e1.mtyperep, top.env) && monadsMatch(top.expectedMonad, e1.mtyperep, top.mDownSubst).fst
                        then check(monadInnerType(e1.mtyperep), boolType())
                        else check(e1.mtyperep, boolType());
  ec.finalSubst = top.finalSubst;
  e1.mDownSubst = top.mDownSubst;
  e2.mDownSubst = e1.mUpSubst;
  ec.downSubst = e2.mUpSubst;
  top.mUpSubst = ec.upSubst;

  e1.downSubst = top.downSubst;
  e2.downSubst = e1.upSubst;
  top.upSubst = e2.upSubst;

  top.mtyperep = if isMonad(e2.mtyperep, top.env) && monadsMatch(top.expectedMonad, e2.mtyperep, top.mDownSubst).fst
                 then e2.mtyperep
                 else if isMonad(e1.mtyperep, top.env) && monadsMatch(top.expectedMonad, e1.mtyperep, top.mDownSubst).fst
                      then monadOfType(e1.mtyperep, e2.mtyperep)
                      else monadOfType(top.expectedMonad, e2.mtyperep);

  e1.monadicallyUsed = isMonad(e1.mtyperep, top.env) && monadsMatch(top.expectedMonad, e1.mtyperep, top.mDownSubst).fst;
  e2.monadicallyUsed = false;
  top.monadicNames = e1.monadicNames ++ e2.monadicNames;

  {- TODO: Is this equation still needed with sharing?  It is now a flow error:
  e2.expectedMonad = if isMonad(e1.mtyperep, top.env) && monadsMatch(top.expectedMonad, e1.mtyperep, top.mDownSubst).fst
                     then e1.mtyperep
                     else top.expectedMonad;
  -}
  
  e2.decSiteVertexInfo = nothing();
  e2.alwaysDecorated = false;
  e2.isRoot = false;

  forwards to ifThenElse('if', @e1, 'then', @e2, 'else', monadFail());
}

aspect production ifThenElse
top::Expr ::= 'if' e1::Expr 'then' e2::Expr 'else' e3::Expr
{
  top.merrors := e1.merrors ++ e2.merrors ++ e3.merrors;
  top.merrors <-
      if isMonad(e1.mtyperep, top.env)
      then if monadsMatch(top.expectedMonad, e1.mtyperep, top.mDownSubst).fst
           then []
           else [errFromOrigin(top, "Can only use " ++ monadToString(top.expectedMonad) ++
                           " implicitly in this 'if-then-els', not " ++ monadToString(e1.mtyperep))]
      else [];

  local ec1::TypeCheck = if isMonad(e1.mtyperep, top.env) && monadsMatch(top.expectedMonad, e1.mtyperep, top.mDownSubst).fst
                         then check(monadInnerType(e1.mtyperep), boolType())
                         else check(e1.mtyperep, boolType());
  local ec2::TypeCheck = if isMonad(e3.mtyperep, top.env) && monadsMatch(top.expectedMonad, e3.mtyperep, top.mDownSubst).fst
                        then if isMonad(e2.mtyperep, top.env) && monadsMatch(top.expectedMonad, e2.mtyperep, top.mDownSubst).fst
                             then check(e3.mtyperep, e2.mtyperep)
                             else check(monadInnerType(e3.mtyperep), e2.mtyperep)
                        else if isMonad(e2.mtyperep, top.env) && monadsMatch(top.expectedMonad, e2.mtyperep, top.mDownSubst).fst
                             then check(e3.mtyperep, monadInnerType(e2.mtyperep))
                             else check(e3.mtyperep, e2.mtyperep);
  ec1.finalSubst = top.finalSubst;
  ec2.finalSubst = top.finalSubst;
  e1.mDownSubst = top.mDownSubst;
  e2.mDownSubst = e1.mUpSubst;
  e3.mDownSubst = e2.mUpSubst;
  ec1.downSubst = e3.mUpSubst;
  ec2.downSubst = ec1.upSubst;
  top.mUpSubst = ec2.upSubst;

  top.mtyperep = if isMonad(e1.mtyperep, top.env) && monadsMatch(top.expectedMonad, e1.mtyperep, top.mDownSubst).fst
                then if isMonad(e2.mtyperep, top.env) && monadsMatch(top.expectedMonad, e2.mtyperep, top.mDownSubst).fst
                     then e2.mtyperep
                     else if isMonad(e3.mtyperep, top.env) && monadsMatch(top.expectedMonad, e3.mtyperep, top.mDownSubst).fst
                          then e3.mtyperep
                          else monadOfType(top.expectedMonad, e3.mtyperep)
                else if isMonad(e2.mtyperep, top.env) && monadsMatch(top.expectedMonad, e2.mtyperep, top.mDownSubst).fst
                     then e2.mtyperep
                     else e3.mtyperep;

  e1.monadicallyUsed = isMonad(e1.mtyperep, top.env) && monadsMatch(top.expectedMonad, e1.mtyperep, top.mDownSubst).fst;
  e2.monadicallyUsed = false;
  e3.monadicallyUsed = false;
  top.monadicNames = e1.monadicNames ++ e2.monadicNames ++ e3.monadicNames;

  --To deal with the case where one type or the other might be "generic" (e.g. Maybe<a>),
  --   we want to do substitution on the types before putting them into the monadRewritten
  nondecorated local e2Type::Type = performSubstitution(e2.mtyperep, top.finalSubst);
  nondecorated local e3Type::Type = performSubstitution(e3.mtyperep, top.finalSubst);
  --
  nondecorated local e1UnDec::Expr =
    if e1.mtyperep.isDecorated
    then Silver_Expr {silver:core:new($Expr {e1.monadRewritten})}
    else e1.monadRewritten;
  --We assume that if e2 or e3 are monads, they are the same as e1 if that is a
  --   monad and we don't allow monads to become nested.
  nondecorated local cMonad::Expr =
    Silver_Expr {
      $Expr {monadBind()}
      ($Expr {e1UnDec},
       (\c::Boolean
         x::$TypeExpr {typerepTypeExpr(dropDecorated(e2Type))}
         y::$TypeExpr {typerepTypeExpr(dropDecorated(e3Type))} ->
         --x::$TypeExpr {typerepTypeExpr(e2Type)}
         --y::$TypeExpr {typerepTypeExpr(e3Type)} ->
         if c
         then $Expr { if isMonad(e2.mtyperep, top.env)
                      then Silver_Expr {x}
                      else Silver_Expr {$Expr {monadReturn()}(x)} }
         else $Expr { if isMonad(e3.mtyperep, top.env)
                      then Silver_Expr {y}
                      else Silver_Expr {$Expr {monadReturn()}(y)} })
       (_, $Expr {e2.monadRewritten}, $Expr {e3.monadRewritten}))
    };
  nondecorated local cBool::Expr =
    Silver_Expr {
      if $Expr {e1.monadRewritten}
      then $Expr {if isMonad(e2.mtyperep, top.env)
                  then e2.monadRewritten
                  else if isMonad(e3.mtyperep, top.env)
                       then Silver_Expr { $Expr {monadReturn()}($Expr {e2.monadRewritten}) }
                       else e2.monadRewritten}
      else $Expr {if isMonad(e3.mtyperep, top.env)
                  then e3.monadRewritten
                  else if isMonad(e2.mtyperep, top.env)
                       then Silver_Expr { $Expr {monadReturn()}($Expr {e3.monadRewritten}) }
                       else e3.monadRewritten}
    };
  top.monadRewritten = if isMonad(e1.mtyperep, top.env)
                       then cMonad
                       else cBool;
} 

aspect production intConst
top::Expr ::= i::Int_t
{
  top.merrors := [];
  propagate mDownSubst, mUpSubst;
  top.mtyperep = intType();
  top.monadicNames = [];
  top.monadRewritten = intConst(i);
}

aspect production floatConst
top::Expr ::= f::Float_t
{
  top.merrors := [];
  propagate mDownSubst, mUpSubst;
  top.mtyperep = floatType();
  top.monadicNames = [];
  top.monadRewritten = floatConst(f);
} 

aspect production terminalConstructor
top::Expr ::= 'terminal' '(' t::TypeExpr ',' es::Expr ',' el::Expr ')'
{
  es.mDownSubst = top.mDownSubst;
  el.mDownSubst = es.mUpSubst;
  top.merrors := es.merrors ++ el.merrors;
  top.mUpSubst = el.mUpSubst;
  top.mtyperep =
     if ( isMonad(es.mtyperep, top.env) && monadsMatch(es.mtyperep, top.expectedMonad, top.mUpSubst).fst ) ||
        ( isMonad(el.mtyperep, top.env) && monadsMatch(el.mtyperep, top.expectedMonad, top.mUpSubst).fst )
     then monadOfType(top.expectedMonad, t.typerep)
     else t.typerep;
  top.monadicNames = [];

  nondecorated local bind::Expr = monadBind();
  nondecorated local ret::Expr = monadReturn();
  nondecorated local esty::TypeExpr =
    typerepTypeExpr(if isMonad(es.mtyperep, top.env) then es.mtyperep
                    else monadInnerType(es.mtyperep));
  nondecorated local elty::TypeExpr =
    typerepTypeExpr(if isMonad(es.mtyperep, top.env) then es.mtyperep
                    else monadInnerType(es.mtyperep));
  nondecorated local bindes::Expr =
    Silver_Expr {
      $Expr {bind}
      ($Expr {es.monadRewritten},
       (\x::$TypeExpr {esty}
         y::$TypeExpr {elty} ->
            $Expr {ret}
            (terminal($TypeExpr {^t}, x, y))) (_, $Expr {el.monadRewritten}))
    };
  nondecorated local bindel::Expr =
    Silver_Expr {
      $Expr {bind}
      ($Expr {el.monadRewritten},
       (\x::$TypeExpr {esty}
         y::$TypeExpr {elty} ->
            $Expr {ret}
            (terminal($TypeExpr {^t}, x, y))) ($Expr {es.monadRewritten}, _))
    };
  nondecorated local bindBoth::Expr =
    Silver_Expr {
      $Expr {bind}
      ($Expr {es.monadRewritten},
       (\x::$TypeExpr {elty}
         y::$TypeExpr {typerepTypeExpr(es.mtyperep)} ->
          $Expr {bind}
          (y,
           \z::$TypeExpr {elty} ->
            $Expr {ret}
            (terminal($TypeExpr {^t}, x, z))) (_, $Expr {el.monadRewritten})))
    };
  top.monadRewritten =
      if isMonad(es.mtyperep, top.env) && monadsMatch(es.mtyperep, top.expectedMonad, top.mUpSubst).fst
      then if isMonad(el.mtyperep, top.env) && monadsMatch(el.mtyperep, top.expectedMonad, top.mUpSubst).fst
           then bindBoth
           else bindes
      else if isMonad(el.mtyperep, top.env) && monadsMatch(el.mtyperep, top.expectedMonad, top.mUpSubst).fst
           then bindel
           else ^top;
}

aspect production stringConst
top::Expr ::= s::String_t
{
  top.merrors := [];
  propagate mDownSubst, mUpSubst;
  top.mtyperep = stringType();
  top.monadicNames = [];

  top.monadRewritten = stringConst(s);
}


--A list of the locations where arguments are monads used implicitly
synthesized attribute monadTypesLocations::[Pair<Type Integer>] occurs on AppExpr, AppExprs;
--A list of the annotation names, with the final argument being if it is monadic
synthesized attribute monadAnns::[(Type, QName, Boolean)] occurs on AnnoExpr, AnnoAppExprs;
--A list of the actual types of arguments
synthesized attribute realTypes::[Type] occurs on AppExpr, AppExprs, AnnoExpr, AnnoAppExprs;
--The only monad banned from being used as an actual argument
attribute expectedMonad occurs on AppExpr, AppExprs, AnnoExpr, AnnoAppExprs;
propagate expectedMonad on AppExpr, AppExprs, AnnoExpr, AnnoAppExprs;
--Whether we're in a special case where monad arguments are allowed, despite the normal prohibition
inherited attribute monadArgumentsAllowed::Boolean occurs on AppExpr, AppExprs, AnnoExpr, AnnoAppExprs;

--We need to put together all the args for the function giving fresh names
--Pass down the args from the regular args to add the annotated args at the end
inherited attribute previousArgs::AppExprs occurs on AnnoAppExprs;
synthesized attribute fullArgs::AppExprs occurs on AnnoAppExprs;
synthesized attribute rewrittenArg::AppExpr occurs on AnnoExpr;

attribute monadRewritten<AppExpr>, merrors, mDownSubst, mUpSubst occurs on AppExpr;
attribute monadRewritten<AppExprs>, merrors, mDownSubst, mUpSubst occurs on AppExprs;
attribute monadRewritten<AnnoExpr>, merrors, mDownSubst, mUpSubst occurs on AnnoExpr;
attribute monadRewritten<AnnoAppExprs>, merrors, mDownSubst, mUpSubst occurs on AnnoAppExprs;

aspect production missingAppExpr
top::AppExpr ::= '_'
{
  top.merrors := [];
  propagate mDownSubst, mUpSubst;
  top.monadRewritten = missingAppExpr('_');
  top.realTypes = [];
  top.monadTypesLocations = [];
  top.monadicNames = [];
}
aspect production presentAppExpr
top::AppExpr ::= e::Expr
{
  top.merrors := e.merrors;

  top.realTypes = [e.mtyperep];
  top.monadTypesLocations = if isMonadic
                            then [(e.mtyperep, top.appExprIndex+1)]
                            else [];
  e.monadicallyUsed = isMonadic;
  top.monadicNames = e.monadicNames;

  --these have an 'a' at the end of their names because of a bug where local names are not local to their grammars
  local attribute errCheck1a::TypeCheck; errCheck1a.finalSubst = top.mUpSubst;
  local attribute errCheck2a::TypeCheck; errCheck2a.finalSubst = top.mUpSubst;

  e.mDownSubst = top.mDownSubst;
  errCheck1a.downSubst = e.mUpSubst;
  errCheck2a.downSubst = e.mUpSubst;
  top.mUpSubst = if isMonadic
                 then errCheck2a.upSubst
                 else errCheck1a.upSubst;
  --determine whether it appears that this is supposed to take
  --   advantage of implicit monads based on types matching the
  --   expected and being monads
  local isMonadic::Boolean =
           isMonad(e.mtyperep, top.env) &&
           fst(monadsMatch(e.mtyperep, top.expectedMonad, e.mUpSubst)) &&
          !fst(monadsMatch(e.mtyperep, top.appExprTyperep, e.mUpSubst));

  errCheck1a = check(if top.appExprTyperep.isDecorated then e.mtyperep else dropDecorated(e.mtyperep), top.appExprTyperep);
  errCheck2a = check(monadInnerType(e.mtyperep), top.appExprTyperep);
  top.merrors <-
    if isMonadic
    then if !errCheck2a.typeerror
         then []
         else [errFromOrigin(top, "Argument " ++ toString(top.appExprIndex+1) ++ " of function '" ++
                top.appExprApplied ++ "' expected " ++ errCheck1a.rightpp ++
                " or a monad of " ++ errCheck1a.rightpp ++
                " but argument is of type " ++ errCheck1a.leftpp)]
    else
      if !errCheck1a.typeerror
      then []
      else [errFromOrigin(top, "Argument " ++ toString(top.appExprIndex+1) ++ " of function '" ++
                top.appExprApplied ++ "' expected " ++ errCheck1a.rightpp ++
                " or a monad of " ++ errCheck1a.rightpp ++
                " but argument is of type " ++ errCheck1a.leftpp)];
  --Functions are not allowed to take monad-typed arguments
  top.merrors <-
    if fst(monadsMatch(top.appExprTyperep, top.expectedMonad, top.mDownSubst)) && !top.monadArgumentsAllowed
    then [errFromOrigin(top, "Implicit equations may not use functions with " ++
                            "monad-typed arguments, specifically " ++ errCheck2a.rightpp)]
    else [];

  top.monadRewritten = presentAppExpr(e.monadRewritten);
}

propagate monadArgumentsAllowed, mDownSubst, mUpSubst on AppExprs;

aspect production snocAppExprs
top::AppExprs ::= es::AppExprs ',' e::AppExpr
{
  top.merrors := es.merrors ++ e.merrors;

  top.realTypes = es.realTypes ++ e.realTypes;

  top.monadTypesLocations = es.monadTypesLocations ++ e.monadTypesLocations;

  top.monadicNames = es.monadicNames ++ e.monadicNames;

  top.monadRewritten = snocAppExprs(es.monadRewritten, ',', e.monadRewritten);
}
aspect production oneAppExprs
top::AppExprs ::= e::AppExpr
{
  top.merrors := e.merrors;

  top.realTypes = e.realTypes;

  top.monadTypesLocations = e.monadTypesLocations;

  top.monadicNames = e.monadicNames;

  top.monadRewritten = oneAppExprs(e.monadRewritten);
}
aspect production emptyAppExprs
top::AppExprs ::=
{
  top.merrors := [];

  top.realTypes = [];

  top.monadTypesLocations = [];

  top.monadicNames = [];

  top.monadRewritten = emptyAppExprs();
}

propagate monadArgumentsAllowed, mDownSubst, mUpSubst on AnnoAppExprs;

aspect production annoExpr
top::AnnoExpr ::= qn::QName '=' e::AppExpr
{
  top.merrors := e.merrors;

  e.monadArgumentsAllowed = top.monadArgumentsAllowed;

  top.realTypes = e.realTypes;
  --can be at most one entry
  top.monadAnns = case e.monadTypesLocations of
                  | [(ty, _)] -> [(ty, ^qn, true)]
                  | _ -> [(e.appExprTyperep, ^qn, false)]
                  end;
  top.monadicNames = e.monadicNames;

  e.mDownSubst = top.mDownSubst;
  top.mUpSubst = e.mUpSubst;

  top.monadRewritten = annoExpr(^qn, '=', e.monadRewritten);

  top.rewrittenArg = e.monadRewritten;
}

aspect production snocAnnoAppExprs
top::AnnoAppExprs ::= es::AnnoAppExprs ',' e::AnnoExpr
{
  top.merrors := es.merrors ++ e.merrors;

  top.realTypes = es.realTypes ++ e.realTypes;

  top.monadAnns = es.monadAnns ++ e.monadAnns;

  top.monadicNames = es.monadicNames ++ e.monadicNames;

  top.monadRewritten = snocAnnoAppExprs(es.monadRewritten, ',', e.monadRewritten);

  es.previousArgs = top.previousArgs;
  top.fullArgs = snocAppExprs(es.fullArgs, ',', e.rewrittenArg);
}

aspect production oneAnnoAppExprs
top::AnnoAppExprs ::= e::AnnoExpr
{
  top.merrors := e.merrors;

  top.realTypes = e.realTypes;

  top.monadAnns = e.monadAnns;

  top.monadicNames = e.monadicNames;

  top.monadRewritten = oneAnnoAppExprs(e.monadRewritten);

  top.fullArgs = snocAppExprs(top.previousArgs, ',', e.rewrittenArg);
}

aspect production emptyAnnoAppExprs
top::AnnoAppExprs ::=
{
  top.merrors := [];

  top.realTypes = [];

  top.monadAnns = [];

  top.monadicNames = [];

  top.monadRewritten = emptyAnnoAppExprs();

  top.fullArgs = top.previousArgs;
}

--Copper Expressions
aspect production failureTerminalIdExpr
top::Expr ::= 'disambiguationFailure'
{
  top.mUpSubst = top.mDownSubst;
  top.mtyperep = terminalIdType();
  top.monadRewritten = ^top;

  top.monadicNames = [];
}


aspect production lexerClassReference
top::Expr ::= @q::QName
{
  top.mUpSubst = top.mDownSubst;
  top.mtyperep = q.lookupValue.typeScheme.typerep;
  top.monadRewritten = ^top;

  top.monadicNames = [];
}

