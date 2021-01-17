grammar silver:compiler:extension:convenienceaspects;
import silver:core;
import silver:compiler:modification:collection;
import silver:compiler:extension:constructparser;


function extractAgDclFromRuleList
Pair<AGDcl [Message]> ::= rules::[Decorated AbstractMatchRule] aspectTy::TypeExpr aspectAttr::QNameAttrOccur genDef::(ProductionStmt ::= DefLHS QNameAttrOccur Expr Location) location::Location
{

  local makeProdParamTypes::([Type] ::= Decorated QName) = \prod::Decorated QName ->
    case prod.lookupValue.typeScheme.typerep of
    | functionType(_, paramTypes, _) -> paramTypes
    | _ -> error("invalid production type")
    end;

  local makeProdParamsList::([AspectRHSElem] ::= [Name] [Type]) =
    \prodParamNames::[Name] prodParamTypes::[Type] ->
      zipWith(aspectRHSElemFull(_, _, location=location), prodParamNames, prodParamTypes);

  local makeProdParams::(AspectRHS ::= [AspectRHSElem] ) = \prodParamsList::[AspectRHSElem] ->
    foldr(aspectRHSElemCons(_, _, location=location),
          aspectRHSElemNil(location=location),
          prodParamsList);

  local makeQNamesFromNames::([QName] ::= [Name]) = map(qNameId(_, location=location),_);

  local makeParamCaseSubExpr::([Expr] ::= [QName]) = \prodParamNames::[QName] ->
    map(baseExpr(_,location=location),prodParamNames);

  local transformPatternMatchRule::([AbstractMatchRule]::=[Decorated AbstractMatchRule]) =
    \mRuleList::[Decorated AbstractMatchRule] ->
      map((\mRule::Decorated AbstractMatchRule -> case mRule of
         | matchRule(pl,cond,e) -> matchRule(
           (foldr(append, [], (map(\pat::Decorated Pattern -> pat.patternSubPatternList, pl)) ) ),
           cond,
           e,
           location=location)
         | _ -> error("This error indicates possible productions for AbstractMatchRule have expanded.")
         end),
         mRuleList);

  local makeParamsCaseExpr::(Expr ::= [Expr] [Decorated AbstractMatchRule]) =
    \paramsCaseSubExpr::[Expr] mRules::[Decorated AbstractMatchRule] ->
      caseExpr(paramsCaseSubExpr, transformPatternMatchRule(mRules),
        mkStrFunctionInvocation(location, "silver:core:error",
            [stringConst(terminal(String_t,
            "\"Error: pattern match failed at " ++ head(mRules).headPattern.location.unparse ++ "\\n\""), location=head(mRules).headPattern.location)]),
            freshType(), location=head(mRules).headPattern.location);

  local makeAspect::(AGDcl ::= Expr QName AspectRHS) =
    \paramsCaseExpr::Expr prod::QName prodParams::AspectRHS ->
      Silver_AGDcl {
        aspect production $QName{prod}
        top::$TypeExpr{aspectTy} ::= $AspectRHS{prodParams}
        { $ProductionStmt{genDef(defTop,aspectAttr,paramsCaseExpr, paramsCaseExpr.location)}}
      };

  local defTop::DefLHS = concreteDefLHS(qNameId(name("top",location), location=location), location=location);

  return case rules of
    | matchRule(prodAppPattern(name,_,_,_)::_, cond,e) :: _ ->
    -- I wish let bindings were stable...
    pair(
      makeAspect(
        makeParamsCaseExpr(
            makeParamCaseSubExpr(makeQNamesFromNames(head(rules).aspectProdParamsList)),
            rules),
        name,
        makeProdParams(
            makeProdParamsList(
            head(rules).aspectProdParamsList,
            makeProdParamTypes(name)))),
      [])
    | [matchRule(wildcPattern(_)::_,_,e)] ->
      pair(
        Silver_AGDcl {
          aspect default production
          top::$TypeExpr{aspectTy} ::=
          { $ProductionStmt{genDef(defTop,aspectAttr,e,head(rules).location)}}
      },
      [])
    | matchRule(wildcPattern(_)::_,_,e) :: _ ->
      pair(
        Silver_AGDcl {
          aspect default production
          top::$TypeExpr{aspectTy} ::=
          { $ProductionStmt{genDef(defTop,aspectAttr,e,head(rules).location)}}
        },
        [wrn(location, "wildcard patterns after this one are dead code.")])
    | _ ->
      pair(
        error("Patterns in aspect convenience syntax should be productions or wildcards only"),
        [err(location,"Patterns in aspect convenience syntax should be productions or wildcards only")])

    end;
}

synthesized attribute aspectProdParamsList::[Name] occurs on AbstractMatchRule;

abstract production convenienceAspects
top::AGDcl ::= attr::QNameAttrOccur ty::TypeExpr ml::MRuleList makeEquation::(ProductionStmt ::= DefLHS QNameAttrOccur Expr Location)
{
  top.defs := [];
  local groupedMRules::[[Decorated AbstractMatchRule]] =
    map(\rules::[AbstractMatchRule] -> map(
      \rule_::AbstractMatchRule -> decorate rule_ with { env = top.env; grammarName = top.grammarName; }, rules),
        groupMRules(ml.matchRuleList));
  local groupExtractResults::[Pair<AGDcl [Message]>] = map(
    extractAgDclFromRuleList(_,ty,attr,makeEquation,top.location),
    groupedMRules);
  local combinedAspectProds::[AGDcl] = map(fst(_),groupExtractResults);
  local combinedAspectDcls::AGDcls = foldr(
   consAGDcls(_,_,location=top.location),
   nilAGDcls(location=top.location),
   combinedAspectProds);
  local fwrd::AGDcl = makeAppendAGDclOfAGDcls(combinedAspectDcls);

  forwards to unsafeTracePrint(fwrd,fwrd.unparse);

}

concrete productions top::AGDcl
| 'aspect' attr::QNameAttrOccur 'on' ty::TypeExpr 'using' '=' 'of' Opt_Vbar_t ml::MRuleList 'end' ';'
{
  forwards to convenienceAspects(attr,ty,ml, attributeDef(_,'.',_,'=',_,';',location=_), location=top.location);

}
| 'aspect' attr::QNameAttrOccur 'on' ty::TypeExpr 'using' ':=' 'of' Opt_Vbar_t ml::MRuleList 'end' ';'
{
  forwards to convenienceAspects(attr,ty,ml, attrContainsBase(_,'.',_,':=',_,';',location=_), location=top.location);
}
| 'aspect' attr::QNameAttrOccur 'on' ty::TypeExpr 'using' '<-' 'of' Opt_Vbar_t ml::MRuleList 'end' ';'
{
  forwards to convenienceAspects(attr,ty,ml, attrContainsAppend(_,'.',_,'<-',_,';', location=_), location=top.location);
}
| 'aspect' attr::QNameAttrOccur 'on' ty::TypeExpr 'of' Opt_Vbar_t ml::MRuleList 'end' ';'
{
  forwards to convenienceAspects(attr,ty,ml, attributeDef(_,'.',_,'=',_,';',location=_), location=top.location);
}


aspect production matchRule
top::AbstractMatchRule ::= pl::[Decorated Pattern] cond::Maybe<Pair<Expr Maybe<Pattern>>> e::Expr
{
  top.aspectProdParamsList = case pl of
    | prodAppPattern_named(prod, _, ps,_,_,_) :: _ ->
      map(\pat::Decorated Pattern ->
        name("__generated_" ++ toString(genIntReally(pat)), top.location),
        ps.patternList)
    | _ -> []
    end;

}

aspect default production
top::AbstractMatchRule ::=
{
  top.aspectProdParamsList = [];
}

function genIntReally -- zzz
Integer ::= a
{ return genInt(); }
