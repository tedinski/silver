grammar silver:extension:bidirtransform;

nonterminal ProductionDef with env, errors, namedSig, patternList, matchProd, typerep, inputNames, location, absGroup, cncGroup, pp, grammarName;

synthesized attribute patternList::PatternList;
synthesized attribute matchProd::Expr;
synthesized attribute namedSig::NamedSignature;

autocopy attribute absGroup::NonterminalList;
autocopy attribute cncGroup::NonterminalList;

concrete production productionDef
pd::ProductionDef ::= qn::QName '(' args::PatternList ')'
{
    pd.errors := args.errors;
    
    pd.pp = qn.pp ++ "(" ++ args.pp ++ ")";

    args.env = pd.env;
    
    local absSig::[NamedSignature] = getProdFromGroup(qn.name, pd.absGroup);
    local cncSig::[NamedSignature] = getProdFromGroup(qn.name, pd.cncGroup);

    pd.namedSig = if length(absSig) != 0 then head(absSig)
        else head(cncSig);
        
    pd.matchProd = matchProd(pd.location, args.rawPatternList, pd.namedSig.inputElements);
    pd.typerep = pd.namedSig.outputElement.typerep;

    -- When we looked up a production, was exactly one production found?
    pd.errors <- if length(absSig) != 0 || length(cncSig) != 0 then []
                 else [err(pd.location, "Unknown Production")];
    
    -- Is the pattern as long as the production's expected input arguments?
    pd.errors <- if length(pd.namedSig.inputElements) != length(args.rawPatternList) 
        then [err(pd.location, "Transformation Production does not match size with Production Signature")]
        else [];

    -- Are variables in pattern the appropriate type for where they are used?
    pd.errors <- tyCheckProd(pd.location, args.rawPatternList, pd.namedSig.inputElements);

    -- Are there any duplicate anonymous variable names defined?
    -- TODO
}

function matchProd
Expr ::= loc::Location args::[Pattern] nsElems::[NamedSignatureElement]
{
    return if length(args) == 1 
        then matchSingle(loc, head(args), head(nsElems), trueConst('true', location=loc)) 
        else matchSingle(loc, head(args), head(nsElems), matchProd(loc, tail(args), tail(nsElems)));
}
                     
function matchSingle
Expr ::= loc::Location arg::Pattern nsElem::NamedSignatureElement ifTrue::Expr
{   
    -- This is unreadable so long as we don't have default annotations
    return case arg of 
        | wildcPattern(_) -> ifTrue
        | _ -> caseExpr_c('case', exprsSingle(baseName(loc, nsElem.elementName), location=loc),
            'of', terminal(Opt_Vbar_t, "|"), mRuleList_cons(matchRule_c(patternList_one(arg, location=loc),
                '->', ifTrue, location=loc),
                    terminal(Vbar_kwd, "|"), mRuleList_one(matchRule_c(patternList_one(wildcPattern('_',location=loc),
                        location=loc),
                    '->',falseConst('false',location=loc),location=loc),location=loc),location=loc),
            'end', location=loc)
    end;
}        

function tyCheckProd
[Message] ::= loc::Location args::[Pattern] nsElems::[NamedSignatureElement]
{
    -- TODO
    return [];
}