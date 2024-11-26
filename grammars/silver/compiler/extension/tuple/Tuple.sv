-- Note: We consider only tuples containing two or more elements
--       The empty tuple () forwards to unit

grammar silver:compiler:extension:tuple;

imports silver:compiler:definition:core;
imports silver:compiler:definition:env;
imports silver:compiler:definition:type:syntax;
imports silver:compiler:definition:type;
imports silver:compiler:definition:flow:env;
imports silver:compiler:analysis:typechecking:core;

imports silver:compiler:extension:patternmatching;

terminal IntConst /[0-9]+/;

tracked nonterminal TupleList with unparse, translation;

-- used to convert the comma-separated list of expressions 
-- that make up the tuple into a pair expression:
translation attribute translation :: Expr;

concrete production emptyTuple
top::Expr ::= '(' ')'
{
  top.unparse = "()";
  top.typerep = tupleType([]);
  forwards to Silver_Expr { silver:core:unit() };
}

concrete production tupleExpr
top::Expr ::= '(' tl::TupleList ')'
{
  top.unparse = "(" ++ tl.unparse ++ ")";

  -- computing specialized tupleType from forward.typerep 
  -- is cleaner than performing type checking on TupleList
  -- (performSubstitution is needed because forward.typerep 
  -- isn't instantiated into a chain of pairs until upSubst is applied) 
  top.typerep = tupleType(performSubstitution(forward.typerep, forward.upSubst).tupleElems);
  
  forwards to @tl.translation;
}

-- selects tuple element at index a
concrete production selector
top::Expr ::= tuple::Expr '.' a::IntConst
{

  -- Forward gets the substitution context of the tuple
  propagate grammarName, config, compiledGrammars, frame, env, flowEnv, downSubst, upSubst, finalSubst, freeVars;
  tuple.decSiteVertexInfo = nothing();
  tuple.appDecSiteVertexInfo = nothing();
  tuple.dispatchFlowDeps = [];
  tuple.isRoot = false;

  local accessIndex::Integer = toInteger(a.lexeme);

  top.unparse = tuple.unparse ++ "." ++ a.lexeme;

  local ty :: Type = performSubstitution(tuple.typerep, tuple.upSubst);
  local len::Integer = length(ty.tupleElems);
  
  forwards to if (accessIndex > len || accessIndex < 1) then
      errorExpr([errFromOrigin(top, "Invalid tuple selector index.")])
    -- @ prevents exponential type checking
    else select(@tuple, 1, accessIndex, len);

}

abstract production select
-- i is the current index, a is the desired access index
-- len is the total length of the tuple
top::Expr ::= exp::Expr i::Integer a::Integer len::Integer
{
  forwards to 
    if i == a then
      if a == len then
        -- only if the access index is the length of the
        -- tuple do we simply return the expression itself
        @exp
      else Silver_Expr { $Expr{@exp}.fst }
    else select(Silver_Expr{ $Expr{@exp}.snd }, i + 1, a, len);
}

-- TupleList cases:
-- There are two elements in the tuple
concrete production tupleList_2Elements
top::TupleList ::= fst::Expr ',' snd::Expr
{
  top.unparse = fst.unparse ++ ", " ++ snd.unparse;
  top.translation = Silver_Expr { silver:core:pair(fst=$Expr{@fst}, snd=$Expr{@snd}) };
}

-- There are more than two elements in the tuple
concrete production tupleList_nElements
top::TupleList ::= fst::Expr ',' snd::TupleList
{
  top.unparse = fst.unparse ++ ", " ++ snd.unparse;
  top.translation = Silver_Expr { silver:core:pair(fst=$Expr{@fst}, snd=$Expr{@snd.translation}) };
}