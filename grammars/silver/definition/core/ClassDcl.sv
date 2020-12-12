grammar silver:definition:core;

concrete production typeClassDcl
top::AGDcl ::= 'class' cl::OptConstraintList id::Name var::TypeExpr '{' body::ClassBody '}'
{
  top.unparse = s"class ${cl.unparse}${id.unparse} ${var.unparse}\n{\n${body.unparse}\n}"; 

  production fName :: String = top.grammarName ++ ":" ++ id.name;
  production tv :: TyVar =
    case var.typerep.freeVariables of
    | v :: _ -> v
    | _ -> freshTyVar()
    end;
  production supers::[Context] = cl.contexts;
  production boundVars::[TyVar] = [tv];
  
  top.defs := classDef(top.grammarName, id.location, fName, supers, tv, body.classMembers) :: body.defs;

  -- Here we ensure that the type is just a type *variable*
  top.errors <- var.errorsTyVars;
  
  -- Redefinition check of the name
  top.errors <- 
    if length(getTypeDclAll(fName, top.env)) > 1 
    then [err(id.location, "Type '" ++ fName ++ "' is already bound.")]
    else [];

  top.errors <-
    if isLower(substring(0,1,id.name))
    then [err(id.location, "Types must be capitalized. Invalid class name " ++ id.name)]
    else [];

  production attribute headDefs :: [Def] with ++;
  headDefs := cl.defs;
  headDefs <- [instDef(top.grammarName, id.location, fName, boundVars, [], var.typerep)];

  cl.env = newScopeEnv(headDefs, top.env);
  
  body.env = cl.env;
  body.classContext = instContext(fName, var.typerep);
}

autocopy attribute classContext::Context;

nonterminal ClassBody with
  config, grammarName, env, defs, location, unparse, errors, classContext, compiledGrammars, classMembers;
nonterminal ClassBodyItem with
  config, grammarName, env, defs, location, unparse, errors, classContext, compiledGrammars, classMembers;

propagate defs, errors on ClassBody, ClassBodyItem;

concrete production consClassBody
top::ClassBody ::= h::ClassBodyItem t::ClassBody
{
  top.unparse = h.unparse ++ "\n" ++ t.unparse;
  top.classMembers = h.classMembers ++ t.classMembers;
}
concrete production nilClassBody
top::ClassBody ::= 
{
  top.unparse = "";
  top.classMembers = [];
}

concrete production classBodyItem
top::ClassBodyItem ::= id::Name '::' ty::TypeExpr ';'
{
  top.unparse = s"${id.name} :: ${ty.unparse};";
  
  production fName :: String = top.grammarName ++ ":" ++ id.name;
  production boundVars :: [TyVar] =
    setUnionTyVars(top.classContext.freeVariables, ty.typerep.freeVariables);
  top.classMembers = [fName];
  
  top.defs <- [classMemberDef(top.grammarName, top.location, fName, boundVars, top.classContext, ty.typerep)];

  top.errors <-
    if length(getValueDclAll(fName, top.env)) > 1
    then [err(id.location, "Value '" ++ fName ++ "' is already bound.")]
    else [];
}

-- TODO: Defaults
