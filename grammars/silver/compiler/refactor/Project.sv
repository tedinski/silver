grammar silver:compiler:refactor;

imports silver:util:cmdargs;
imports silver:compiler:driver;

imports silver:compiler:definition:core;
imports silver:compiler:definition:type;
imports silver:compiler:definition:env;
imports silver:compiler:definition:concrete_syntax;
imports silver:compiler:definition:type:syntax;
imports silver:compiler:definition:flow:syntax;

imports silver:compiler:analysis:typechecking:core;

imports silver:compiler:modification:let_fix;
imports silver:compiler:modification:lambda_fn;
imports silver:compiler:modification:concisefunctions;
imports silver:compiler:modification:collection;
imports silver:compiler:modification:primitivepattern;
imports silver:compiler:modification:ffi;
imports silver:compiler:modification:copper;
imports silver:compiler:modification:defaultattr;
imports silver:compiler:modification:list;
imports silver:compiler:modification:copper_mda;

imports silver:rewrite;
imports silver:langutil:pp;
imports silver:langutil:unparse;

-- Here we specify how layout/indentation should be handled for productions that are
-- introduced as the result of a transformation, and thus don't have layout from the
-- original CST.

aspect production nonterminalAST
top::AST ::= prodName::String children::ASTs annotations::NamedASTs
{
  prodChildLayout <- [
    ("silver:compiler:modification:concisefunctions:shortFunctionDcl", 1, line()),
    ("silver:compiler:modification:concisefunctions:shortFunctionDcl", 3, line()),
    ("silver:compiler:extension:convenience:shortNondecLocalDecl", 5, line()),
    ("silver:compiler:extension:convenience:shortNondecLocalDeclwKwds", 6, line())
  ];
  prodChildIndent <- [
    ("silver:compiler:modification:concisefunctions:shortFunctionDcl", 4, 2),
    ("silver:compiler:extension:convenience:shortNondecLocalDecl", 6, 2),
    ("silver:compiler:extension:convenience:shortNondecLocalDeclwKwds", 7, 2)
  ];
  prodChildGroup <- [
    ("silver:compiler:modification:concisefunctions:shortFunctionDcl", 0, 2),
    ("silver:compiler:modification:concisefunctions:shortFunctionDcl", 3, 5),
    ("silver:compiler:extension:convenience:shortNondecLocalDecl", 5, 7),
    ("silver:compiler:extension:convenience:shortNondecLocalDeclwKwds", 6, 8)
  ];
}

aspect production terminalAST
top::AST ::= _ _ _
{
  termPreLayout <- [
    ("silver:compiler:definition:core:Equal_t", pp" ")
  ];
  termPostLayout <- [
    ("silver:compiler:definition:core:Global_kwd", pp" "),
    ("silver:compiler:modification:concisefunctions:Fun_kwd", pp" "),
    ("silver:compiler:definition:core:Comma_t", pp" "),
    ("silver:compiler:definition:core:Equal_t", pp" "),
    ("silver:compiler:definition:core:Nondec_kwd", pp" "),
    ("silver:compiler:definition:core:Local_kwd", pp" "),
    ("silver:compiler:definition:core:Attribute_kwd", pp" ")
  ];
}
