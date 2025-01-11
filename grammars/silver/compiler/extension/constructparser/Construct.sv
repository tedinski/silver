grammar silver:compiler:extension:constructparser;
import silver:compiler:definition:core;
import silver:compiler:definition:env;
import silver:compiler:definition:type;
import silver:compiler:definition:type:syntax;
import silver:compiler:modification:copper;
import silver:compiler:modification:list;

terminal Construct_t 'construct' lexer classes {KEYWORD};
terminal Translator_t 'translator' lexer classes {KEYWORD};
terminal Using_t 'using' lexer classes {KEYWORD};

concrete production construct_c
top::File ::= gdcl::GrammarDcl  mStmts::ModuleStmts  is::ImportStmts
  'construct' parserName::Name  'as' m::QName  'translator'  'using'  ms::ParserComponents
{
  local agDcls :: AGDcls =
    consAGDcls(@setJarName, consAGDcls(@prsr, consAGDcls(@main,
      nilAGDcls())));

  local setJarName :: AGDcl = jarNameDcl(@parserName);

  local prsr :: AGDcl =
    parserDcl('parser', name("extendedParser"), '::',
      nominalTypeExpr(qNameTypeId(terminal(IdUpper_t, "File"))),
      '{',
      consParserComponent(
        parserComponent(moduleName(@m),
          nilParserComponentModifier(), ';'),
        @ms),
      '}');

  local main :: AGDcl =
    functionDcl('function', name("main"),
      functionSignature(
        nilConstraint(),
        '=>',
        functionLHS(
          appTypeExpr(
            nominalTypeExpr(
              qNameTypeId(terminal(IdUpper_t, "IOVal"))),
            bTypeList('<', typeListSingle(integerTypeExpr('Integer')), '>'))),
        '::=',
        productionRHSCons(
          productionRHSElem(elemNotShared(), name("args"), '::',
            listTypeExpr('[', stringTypeExpr('String'), ']')),
          productionRHSCons(
            productionRHSElem(elemNotShared(), name("ioIn"), '::',
              nominalTypeExpr(qNameTypeId(terminal(IdUpper_t, "IOToken")))),
            productionRHSNil()))),
      productionBody('{',
        productionStmtsSnoc(productionStmtsNil(),
          returnDef('return',
            Silver_Expr { driver(args, ioIn, extendedParser) },
            ';')),
        '}'));

  local importStmts :: ImportStmts =
    consImportStmts(
      importStmt('import', moduleAll(^m), ';'),
      @is);

  forwards to fileRoot(@gdcl, @mStmts, @importStmts, @agDcls);
}

