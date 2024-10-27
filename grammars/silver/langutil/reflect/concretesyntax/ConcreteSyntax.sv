grammar silver:langutil:reflect:concretesyntax;

-- This grammar logically belongs under of silver:reflect, but it needs to live
-- here due to its dependency on the langutil artifact.

imports silver:reflect;
imports silver:langutil;

terminal Comma_t       ',';
terminal Equal_t       '=';
terminal Colon_t       ':';
terminal LParen_t      '(';
terminal RParen_t      ')';
terminal LSqr_t        '[';
terminal RSqr_t        ']';

terminal QName_t /[A-Za-z][A-Za-z0-9\_:]*/ submits to {ASTkwd};

lexer class ASTkwd;
terminal Terminal_kwd 'terminal' lexer classes {ASTkwd};

terminal True_kwd  'true' lexer classes {ASTkwd};
terminal False_kwd 'false' lexer classes {ASTkwd};
terminal Int_t     /[\-]?[0-9]+/;
terminal Float_t   /[\-]?[0-9]+[\.][0-9]+/;
terminal String_t  /[\"]([^\r\n\"\\]|[\\][\"]|[\\][\\]|[\\]b|[\\]n|[\\]r|[\\]f|[\\]t)*[\"]/;

ignore terminal WhiteSpace /[\r\n\t\ ]+/;

closed tracked nonterminal AST_c with unparse, ast<AST>, errors;

concrete productions top::AST_c
| prodName::QName_t '(' children::ASTs_c ',' annotations::NamedASTs_c ')'
  {
    top.unparse = s"${prodName.lexeme}(${children.unparse}, ${annotations.unparse})";
    top.ast =
      nonterminalAST(prodName.lexeme, foldr(consAST, nilAST(), children.ast), foldr(consNamedAST, nilNamedAST(), annotations.ast));
    top.errors := children.errors ++ annotations.errors;
  }
| prodName::QName_t '(' children::ASTs_c ')'
  {
    top.unparse = s"${prodName.lexeme}(${children.unparse})";
    top.ast = nonterminalAST(prodName.lexeme, foldr(consAST, nilAST(), children.ast), nilNamedAST());
    top.errors := children.errors;
  }
| prodName::QName_t '(' annotations::NamedASTs_c ')'
  {
    top.unparse = s"${prodName.lexeme}(${annotations.unparse})";
    top.ast = nonterminalAST(prodName.lexeme, nilAST(), foldr(consNamedAST, nilNamedAST(), annotations.ast));
    top.errors := annotations.errors;
  }
| prodName::QName_t '(' ')'
  {
    top.unparse = s"${prodName.lexeme}()";
    top.ast = nonterminalAST(prodName.lexeme, nilAST(), nilNamedAST());
    top.errors := [];
  }
| 'terminal' '(' terminalName::QName_t ',' lexeme::String_t ',' location::AST_c ')'
  {
    top.unparse = s"terminal(${terminalName.lexeme}, ${lexeme.lexeme}, ${location.unparse})";
    local locReifyRes::Either<String Location> = reify(location.ast);
    top.ast =
      terminalAST(
        terminalName.lexeme,
        unescapeString(substring(1, length(lexeme.lexeme) - 1, lexeme.lexeme)),
        fromRight(locReifyRes, bogusLoc()));
    top.errors :=
      case locReifyRes of
      | left(msg) -> [errFromOrigin(location, msg)]
      | right(_) -> []
      end;
  }
| '[' vals::ASTs_c ']'
  {
    top.unparse = s"[${vals.unparse}]";
    top.ast = listAST(foldr(consAST, nilAST(), vals.ast));
    top.errors := vals.errors;
  }
| '[' ']'
  {
    top.unparse = "[]";
    top.ast = listAST(nilAST());
    top.errors := [];
  }
| s::String_t
  {
    top.unparse = s.lexeme;
    top.ast = stringAST(unescapeString(substring(1, length(s.lexeme) - 1, s.lexeme)));
    top.errors := [];
  }
| i::Int_t
  {
    top.unparse = i.lexeme;
    top.ast = integerAST(toInteger(i.lexeme));
    top.errors := [];
  }
| f::Float_t
  {
    top.unparse = f.lexeme;
    top.ast = floatAST(toFloat(f.lexeme));
    top.errors := [];
  }
| 'true'
  {
    top.unparse = "true";
    top.ast = booleanAST(true);
    top.errors := [];
  }
| 'false'
  {
    top.unparse = "false";
    top.ast = booleanAST(false);
    top.errors := [];
  }

tracked nonterminal ASTs_c with unparse, ast<[AST]>, errors;

concrete productions top::ASTs_c
| t::ASTs_c ',' h::AST_c
  {
    top.unparse = s"${t.unparse}, ${h.unparse}";
    top.ast = t.ast ++ [h.ast];
    top.errors := h.errors ++ t.errors;
  }
| h::AST_c
  {
    top.unparse = h.unparse;
    top.ast = [h.ast];
    top.errors := [];
  }

tracked nonterminal NamedASTs_c with unparse, ast<[NamedAST]>, errors;

concrete productions top::NamedASTs_c
| t::NamedASTs_c ',' h::NamedAST_c
  {
    top.unparse = s"${t.unparse}, ${h.unparse}";
    top.ast = t.ast ++ [h.ast];
    top.errors := h.errors ++ t.errors;
  }
| h::NamedAST_c
  {
    top.unparse = h.unparse;
    top.ast = [h.ast];
    top.errors := [];
  }

tracked nonterminal NamedAST_c with unparse, ast<NamedAST>, errors;

concrete productions top::NamedAST_c
| n::QName_t '=' v::AST_c
  {
    top.unparse = s"${n.lexeme} = ${v.unparse}";
    top.ast = namedAST(n.lexeme, v.ast);
    top.errors := v.errors;
  }
