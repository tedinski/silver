grammar silver:extension:silverconstruction;

marking terminal SilverExpr_t           'Silver_Expr'           lexer classes {KEYWORD, RESERVED};
marking terminal SilverPattern_t        'Silver_Pattern'        lexer classes {KEYWORD, RESERVED};
marking terminal SilverAGDcl_t          'Silver_AGDcl'          lexer classes {KEYWORD, RESERVED};
marking terminal SilverProductionStmt_t 'Silver_ProductionStmt' lexer classes {KEYWORD, RESERVED};

temp_imp_ide_font font_escape color(160, 32, 240) bold italic;
lexer class Escape font=font_escape;

terminal EscapeExpr_t              '$Expr'              lexer classes {Escape};
terminal EscapeTypeExpr_t          '$TypeExpr'          lexer classes {Escape};
terminal EscapePattern_t           '$Pattern'           lexer classes {Escape};
terminal EscapeQName_t             '$QName'             lexer classes {Escape};
terminal EscapeQNameAttrOccur_t    '$QNameAttrOccur'    lexer classes {Escape};
terminal EscapeName_t              '$Name'              lexer classes {Escape};
terminal Escape_qName_t            '$qName'             lexer classes {Escape};
terminal Escape_name_t             '$name'              lexer classes {Escape};
