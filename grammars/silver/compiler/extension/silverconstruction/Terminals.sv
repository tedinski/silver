grammar silver:compiler:extension:silverconstruction;

marking terminal SilverExpr_t           'Silver_Expr'           lexer classes {KEYWORD, RESERVED};
marking terminal SilverExprInh_t        'Silver_ExprInh'        lexer classes {KEYWORD, RESERVED};
marking terminal SilverPattern_t        'Silver_Pattern'        lexer classes {KEYWORD, RESERVED};
marking terminal SilverAGDcl_t          'Silver_AGDcl'          lexer classes {KEYWORD, RESERVED};
marking terminal SilverProductionStmt_t 'Silver_ProductionStmt' lexer classes {KEYWORD, RESERVED};
marking terminal SilverTypeExpr_t       'Silver_TypeExpr'       lexer classes {KEYWORD, RESERVED};

lexer class Antiquote extends SPECOP;

terminal AntiquoteExpr_t              '$Expr'              lexer classes {Antiquote};
terminal AntiquoteAppExpr_t           '$AppExpr'           lexer classes {Antiquote};
terminal AntiquoteExprInhs_t          '$ExprInhs'          lexer classes {Antiquote};
terminal AntiquoteTypeExpr_t          '$TypeExpr'          lexer classes {Antiquote};
terminal AntiquoteConstraintList_t    '$ConstraintList'    lexer classes {Antiquote};
terminal AntiquotePattern_t           '$Pattern'           lexer classes {Antiquote};
terminal AntiquoteFunctionSignature_t '$FunctionSignature' lexer classes {Antiquote};
terminal AntiquoteProductionRHS_t     '$ProductionRHS'     lexer classes {Antiquote};
terminal AntiquoteAspectRHS_t         '$AspectRHS'         lexer classes {Antiquote};
terminal AntiquoteProductionStmt_t    '$ProductionStmt'    lexer classes {Antiquote};
terminal AntiquoteQName_t             '$QName'             lexer classes {Antiquote};
terminal AntiquoteQNameAttrOccur_t    '$QNameAttrOccur'    lexer classes {Antiquote};
terminal AntiquoteName_t              '$Name'              lexer classes {Antiquote};
terminal Antiquote_qName_t            '$qName'             lexer classes {Antiquote};
terminal Antiquote_name_t             '$name'              lexer classes {Antiquote};
