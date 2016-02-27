grammar silver:extension:doc:core;

aspect production aspectProductionDcl
top::AGDcl ::= 'aspect' 'production' id::QName ns::AspectProductionSignature body::ProductionBody
{
  top.docs := [commentDocItem(bodilessCommentItem("aspect production", id.name, ns.pp))];
}

concrete production docAspectProductionDcl
top::AGDcl ::= comment::DocComment 'aspect' 'production' id::QName ns::AspectProductionSignature body::ProductionBody
{
  top.docs := [commentDocItem(commentItem("aspect production", id.name, ns.pp, comment))];

  forwards to aspectProductionDcl('aspect', 'production', id, ns, body, location=top.location);
}

concrete production noDocAspectProductionDcl
top::AGDcl ::= noDoc::NoDocComment_t 'aspect' 'production' id::QName ns::AspectProductionSignature body::ProductionBody
{
  top.docs := [];

  forwards to aspectProductionDcl('aspect', 'production', id, ns, body, location=top.location);
}

aspect production aspectFunctionDcl
top::AGDcl ::= 'aspect' 'function' id::QName ns::AspectFunctionSignature body::ProductionBody
{
  top.docs := [commentDocItem(bodilessCommentItem("aspect function", id.name, ns.pp))];
}

concrete production docAspectFunctionDcl
top::AGDcl ::= comment::DocComment 'aspect' 'function' id::QName ns::AspectFunctionSignature body::ProductionBody
{
  top.docs := [commentDocItem(commentItem("aspect function", id.name, ns.pp, comment))];

  forwards to aspectFunctionDcl('aspect', 'function', id, ns, body, location=top.location);
}

concrete production noDocAspectFunctionDcl
top::AGDcl ::= noDoc::NoDocComment_t 'aspect' 'function' id::QName ns::AspectFunctionSignature body::ProductionBody
{
  top.docs := [];

  forwards to aspectFunctionDcl('aspect', 'function', id, ns, body, location=top.location);
}
