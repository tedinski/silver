grammar silver:extension:polymorphism;

import core;
import silver:base;
import silver:extension:autocopy ;

aspect production plmProdDcl
d::AGDcl ::= a::Abstract_kwd p::Production_kwd  pd::Id_t ps::TypeParams
	s::PlmProductionSignature body::ProductionBody
{
  body.isAspect = false; 
}


