grammar silver_features;

nonterminal TransNT1;
nonterminal TransNT2;
nonterminal TransNT3;

translation attribute trans1::TransNT2 occurs on TransNT1;
translation attribute trans2::TransNT3 occurs on TransNT2;

wrongCode "Cycle in translation attributes! silver_features:trans3 translates silver_features:TransNT3 to silver_features:TransNT1, but this nonterminal has translation attributes to silver_features:TransNT1, silver_features:TransNT2, silver_features:TransNT3." {
  translation attribute trans3::TransNT1 occurs on TransNT3;
}

translation attribute thing<a>::a;

wrongCode "Occurrence of translation attribute silver_features:thing must have a nonterminal type.  Instead it is of type String" {
  attribute thing<String> occurs on TransNT1;
}
