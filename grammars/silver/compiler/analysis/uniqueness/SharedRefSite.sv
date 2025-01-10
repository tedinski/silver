grammar silver:compiler:analysis:uniqueness;

-- Shared references taken in this tree
monoid attribute sharedRefs::[(String, SharedRefSite)];

attribute sharedRefs occurs on
  Grammar, File, AGDcls, AGDcl,
  ProductionBody, ProductionStmts, ProductionStmt;
propagate sharedRefs on
  Grammar, File, AGDcls, AGDcl,
  ProductionBody, ProductionStmts, ProductionStmt;

{--
 - Represents taking of a shared reference to a child or local/production attribute,
 - to catch a tree being shared in multiple places.
 -}
data SharedRefSite = sharedRefSite with
  sourceGrammar,  -- The grammar of where the reference was taken
  sourceLocation; -- The location of where the reference was taken

-- Append lists of references, ignoring duplicate refs to the same ref site
fun unionMutuallyExclusiveRefs
[(String, SharedRefSite)] ::= rs1::[(String, SharedRefSite)] rs2::[(String, SharedRefSite)] =
  rs1 ++ filter(\ r::(String, SharedRefSite) -> !lookup(r.1, rs1).isJust, rs2);

-- We don't care about the locations for correctness, don't compare it to avoid touching interface files.
instance Eq SharedRefSite {
  eq = \ s1::SharedRefSite s2::SharedRefSite -> s1.sourceGrammar == s2.sourceGrammar;
}
