grammar silver:compiler:translation:java:core;

import silver:compiler:driver:util;

attribute genFiles occurs on RootSpec;
attribute genBinaryFiles occurs on RootSpec;

aspect production interfaceRootSpec
top::RootSpec ::= _ _ _
{
  top.genFiles := [];
  top.genBinaryFiles := [];
}

aspect production errorRootSpec
top::RootSpec ::= _ _ _ _ _
{
  top.genFiles := [];
  top.genBinaryFiles := [];
}

aspect production grammarRootSpec
top::RootSpec ::= g::Grammar  _ _ _ _ _
{
  top.genBinaryFiles := [
    ("Silver.svi", serInterface)
  ];

  top.genFiles := g.genFiles ++
  [("Init.java", s"""
package ${makeName(g.declaredName)};

public class Init{
	private static boolean preInit = false;
	private static boolean init = false;
	private static boolean postInit = false;

	public static void initAllStatics(){
		if(preInit) return;
		preInit = true;
${makeOthers(top.allGrammarDependencies, "initAllStatics")}
	}

	public static void init(){
		if(init) return;
		init = true;
		setupInheritedAttributes();
${makeOthers(top.allGrammarDependencies, "init")}
		initProductionAttributeDefinitions();
	}

	public static void postInit(){
		if(postInit) return;
		postInit = true;
${makeOthers(top.allGrammarDependencies, "postInit")}
${g.postInit}
	}

	private static void setupInheritedAttributes(){
${g.setupInh}
	}

	private static void initProductionAttributeDefinitions(){
${g.initProd}
	}

${g.initWeaving}
${g.valueWeaving}
	final static common.DecoratedNode context = common.TopNode.singleton; // For globals
${g.initValues}
}
""")];
}

fun makeOthers String ::= others::[String] nme::String =
  if null(others) then "" else s"\t\t${makeName(head(others))}.Init.${nme}();\n${makeOthers(tail(others),nme)}";

