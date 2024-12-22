grammar silver:compiler:translation:java:core;

import silver:compiler:modification:ffi only ioForeignType; -- for main type check only
import silver:compiler:modification:list only listCtrType;

import silver:compiler:modification:concisefunctions;

aspect production shortFunctionDcl
top::AGDcl ::= 'fun' id::Name ns::FunctionSignature '=' e::Expr ';'
{
  -- For main functions which return IOVal<Integer>
  local attribute typeIOValFailed::Boolean = unify(namedSig.typerep,
    appTypes(
      functionType(2, []),
        [appType(listCtrType(), stringType()),
          ioForeignType,
          appType(nonterminalType("silver:core:IOVal", [starKind()], true, false), intType())])).failure;

  -- For main functions which return IO<Integer>
  local attribute typeIOMonadFailed::Boolean = unify(namedSig.typerep,
    appTypes(
      functionType(1, []),
        [appType(listCtrType(), stringType()),
          appType(nonterminalType("silver:core:IO", [starKind()], false, false), intType())])).failure;

  top.genFiles <-
    if id.name == "main"
      then [("Main.java", generateMainClassString(top.grammarName, !typeIOValFailed))]
      else [];

  top.errors <-
    if id.name == "main" && typeIOValFailed && typeIOMonadFailed -- Neither legal main function type used
      then [errFromOrigin(top, "main function must have type signature (IOVal<Integer> ::= [String] IOToken) " ++
        "or (IO<Integer> ::= [String]). Instead it has type " ++ prettyType(namedSig.typerep))]
      else [];
}

aspect production functionDcl
top::AGDcl ::= 'function' id::Name ns::FunctionSignature body::ProductionBody
{
  local className :: String = "P" ++ escapeName(id.name, top.genFilesUnescapedDown);

  top.setupInh := body.setupInh;
  top.initProd := s"\t\t//FUNCTION ${id.name} ${ns.unparse}\n" ++ body.translation;

  local localVar :: String = "count_local__ON__" ++ makeIdName(fName);

  top.initWeaving := s"\tpublic static int ${localVar} = 0;\n";
  top.valueWeaving := body.valueWeaving;

  local argsAccess :: String =
    implode(", ", map(\ c::Context -> decorate c with {boundVariables = namedSig.freeVariables;}.contextRefElem, namedSig.contexts) ++ map((.childRefElem), namedSig.inputElements));

  local funBody :: String =
s"""			final common.DecoratedNode context = new P${id.name}(${argsAccess}).decorate(originCtx);
			//${head(body.returnExpr).unparse}
			return (${namedSig.outputElement.typerep.transType})(${head(body.returnExpr).translation});
""";

  top.genFilesUnescapedUp := [id.name];
  top.genFiles :=
    [(s"${className}.java", generateFunctionClassString(body.env, top.flowEnv, top.grammarName, id.name, namedSig, funBody, top.genFilesUnescapedDown))] ++
    if id.name == "main" 
	then [("Main.java", generateMainClassString(top.grammarName, !typeIOValFailed))] -- !typeIOValFailed true if main type used was IOVal<Integer>
    else [];

  -- For main functions which return IOVal<Integer>
  local attribute typeIOValFailed::Boolean = unify(namedSig.typerep,
    appTypes(
      functionType(2, []),
        [appType(listCtrType(), stringType()),
          ioForeignType,
          appType(nonterminalType("silver:core:IOVal", [starKind()], true, false), intType())])).failure;

  -- For main functions which return IO<Integer>
  local attribute typeIOMonadFailed::Boolean = unify(namedSig.typerep,
    appTypes(
      functionType(1, []),
        [appType(listCtrType(), stringType()),
          appType(nonterminalType("silver:core:IO", [starKind()], false, false), intType())])).failure;

  -- main function signature check TODO: this should probably be elsewhere!
  top.errors <- 
    if id.name == "main" && typeIOValFailed && typeIOMonadFailed -- Neither legal main function type used
    then [errFromOrigin(top, "main function must have type signature (IOVal<Integer> ::= [String] IOToken) " ++ 
		"or (IO<Integer> ::= [String]). Instead it has type " ++ prettyType(namedSig.typerep))]
    else [];
}

function generateFunctionClassString
String ::= env::Env flowEnv::FlowEnv whatGrammar::String whatName::String whatSig::NamedSignature whatResult::String genFilesUnescapedDown::[String]
{
  local className :: String = "P" ++ escapeName(whatName, genFilesUnescapedDown);

  local localVar :: String = 
    s"count_local__ON__${makeIdName(whatGrammar)}_${whatName}";

  local commaIfArgs :: String = if length(whatSig.contexts) + length(whatSig.inputElements) != 0 then "," else "";
  
  local contexts::Contexts = foldContexts(whatSig.contexts);
  contexts.boundVariables = whatSig.freeVariables;

  return s"""
package ${makeName(whatGrammar)};

import silver.core.NOriginInfo;

public final class ${className} extends common.FunctionNode {

${makeIndexDcls(0, whatSig.inputElements)}

	public static final int num_local_attrs = Init.${localVar};
	public static final String[] occurs_local = new String[num_local_attrs];

	public static final common.Lazy[][] childInheritedAttributes = new common.Lazy[${toString(length(whatSig.inputElements))}][];

    public static final boolean[] localDecorable = new boolean[num_local_attrs];
	public static final common.Lazy[] localAttributes = new common.Lazy[num_local_attrs];
    public static final common.Lazy[] localDecSites = new common.Lazy[num_local_attrs];
	public static final common.Lazy[][] localInheritedAttributes = new common.Lazy[num_local_attrs][];

${whatSig.inhOccursIndexDecls}

	public static final int[] childInhContextTypeVars = {${implode(",", whatSig.childTypeVarElems)}};
	public static final int[] localInhContextTypeVars = new int[num_local_attrs];

	static {
${whatSig.childStatic}
	}

	public ${className}(${whatSig.javaSignature}) {
${implode("", map(makeChildAssign, whatSig.inputElements))}
${contexts.contextInitTrans}
	}

${whatSig.childDecls}

${contexts.contextMemberDeclTrans}

	@Override
	public boolean isChildDecorable(final int index) {
		switch(index) {
${implode("", map(makeChildDecorableCase(env, _), whatSig.inputElements))}
            default: return false;
        }
    }

	@Override
	public Object getChild(final int index) {
		switch(index) {
${implode("", map(makeChildAccessCase, whatSig.inputElements))}
			default: return null;
		}
	}

	@Override
	public Object getChildLazy(final int index) {
		switch(index) {
${implode("", map(makeChildAccessCaseLazy, whatSig.inputElements))}
			default: return null;
		}
	}

	@Override
	public common.Lazy getChildDecSite(final int index) {
		switch(index) {
${implode("", map(makeChildDecSiteAccessCase(env, flowEnv, whatSig.outputElement.typerep.typeName, whatSig.fullName, _), whatSig.inputElements))}
            default: return null;
        }
    }

	@Override
	public final int getNumberOfChildren() {
		return ${toString(length(whatSig.inputElements))};
	}

	@Override
	public common.Lazy[] getLocalInheritedAttributes(final int key) {
${flatMap(makeInhOccursContextAccess(whatSig.freeVariables, whatSig.contextInhOccurs, "localInhContextTypeVars", "localInheritedAttributes", _), whatSig.inhOccursContextTypes)}
		return localInheritedAttributes[key];
	}

	@Override
	public common.Lazy[] getChildInheritedAttributes(final int key) {
${flatMap(makeInhOccursContextAccess(whatSig.freeVariables, whatSig.contextInhOccurs, "childInhContextTypeVars", "childInheritedAttributes", _), whatSig.inhOccursContextTypes)}
		return childInheritedAttributes[key];
	}

	@Override
	public boolean isLocalDecorable(final int key) {
		return localDecorable[key];
	}

	@Override
	public common.Lazy getLocal(final int key) {
		return localAttributes[key];
	}

	@Override
	public common.Lazy getLocalDecSite(final int key) {
		return localDecSites[key];
	}

	@Override
	public final int getNumberOfLocalAttrs() {
		return num_local_attrs;
	}

	@Override
	public final String getNameOfLocalAttr(final int index) {
		return occurs_local[index];
	}

	@Override
	public String getName() {
		return "${whatSig.fullName}";
	}

	public static ${whatSig.outputElement.typerep.transType} invoke(final common.OriginContext originCtx ${commaIfArgs} ${whatSig.javaSignature}) {
		try {
${whatResult}
		} catch(Throwable t) {
			throw new common.exceptions.TraceException("Error while evaluating function ${whatSig.fullName}", t);
		}
	}

${if null(whatSig.contexts) -- Can only use a singleton when there aren't contexts.
  then s"""
	public static final common.NodeFactory<${whatSig.outputElement.typerep.transCovariantType}> factory = new Factory();
""" else s"""
	public static final common.NodeFactory<${whatSig.outputElement.typerep.transCovariantType}> getFactory(${contexts.contextParamTrans}) {
		return new Factory(${implode(", ", map(\ c::Context -> decorate c with {boundVariables = whatSig.freeVariables;}.contextRefElem, whatSig.contexts))});
	}
"""}

	public static final class Factory extends common.NodeFactory<${whatSig.outputElement.typerep.transType}> {
${contexts.contextMemberDeclTrans}

		public Factory(${contexts.contextParamTrans}) {
${contexts.contextInitTrans}
		}

		@Override
		public final ${whatSig.outputElement.typerep.transType} invoke(final common.OriginContext originCtx, final Object[] children, final Object[] namedNotApplicable) {
			return ${className}.invoke(${implode(", ",
			  ["originCtx"] ++
			  map(\ c::Context -> decorate c with {boundVariables = whatSig.freeVariables;}.contextRefElem, whatSig.contexts) ++
			  unpackChildren(0, whatSig.inputElements))});
		}
		
		@Override
		public final common.AppTypeRep getType() {
${makeTyVarDecls(3, whatSig.typerep.freeVariables)}
			return ${transFreshTypeRep(whatSig.typerep)};
		}
		
		@Override
		public final String toString() {
			return "${whatGrammar}:${whatName}";
		}
	};
}""";
}

function generateMainClassString
String ::= whatGrammar::String isIOValReturn::Boolean
{
  local attribute package :: String;
  package = makeName(whatGrammar);

  -- Code used if main function return type is IOVal<Integer>
  local attribute invocationIOVal::String = package ++ 
    ".Pmain.invoke(common.OriginContext.ENTRY_CONTEXT, cvargs(args), common.IOToken.singleton)";
	
  -- Code used if main function return type is IO<Integer>
  local attribute invokationEvalIO::String = 
    "silver.core.PevalIO.invoke(common.OriginContext.ENTRY_CONTEXT, " ++ package ++ 
    ".Pmain.invoke(common.OriginContext.ENTRY_CONTEXT, cvargs(args)), common.IOToken.singleton)";

  return s"""
package ${package};

import silver.core.*;

public class Main {
	public static void main(String[] args) {
		common.Util.init();
		${package}.Init.initAllStatics();
		${package}.Init.init();
		${package}.Init.postInit();

		try {
			common.Node rv = (common.Node) ${if isIOValReturn then invocationIOVal else invokationEvalIO};
			common.DecoratedNode drv = rv.decorate();
			drv.synthesized(silver.core.Init.silver_core_io__ON__silver_core_IOVal); // demand the io token
			System.exit( (Integer)drv.synthesized(silver.core.Init.silver_core_iovalue__ON__silver_core_IOVal) );
		} catch(Throwable t) {
			Throwable rt = common.exceptions.SilverException.getRootCause(t);
			if(rt instanceof common.exceptions.SilverExit)
				System.exit(((common.exceptions.SilverExit)rt).getExitCode());
			common.Util.printStackCauses(t);
		}
	}
	public static common.ConsCell cvargs(String[] args) {
		common.ConsCell result = common.ConsCell.nil;
		for(int i = args.length - 1; i >= 0; i--) {
			result = new common.ConsCell(new common.StringCatter(args[i]), result);
		}
		return result;
	}
}""";
}

