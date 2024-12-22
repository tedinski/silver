grammar silver:compiler:modification:concisefunctions:java;

aspect production shortFunctionDcl
top::AGDcl ::= _ id::Name ns::FunctionSignature '=' e::Expr ';'
{
  local className :: String = "P" ++ escapeName(id.name, top.genFilesUnescapedDown);
  local commaIfArgs :: String = if length(namedSig.contexts) + length(namedSig.inputElements) != 0 then "," else "";

  local contexts::Contexts = foldContexts(namedSig.contexts);
  contexts.boundVariables = namedSig.freeVariables;

  -- This mirrors normal function translation, except that it doesn't inherit from Node.
  top.genFilesUnescapedUp := [id.name];
  top.genFiles := [(className ++ ".java", s"""
package ${makeName(top.grammarName)};

import silver.core.*;

// ${ns.unparse}
public final class ${className} {

	public static ${namedSig.outputElement.typerep.transType} invoke(final common.OriginContext originCtx ${commaIfArgs} ${namedSig.javaSignature}) {
		final common.DecoratedNode context = common.TopNode.singleton;
		try {
			//${e.unparse}
			return ${e.translation};
		} catch(Throwable t) {
			throw new common.exceptions.TraceException("Error while evaluating function ${namedSig.fullName}", t);
		}
	}

${if null(namedSig.contexts) -- Can only use a singleton when there aren't contexts.
  then s"""
	public static final common.NodeFactory<${namedSig.outputElement.typerep.transCovariantType}> factory = new Factory();
""" else s"""
	public static final common.NodeFactory<${namedSig.outputElement.typerep.transCovariantType}> getFactory(${contexts.contextParamTrans}) {
		return new Factory(${implode(", ", map(\ c::Context -> decorate c with {boundVariables = namedSig.freeVariables;}.contextRefElem, namedSig.contexts))});
	}
"""}

	public static final class Factory extends common.NodeFactory<${namedSig.outputElement.typerep.transType}> {
${contexts.contextMemberDeclTrans}

		public Factory(${contexts.contextParamTrans}) {
${contexts.contextInitTrans}
		}

		@Override
		public final ${namedSig.outputElement.typerep.transType} invoke(final common.OriginContext originCtx, final Object[] children, final Object[] namedNotApplicable) {
			return ${className}.invoke(${implode(", ",
			  ["originCtx"] ++
			  map(\ c::Context -> decorate c with {boundVariables = namedSig.freeVariables;}.contextRefElem, namedSig.contexts) ++
			  unpackChildren(0, namedSig.inputElements))});
		}
		
		@Override
		public final common.AppTypeRep getType() {
${makeTyVarDecls(3, namedSig.typerep.freeVariables)}
			return ${transFreshTypeRep(namedSig.typerep)};
		}
		
		@Override
		public final String toString() {
			return "${fName}";
		}
	};

}
""")];
}

aspect production shortFunParamReference
top::Expr ::= @q::QName
{
  top.translation = s"common.Util.<${top.finalType.transType}>demand(${top.lazyTranslation})";
  top.lazyTranslation = "c_" ++ q.lookupValue.fullName;
  top.initTransDecSites := "";
}
