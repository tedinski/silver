grammar silver:compiler:translation:java:core;

import silver:compiler:driver;

aspect production productionDcl
top::AGDcl ::= 'abstract' 'production' id::Name d::ProductionImplements ns::ProductionSignature body::ProductionBody
{
  local className :: String = "P" ++ id.name;

  top.setupInh := body.setupInh;
  top.initProd := s"\t\t${className}.initProductionAttributeDefinitions();\n"
               ++ s"\t\tcommon.RTTIManager.registerProduction(${className}.prodleton);\n\n";
  top.postInit := s"";

  top.initWeaving := s"\tpublic static int ${localVar} = 0;\n";
  top.valueWeaving := body.valueWeaving;

  local localVar :: String = "count_local__ON__" ++ makeIdName(fName);
  local ntName :: String = namedSig.outputElement.typerep.typeName;

  local fnnt :: String = makeNTName(ntName);
  local isData :: Boolean = namedSig.outputElement.typerep.isData;
  local wantsTracking :: Boolean = namedSig.outputElement.typerep.isTracked;

  local ntDeclPackage :: String = implode(".", init(explode(".", fnnt)));
  local typeNameSnipped :: String = last(explode(":", namedSig.outputElement.typerep.typeName));

  local decorableChildren :: [NamedSignatureElement] =
    filter(\ x::NamedSignatureElement -> isDecorable(x.typerep, body.env), namedSig.inputElements);

  local undecChild :: (String ::= NamedSignatureElement) =
    \ x::NamedSignatureElement ->
      if x.typerep.isDecorated
      then s"context.childDecoratedLazy(i_${x.elementName})"
      else if isDecorable(x.typerep, body.env)
      then s"context.childUndecoratedLazy(i_${x.elementName})"
      else s"child_${x.elementName}";

  local dupChild :: (String ::= NamedSignatureElement) =
    \ x::NamedSignatureElement ->
      if x.typerep.transType == "Object"
      then s"(getChild_${x.elementName}() instanceof common.Tracked?((common.Tracked)child_${x.elementName}).duplicate(null, notes):child_${x.elementName})"
      else if x.typerep.isTracked
      then s"getChild_${x.elementName}().duplicate(null, notes)"
      else s"child_${x.elementName}";

  local copyChild :: (String ::= NamedSignatureElement) =
    (\x::NamedSignatureElement -> s"child_${x.elementName}");

  local copyAnno :: (String ::= NamedSignatureElement) =
    (\x::NamedSignatureElement -> s"anno_${makeIdName(x.elementName)}");

  local updateAnno :: (String ::= Integer NamedSignatureElement) =
    (\i::Integer x::NamedSignatureElement ->
      s"annos[${toString(i)}] != null? annos[${toString(i)}] : anno_${makeIdName(x.elementName)}");

  local getChildNames :: (String ::= NamedSignatureElement) =
    (\x::NamedSignatureElement -> s"\"${x.elementName}\"");

  local getChildTypes :: (String ::= NamedSignatureElement) =
    (\x::NamedSignatureElement -> case x.typerep of
                                  | nonterminalType(fn, _, _, _) -> s"\"${fn}\""
                                  | _ -> "null"
                                  end);

  local commaIfAny :: String = if length(namedSig.inputElements)!=0 || length(namedSig.namedInputElements)!=0 || length(namedSig.contexts)!=0 then "," else "";

  local contexts::Contexts = foldContexts(namedSig.contexts);
  contexts.boundVariables = namedSig.freeVariables;

  top.genFiles := [(className ++ ".java", s"""
package ${makeName(top.grammarName)};

import silver.core.*;

// ${ntName}
// ${ns.unparse}
public final class ${className} extends ${fnnt} {

${makeIndexDcls(0, namedSig.inputElements)}

    public static final String childNames[] = {${implode(",", map(getChildNames, namedSig.inputElements))}};
    public static final String childTypes[] = {${implode(",", map(getChildTypes, namedSig.inputElements))}};

    public static final int num_local_attrs = Init.${localVar};
    public static final String[] occurs_local = new String[num_local_attrs];

    public static final common.Lazy[] synthesizedAttributes = new common.Lazy[${fnnt}.num_syn_attrs];
    public static final common.Lazy[][] childInheritedAttributes = new common.Lazy[${toString(length(namedSig.inputElements))}][];

    public static final boolean[] localDecorable = new boolean[num_local_attrs];
    public static final common.Lazy[] localAttributes = new common.Lazy[num_local_attrs];
    public static final common.Lazy[] localDecSites = new common.Lazy[num_local_attrs];
    public static final common.Lazy[][] localInheritedAttributes = new common.Lazy[num_local_attrs][];

${if isData then "" else s"""
    public static final common.Lazy[] forwardInheritedAttributes = new common.Lazy[${fnnt}.num_inh_attrs];
    public static final boolean[] localIsForward = new boolean[num_local_attrs];"""}

${namedSig.inhOccursIndexDecls}

    public static final int[] childInhContextTypeVars = {${implode(",", namedSig.childTypeVarElems)}};
    public static final int[] localInhContextTypeVars = new int[num_local_attrs];

    static {
${namedSig.childStatic}
    }

    public ${className}(final NOriginInfo origin, final boolean isUniqueInvocation${commaIfAny} ${namedSig.javaSignature}) {
        super(${implode(", ",
        	(if wantsTracking then ["origin"] else []) ++
        	(if isData then []
             else ["isUniqueInvocation"]) ++
        	map((.annoRefElem), namedSig.namedInputElements))});
${implode("", map(makeChildAssign, namedSig.inputElements))}
${contexts.contextInitTrans}
    }

    public ${className}(final NOriginInfo origin${commaIfAny} ${namedSig.javaSignature}) {
        this(origin, false${if length(namedSig.refInvokeTrans)!=0 then ", " ++ namedSig.refInvokeTrans else ""});
    }

    public ${className}(final boolean isUniqueInvocation${commaIfAny} ${namedSig.javaSignature}) {
        this(null, isUniqueInvocation${if length(namedSig.refInvokeTrans)!=0 then ", " ++ namedSig.refInvokeTrans else ""});
    }

    public ${className}(${namedSig.javaSignature}) {
        this(null${if length(namedSig.refInvokeTrans)!=0 then ", " ++ namedSig.refInvokeTrans else ""});
    }

${namedSig.childDecls}

${contexts.contextMemberDeclTrans}

    @Override
    public final ${className} updateAnnos(final Object[] annos) {
        assert !isUnique;
        if (annos == null) return this;
        assert annos.length == ${toString(length(namedSig.namedInputElements))};
        return new ${className}(${implode(", ",
            -- A node with updated annotations has the same origin as the original node.
            (if wantsTracking then ["this.origin"] else []) ++
            namedSig.contextRefElems ++
            map(copyChild, namedSig.inputElements) ++
            unzipWith(updateAnno, enumerate(namedSig.namedInputElements)))});
    }

	@Override
	public boolean isChildDecorable(final int index) {
		switch(index) {
${implode("", map(makeChildDecorableCase(body.env, _), namedSig.inputElements))}
            default: return false;
        }
    }

	@Override
	public Object getChild(final int index) {
		switch(index) {
${implode("", map(makeChildAccessCase, namedSig.inputElements))}
            default: return null;
        }
    }

    @Override
    public Object getChildLazy(final int index) {
        switch(index) {
${implode("", map(makeChildAccessCaseLazy, namedSig.inputElements))}
            default: return null;
        }
    }

	@Override
	public common.Lazy getChildDecSite(final int index) {
		switch(index) {
${implode("", map(makeChildDecSiteAccessCase(body.env, top.flowEnv, body.frame.lhsNtName, fName, _), namedSig.inputElements))}
            default: return null;
        }
    }

    @Override
    public final int getNumberOfChildren() {
        return ${toString(length(namedSig.inputElements))};
    }

    @Override
    public common.Lazy getSynthesized(final int index) {
        return synthesizedAttributes[index];
    }

    @Override
    public common.Lazy[] getLocalInheritedAttributes(final int key) {
${flatMap(makeInhOccursContextAccess(namedSig.freeVariables, namedSig.contextInhOccurs, "localInhContextTypeVars", "localInheritedAttributes", _), namedSig.inhOccursContextTypes)}
        return localInheritedAttributes[key];
    }

    @Override
    public common.Lazy[] getChildInheritedAttributes(final int key) {
${flatMap(makeInhOccursContextAccess(namedSig.freeVariables, namedSig.contextInhOccurs, "childInhContextTypeVars", "childInheritedAttributes", _), namedSig.inhOccursContextTypes)}
        return childInheritedAttributes[key];
    }

${if isData then "" else s"""
    @Override
    public common.Node evalUndecorate(final common.DecoratedNode context) {
        ${if any(map((.elementShared), namedSig.inputElements))
          then "return context.getForwardParent().undecorate();"
          else if !null(decorableChildren)
          then s"return new ${className}(${implode(", ",
            -- An implicitly undecorated production node has the same origin as the original node.
            -- This will be overidden by duplicate when calling new().
            (if wantsTracking then ["this.origin"] else []) ++
            namedSig.contextRefElems ++
            map(undecChild, namedSig.inputElements) ++
            map(copyAnno, namedSig.namedInputElements))});"
          else "return this;"}
    }

    @Override
    public boolean hasForward() {
        return ${(if null(body.forwardExpr) then "false" else "true")};
    }

    @Override
    public common.Node evalForward(final common.DecoratedNode context) {
        ${if null(body.forwardExpr)
          then s"throw new common.exceptions.SilverInternalError(\"Production ${fName} erroneously claimed to forward\")"
          else s"return ((common.Node)${head(body.forwardExpr).translation}${
            if wantsTracking && !top.config.noRedex
            then s".duplicateForForwarding(context.getNode(), \"${escapeString(getParsedOriginLocationOrFallback(head(body.forwardExpr)).unparse)}\")"
            else ""})"};
    }

    @Override
    public common.Lazy[] getForwardInheritedAttributes() {
        return forwardInheritedAttributes;
    }

    @Override
    public boolean getLocalIsForward(final int key) {
        return localIsForward[key];
    }"""}

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
        return "${fName}";
    }

    ${otImpl}
    
    @Override
    public final common.TypeRep getType() {
${makeTyVarDecls(2, namedSig.typerep.freeVariables)}
        
        ${implode("\n\t\t", map(makeChildUnify(fName, _), namedSig.inputElements))}
        
        return ${transFreshTypeRep(namedSig.outputElement.typerep)};
    }

    static void initProductionAttributeDefinitions() {
${body.translation}
    }

    public static final common.RTTIManager.Prodleton<${className}> prodleton = new Prodleton();

    public static final class Prodleton extends common.RTTIManager.Prodleton<${className}> {
        public ${className} reify(
            final silver.core.NAST origAST,
            final common.ConsCell rules,
            final common.TypeRep resultType,
            final silver.core.NAST[] childASTs,
            final String[] annotationNames,
            final silver.core.NAST[] annotationASTs)
        {
            assert annotationNames.length == annotationASTs.length;
            ${makeAnnoIndexDcls(0, namedSig.namedInputElements)}
            ${makeTyVarDecls(2, namedSig.typerep.freeVariables)}

            common.TypeRep givenType = ${transFreshTypeRep(namedSig.outputElement.typerep)};
            if (!common.TypeRep.unify(resultType, givenType)) {
                throw new common.exceptions.SilverError("reify is constructing " + resultType.toString() + ", but found " + givenType.toString() + " production ${fName} AST.");
            }
            
            if (childASTs.length != ${toString(length(namedSig.inputElements))}) {
                throw new common.exceptions.SilverError("Production ${fName} expected ${toString(length(namedSig.inputElements))} child(ren), but got " + childASTs.length + ".");
            }
            
            String[] expectedAnnotationNames = new String[] {${implode(", ", map((.annoNameElem), annotationsForNonterminal(namedSig.outputElement.typerep, top.env)))}};
            if (!java.util.Arrays.equals(annotationNames, expectedAnnotationNames)) {
                throw new common.exceptions.SilverError("Production ${fName} expected " + common.Util.namesToString(expectedAnnotationNames, "no") + " annotation(s), but got " + common.Util.namesToString(annotationNames, "none") + ".");
            }
            
            ${implode("\n\t\t", map(makeChildReify(fName, length(namedSig.inputElements), _), namedSig.inputElements))}
            ${implode("\n\t\t", map(makeAnnoReify(fName, _), namedSig.namedInputElements))}
            ${namedSig.contextRuntimeResolve}

            return new ${className}(${if wantsTracking then "new silver.core.PoriginOriginInfo(origAST, true, rules, common.OriginsUtil.SET_FROM_REIFICATION_OIT)"++commaIfAny else ""} ${namedSig.refInvokeTrans});
        }

        public ${className} constructDirect(
            final Object[] children,
            final Object[] annos)
        {
            int counter = 0;
            ${implode("\n\t\t", map(makeConstructDirectChildren, namedSig.inputElements))}

            counter = 0;
            ${implode("\n\t\t", map(makeConstructDirectAnno,     namedSig.namedInputElements))}

            ${namedSig.contextRuntimeResolve}

            return new ${className}(${namedSig.refInvokeTrans});
        }

        public String getName(){ return "${fName}"; }
        public common.RTTIManager.Nonterminalton<${fnnt}> getNonterminalton(){ return ${fnnt}.nonterminalton; }

        public String getTypeUnparse() { return "${escapeString(namedSig.typeScheme.typepp)}"; }
        public int getChildCount() { return ${toString(length(namedSig.inputElements))}; }
        public int getAnnoCount() { return ${toString(length(namedSig.namedInputElements))}; }

        public String[] getOccursInh() { return ${className}.occurs_inh; }
        public String[] getChildNames() { return ${className}.childNames; }
        public String[] getChildTypes() { return ${className}.childTypes; }
        public common.Lazy[][] getChildInheritedAttributes() { return ${className}.childInheritedAttributes; }
    }

    public common.RTTIManager.Prodleton<${className}> getProdleton() { return prodleton; }


	${if null(namedSig.contexts) then s"public static final common.NodeFactory<${fnnt}> factory = new Factory();" else ""}

	public static final class Factory extends common.NodeFactory<${fnnt}> {
${contexts.contextMemberDeclTrans}

		public Factory(${contexts.contextParamTrans}) {
${contexts.contextInitTrans}
		}
	
		@Override
        public final ${fnnt} invoke(final common.OriginContext originCtx, final Object[] children, final Object[] annotations) {
            return new ${className}(
              ${implode(", ", (if wantsTracking then [newConstructionOriginUsingCtxRef] else []) ++
                -- If this prod implements a dispatch signature, then it *can* have shared children when invoked.
                (if d.implementsSig.isJust then "true" else "false") ::
                map(\ c::Context -> decorate c with {boundVariables = namedSig.freeVariables;}.contextRefElem, namedSig.contexts) ++
                unpackChildren(0, namedSig.inputElements) ++ unpackAnnotations(0, namedSig.namedInputElements))});
        }
		
        @Override
        public final common.AppTypeRep getType() {
${makeTyVarDecls(3, namedSig.typerep.freeVariables)}
			return ${transFreshTypeRep(namedSig.typerep)};
		}
		
		@Override
		public final String toString() {
			return "${top.grammarName}:${id.name}";
		}
	};

}
""")];

  local otImpl :: String = if wantsTracking then s"""
    @Override
    public ${fnnt} duplicate(common.Node redex, common.ConsCell notes) {
        silver.core.NOriginInfo oi;
        if (redex == null || ${if top.config.noRedex then "true" else "false"}) {
            oi = new PoriginOriginInfo(this, true, notes, common.OriginsUtil.SET_AT_NEW_OIT);
        } else {
            oi = new PoriginAndRedexOriginInfo(this, redex, notes, true, notes, common.OriginsUtil.SET_AT_NEW_OIT);
        }
        return new ${className}(
            ${implode(", ",
                "oi" :: "isUnique" ::
                namedSig.contextRefElems ++
                map(dupChild, namedSig.inputElements) ++
                map(copyAnno, namedSig.namedInputElements))});
    }

    @Override
    public ${fnnt} updateOriginInfo(silver.core.NOriginInfo oi) {
        return new ${className}(
            ${implode(", ",
                "oi" :: "isUnique" ::
                namedSig.contextRefElems ++
                map(copyChild, namedSig.inputElements) ++
                map(copyAnno, namedSig.namedInputElements))});
    }
    """ else "";

  -- main function signature check TODO: this should probably be elsewhere!
  top.errors <-
    if id.name == "main"
    then [errFromOrigin(top, "main should be a function!")]
    else [];
}
