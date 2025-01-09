package edu.umn.cs.melt.lsp4jutil;

import java.util.function.Supplier;

import common.AppTypeRep;
import common.BaseTypeRep;
import common.FunctionTypeRep;
import common.NodeFactory;
import common.OriginContext;
import common.SilverCopperParser;
import common.exceptions.TraceException;
import common.Util;
import silver.core.NParseResult;

/**
* A wrapper to treat a Silver-generated Copper parser as a Silver function.
* 
* @author krame505
*/
public class CopperParserNodeFactory extends NodeFactory<NParseResult> {
    private Supplier<? extends SilverCopperParser<?>> parserFactory;

    public CopperParserNodeFactory(Supplier<? extends SilverCopperParser<?>> parserFactory) {
        this.parserFactory = parserFactory;
    }

    @Override
    public AppTypeRep getType() {
        return new AppTypeRep(new AppTypeRep(new AppTypeRep(new FunctionTypeRep(2, new String[] {}), new BaseTypeRep("String")), new BaseTypeRep("String")), new AppTypeRep(new BaseTypeRep("silver:core:ParseResult"), new BaseTypeRep("silver:compiler:definition:core:File")));
    }

    @Override
    public NParseResult invoke(OriginContext originCtx, Object[] args, Object[] namedArgs) {
		try {
            return Util.callCopperParser(parserFactory.get(), args[0], args[1]);
		} catch(Throwable t) {
			throw new TraceException("Error while invoking Copper parser", t);
		}
    }
    
}
