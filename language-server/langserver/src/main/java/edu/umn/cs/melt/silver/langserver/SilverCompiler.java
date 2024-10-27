package edu.umn.cs.melt.silver.langserver;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.stream.Collectors;

import org.eclipse.lsp4j.Diagnostic;

import common.ConsCell;
import common.DecoratedNode;
import common.OriginContext;
import common.StringCatter;
import common.javainterop.ConsCellCollection;
import edu.umn.cs.melt.lsp4jutil.CopperParserNodeFactory;
import edu.umn.cs.melt.lsp4jutil.Util;
import silver.compiler.driver.PbuildRun;
import silver.compiler.driver.PparseArgsOrError;
import silver.compiler.driver.util.NBuildEnv;
import silver.compiler.driver.util.NCompilation;
import silver.compiler.driver.util.PbuildEnv;
import silver.compiler.driver.util.PwriteInterface;
import silver.compiler.langserver.PfindDeclLocation;
import silver.compiler.langserver.PfindReferences;
import silver.core.NLocation;
import silver.core.NPair;
import silver.core.PunsafeEvalIO;

/**
 * Abstraction over the Silver compiler, to perform builds and query information from the most recent build.
 * 
 * @author krame505
 */
public class SilverCompiler {
    private NCompilation comp = null;
    private String silverGen;
    private String stdLibGrammarsDir;

    private SilverCompiler() {
        try {
            silverGen = Files.createTempDirectory("silver_generated").toString() + "/";
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private static SilverCompiler instance;
    public static SilverCompiler getInstance() {
        if (instance == null) {
            instance = new SilverCompiler();
        }
        return instance;
    }

    public void setStdLibGrammarsDir(Path stdLibGrammars) {
        this.stdLibGrammarsDir = stdLibGrammars.toString() + "/";
    }

    public void build(
            CopperParserNodeFactory parserFn, Collection<String> grammarDirs, Collection<String> buildGrammars,
            boolean cleanBuild, boolean enableMWDA, BiConsumer<String, List<Diagnostic>> reportDiagnostics) {
        System.err.println("Building");
        String silverHome = "";  // Not needed since we aren't doing translation
        List<String> args = new ArrayList<>();
        List<String> grammarPath = new ArrayList<>(grammarDirs);
        List<String> silverHostGen = List.of(silverGen);

        if (stdLibGrammarsDir == null) {
            throw new IllegalStateException("Silver host grammars path not set");
        }

        if (enableMWDA) {
            System.err.println("MWDA enabled");
            args.add("--warn-all");
        }

        // Clean build if requested
        if (cleanBuild) {
            System.err.println("Clean build");
            args.add("--clean");
        }

        // Add the silver resource grammars to the end of the grammar path,
        // so if silver is in the workspace we will find it there first.
        grammarPath.add(stdLibGrammarsDir);

        // Set up the build environment
        NBuildEnv benv = new PbuildEnv(
            ConsCellCollection.fromStringList(grammarPath),
            new StringCatter(silverGen),
            new StringCatter(silverHome),
            ConsCellCollection.fromStringList(silverHostGen)
        );
        DecoratedNode a = PparseArgsOrError.invoke(OriginContext.FFI_CONTEXT, ConsCellCollection.fromStringList(args));

        // Build!
        NCompilation comp = (NCompilation)PunsafeEvalIO.invoke(OriginContext.FFI_CONTEXT,
            PbuildRun.invoke(OriginContext.FFI_CONTEXT,
                parserFn, a, benv,
                ConsCellCollection.fromIterator(buildGrammars.stream().<StringCatter>map(StringCatter::new).iterator())));

        // Note that we must demand allGrammars from comp before demanding
        // recompiledGrammars to ensure that IO happens properly,
        // due to the circularity in the driver involving unsafeInterleaveIO.
        Collection<DecoratedNode> allGrammars = new ConsCellCollection<>(
            comp.synthesized(silver.compiler.driver.util.Init.silver_compiler_driver_util_allGrammars__ON__silver_compiler_driver_util_Compilation));
        Collection<DecoratedNode> recompiledGrammars = new ConsCellCollection<>(
            comp.synthesized(silver.compiler.driver.util.Init.silver_compiler_driver_util_recompiledGrammars__ON__silver_compiler_driver_util_Compilation));

        // Check that we built all triggered grammars.
        Set<String> builtGrammars = allGrammars.stream()
            .map(r -> r.synthesized(silver.compiler.driver.util.Init.silver_compiler_definition_env_declaredName__ON__silver_compiler_driver_util_RootSpec).toString())
            .collect(Collectors.toSet());
        for (String grammar : buildGrammars) {
            if (!builtGrammars.contains(grammar)) {
                System.err.println("Failed to find triggered grammar " + grammar);
            }
        }

        // Report diagnostics
        System.err.println("Reporting diagnostics");
        for (DecoratedNode r : allGrammars) {
            String grammarSource =
                r.synthesized(silver.compiler.driver.util.Init.silver_compiler_definition_env_grammarSource__ON__silver_compiler_driver_util_RootSpec).toString();

            Collection<NPair> allFileErrors = new ConsCellCollection<>(
                r.synthesized(silver.compiler.driver.util.Init.silver_compiler_definition_core_allFileErrors__ON__silver_compiler_driver_util_RootSpec));
            for (NPair fileErrors : allFileErrors) {
                String fileName = fileErrors.getAnno_silver_core_fst().toString();
                ConsCell messages = (ConsCell)fileErrors.getAnno_silver_core_snd();
                String uri = "file://" + grammarSource + fileName;

                // System.err.println("Reporting diagnostics for " + grammarSource + fileName);
                reportDiagnostics.accept(uri, Util.messagesToDiagnostics(messages, uri));
            }
        }

        // Write updated interface files
        System.err.println("Writing interface files");
        for (DecoratedNode r : recompiledGrammars) {
            PunsafeEvalIO.invoke(OriginContext.FFI_CONTEXT,
                PwriteInterface.invoke(OriginContext.FFI_CONTEXT, new StringCatter(silverGen), r));
        }

        // Only update the compilation result once we are done reporting errors, to avoid race conditions from other attributes being demanded
        this.comp = comp;
    }
    
    public Collection<NLocation> getDeclaration(String fileName, int line, int col) {
        if (comp == null) {
            return List.of();
        }
        return new ConsCellCollection<NLocation>(
            PfindDeclLocation.invoke(OriginContext.FFI_CONTEXT, new StringCatter(fileName), line, col, comp));
    }
    
    public Collection<NLocation> getReferences(String fileName, int line, int col) {
        if (comp == null) {
            return List.of();
        }
        return new ConsCellCollection<NLocation>(
            PfindReferences.invoke(OriginContext.FFI_CONTEXT, new StringCatter(fileName), line, col, comp));
    }
}
