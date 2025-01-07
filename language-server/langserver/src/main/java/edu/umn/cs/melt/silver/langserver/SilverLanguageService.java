package edu.umn.cs.melt.silver.langserver;

import java.io.File;
import java.net.URI;
import java.net.URISyntaxException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import org.eclipse.lsp4j.ApplyWorkspaceEditParams;
import org.eclipse.lsp4j.ConfigurationItem;
import org.eclipse.lsp4j.ConfigurationParams;
import org.eclipse.lsp4j.CreateFilesParams;
import org.eclipse.lsp4j.DeclarationParams;
import org.eclipse.lsp4j.DeleteFilesParams;
import org.eclipse.lsp4j.Diagnostic;
import org.eclipse.lsp4j.DidChangeConfigurationParams;
import org.eclipse.lsp4j.DidChangeTextDocumentParams;
import org.eclipse.lsp4j.DidChangeWatchedFilesParams;
import org.eclipse.lsp4j.DidCloseTextDocumentParams;
import org.eclipse.lsp4j.DidOpenTextDocumentParams;
import org.eclipse.lsp4j.DidSaveTextDocumentParams;
import org.eclipse.lsp4j.ExecuteCommandParams;
import org.eclipse.lsp4j.FileCreate;
import org.eclipse.lsp4j.Location;
import org.eclipse.lsp4j.LocationLink;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.PublishDiagnosticsParams;
import org.eclipse.lsp4j.Range;
import org.eclipse.lsp4j.ReferenceParams;
import org.eclipse.lsp4j.RenameFilesParams;
import org.eclipse.lsp4j.SemanticTokens;
import org.eclipse.lsp4j.SemanticTokensParams;
import org.eclipse.lsp4j.TextDocumentContentChangeEvent;
import org.eclipse.lsp4j.TextEdit;
import org.eclipse.lsp4j.WorkspaceEdit;
import org.eclipse.lsp4j.WorkspaceFolder;
import org.eclipse.lsp4j.jsonrpc.CompletableFutures;
import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.eclipse.lsp4j.services.LanguageClient;
import org.eclipse.lsp4j.services.TextDocumentService;
import org.eclipse.lsp4j.services.WorkspaceService;

import com.google.gson.JsonElement;
import com.google.gson.JsonPrimitive;

import common.SilverCopperParser;
import edu.umn.cs.melt.lsp4jutil.CopperParserNodeFactory;
import edu.umn.cs.melt.lsp4jutil.CopperSemanticTokenEncoder;
import edu.umn.cs.melt.lsp4jutil.Util;
import silver.compiler.definition.core.NFile;

/**
 * Implementation of LSP text document and workspace services for Silver.
 * 
 * @author krame505
 */
public class SilverLanguageService implements TextDocumentService, WorkspaceService {
    private LanguageClient client;
    private List<WorkspaceFolder> folders;
    private Map<String, String> fileContents = new HashMap<>();
    private Map<String, Integer> fileVersions = new HashMap<>();
    private Map<String, Integer> savedVersions = new HashMap<>();
    private boolean buildInProgress = false, buildTriggered = false, cleanRequested = false, mwdaEnabled = false;
    private Set<String> grammarDirs = new HashSet<>();
    private Set<String> buildGrammars = new HashSet<>();

    public void setClient(LanguageClient client) {
        this.client = client;
    }

    public void setWorkspaceFolders(List<WorkspaceFolder> folders) {
        this.folders = folders;
        refreshWorkspace();
    }

    @Override
    public void didOpen(DidOpenTextDocumentParams params) {
        // System.err.println("Opened " + params);
        String uri = params.getTextDocument().getUri();
        fileContents.put(uri, params.getTextDocument().getText());
        fileVersions.put(uri, params.getTextDocument().getVersion());
        savedVersions.put(uri, params.getTextDocument().getVersion());
        triggerBuild();
    }

    @Override
    public void didChange(DidChangeTextDocumentParams params) {
        // System.err.println("Changed " + params);
        String uri = params.getTextDocument().getUri();
        for (TextDocumentContentChangeEvent change : params.getContentChanges()) {
            fileContents.put(uri, change.getText());
            fileVersions.put(uri, params.getTextDocument().getVersion());
        }
    }

    @Override
    public void didClose(DidCloseTextDocumentParams params) {
        // System.err.println("Closed " + params);
        String uri = params.getTextDocument().getUri();
        fileContents.remove(uri);
        fileVersions.remove(uri);
        savedVersions.remove(uri);
    }

    @Override
    public void didSave(DidSaveTextDocumentParams params) {
        // System.err.println("Saved " + params);
        String uri = params.getTextDocument().getUri();
        if (!fileVersions.containsKey(uri)) {
            throw new IllegalStateException("File saved before it was changed");
        }
        savedVersions.put(uri, fileVersions.get(uri));
        triggerBuild();
    }

    @Override
    public CompletableFuture<Object> executeCommand(ExecuteCommandParams params) {
        switch (params.getCommand()) {
        case "silver.clean":
            cleanRequested = true;
            triggerBuild();
            return null;
        }
        throw new UnsupportedOperationException("Unsupported command " + params.getCommand());
    }

    @Override
    public void didChangeConfiguration(DidChangeConfigurationParams params) {

    }

    @Override
    public void didChangeWatchedFiles(DidChangeWatchedFilesParams params) {

    }

    @Override
    public void didCreateFiles(CreateFilesParams params) {
        Map<String, List<TextEdit>> edits = new HashMap<>();
        for (FileCreate f : params.getFiles()) {
            if (!f.getUri().endsWith(".md")) {
                SilverUtil.uriToGrammar(f.getUri()).ifPresent(grammar -> {
                    String grammarDecl = "grammar " + grammar + ";\n\n";
                    TextEdit edit = new TextEdit(new Range(new Position(0, 0), new Position(0, 0)), grammarDecl);
                    edits.put(f.getUri(), List.of(edit));
                });
            }
        }
        client.applyEdit(new ApplyWorkspaceEditParams(new WorkspaceEdit(edits)));
        refreshWorkspace();
    }

    @Override
    public void didDeleteFiles(DeleteFilesParams params) {
        refreshWorkspace();
    }

    @Override
    public void didRenameFiles(RenameFilesParams params) {
        refreshWorkspace();
    }

    @Override
    public CompletableFuture<Either<List<? extends Location>, List<? extends LocationLink>>> declaration(DeclarationParams params) {
        return CompletableFutures.computeAsync((cancelChecker) -> {
            String fileName = "";
            try {
                fileName = new URI(params.getTextDocument().getUri()).getPath();
            } catch (URISyntaxException e) {
                e.printStackTrace();
            }
            return Either.forLeft(SilverCompiler.getInstance()
                .getDeclaration(fileName, params.getPosition().getLine() + 1, params.getPosition().getCharacter())
                .stream()
                .map((loc) -> new Location("file://" + Util.locationToFile(loc), Util.locationToRange(loc)))
                .collect(Collectors.toList()));
        });
    }

    @Override
    public CompletableFuture<List<? extends Location>> references(ReferenceParams params) {
        return CompletableFutures.computeAsync((cancelChecker) -> {
            String fileName = "";
            try {
                fileName = new URI(params.getTextDocument().getUri()).getPath();
            } catch (URISyntaxException e) {
                e.printStackTrace();
            }
            return SilverCompiler.getInstance()
                .getReferences(fileName, params.getPosition().getLine() + 1, params.getPosition().getCharacter())
                .stream()
                .map((loc) -> new Location("file://" + Util.locationToFile(loc), Util.locationToRange(loc)))
                .collect(Collectors.toList());
        });
    }

    public static final List<String> tokenTypes = Arrays.asList(new String[] {
        "namespace", "type", "interface", "class", "typeParameter", "parameter", "variable", "function",
        "keyword", "modifier", "comment", "string", "number", "regexp", "operator", "macro"
    });
    public static final List<String> tokenModifiers = Arrays.asList(new String[] {
        "declaration", "definition", "documentation", "defaultLibrary", "modification"
    });

    private CopperSemanticTokenEncoder semanticTokenEncoder = null;
    private CopperParserNodeFactory parserFn = null;
    public void setParserFactory(Supplier<SilverCopperParser<NFile>> parserFactory) {
        semanticTokenEncoder = new CopperSemanticTokenEncoder(parserFactory, tokenTypes, tokenModifiers);
        parserFn = new CopperParserNodeFactory(parserFactory);
    }

    @Override
    public CompletableFuture<SemanticTokens> semanticTokensFull(SemanticTokensParams params) {
        if (semanticTokenEncoder == null) {
            throw new IllegalStateException("Semantic tokens requested when parser has not been initialized");
        }

        String uri = params.getTextDocument().getUri();
        return CompletableFutures.computeAsync((cancelChecker) -> {
            List<Integer> tokens;
            int requestVersion;
            // Recompute tokens if the file is changed while tokens are being computed
            do {
                requestVersion = fileVersions.get(uri);
                if (fileContents.containsKey(uri)) {
                    tokens = semanticTokenEncoder.parseTokens(fileContents.get(uri));
                } else {
                    tokens = new ArrayList<Integer>();
                }
            } while (requestVersion != fileVersions.get(uri));
            return new SemanticTokens(tokens);
        });
    }

    private void refreshWorkspace() {
        grammarDirs.clear();
        buildGrammars.clear();

        for (WorkspaceFolder folder : folders) {
            URI uri;
            try {
                uri = new URI(folder.getUri());
            } catch (URISyntaxException e) {
                throw new IllegalArgumentException("Invalid URI", e);
            }
            findGrammars(new File(uri));
        }

        triggerBuild();
    }

    private void findGrammars(File root) {
        // Workaround to avoid copied resource grammars in the maven build
        // directory in this LSP plugin under the Silver repo.
        // We might want to add a more intelligent way of specifying grammars to
        // exclude in case duplicates are found.
        if (root.getPath().contains("/target/classes/")) return;

        for (File file : root.listFiles()) {
            if (file.isDirectory()) {
                findGrammars(file);
            } else if (SilverUtil.isValidSilverFileName(file.getName())) {
                Optional<String> fileGrammar = SilverUtil.uriToGrammar("file://" + file.getAbsolutePath());
                fileGrammar.ifPresent(buildGrammars::add);
                fileGrammar.ifPresent(grammar -> grammarDirs.add(
                    root.getAbsolutePath().replace("/", ":").replace(".", ":")
                    .split(grammar, 2)[0].replace(":", "/")));
            }
        }
    }

    public synchronized void triggerBuild() {
        buildTriggered = true;
        if (!buildInProgress && parserFn != null) {
            buildInProgress = true;
            new Thread(this::doBuild).start();
        }
    }

    private void doBuild() {
        while(true) {
            Map<String, Integer> buildVersions;
            synchronized (this) {
                buildTriggered = false;
                buildVersions = new HashMap<>(savedVersions);
            }
            if (parserFn == null) {
                throw new IllegalStateException("Build requested when parser has not been loaded");
            }

            // Check the config for whether the MWDA is enabled
            ConfigurationItem enableMWDAConfigItem = new ConfigurationItem();
            enableMWDAConfigItem.setSection("silver.enableMWDA");
            ConfigurationParams configParams = new ConfigurationParams(List.of(enableMWDAConfigItem));
            boolean enableMWDA = mwdaEnabled;
            try {
                Object configMWDAGet = client.configuration(configParams).get().get(0);
                if (configMWDAGet != null && !((JsonElement)configMWDAGet).isJsonNull()) {
                    enableMWDA = ((JsonPrimitive)configMWDAGet).getAsBoolean();
                }
            } catch (InterruptedException | ExecutionException e) {
                // Ignore, getting the settings sometimes fails when a build is triggered during initialization
            }

            boolean cleanBuild = cleanRequested;
            if (enableMWDA && !mwdaEnabled) {
                // Do a clean build when the MWDA is initially enabled
                cleanBuild = true;
            }
            mwdaEnabled = enableMWDA;
            cleanRequested = false;
    
            SilverCompiler.getInstance().build(
                parserFn, grammarDirs, buildGrammars, cleanBuild, enableMWDA,
                (String uri, List<Diagnostic> diagnostics) ->
                    client.publishDiagnostics(new PublishDiagnosticsParams(uri, diagnostics, buildVersions.get(uri))));
            synchronized (this) {
                if (!buildTriggered) {
                    buildInProgress = false;
                    break;
                }
            }
        }
    }
}
