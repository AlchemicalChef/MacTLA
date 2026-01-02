import SwiftUI

struct ContentView: View {
    @EnvironmentObject var appState: AppState
    @StateObject private var documentManager = DocumentManager()
    @State private var showProjectBrowser = false
    @State private var showSymbolNavigator = false
    @State private var showStateGraph = false
    @State private var columnVisibility: NavigationSplitViewVisibility = .all
    @State private var graphStates: [GraphState] = []
    @State private var graphTransitions: [GraphTransition] = []
    @State private var showNewFileDialog = false
    @State private var newFileName = "NewSpec"

    var body: some View {
        NavigationSplitView(columnVisibility: $columnVisibility) {
            ProjectSidebarView()
                .navigationTitle("TLA+")
                #if os(macOS)
                .navigationSplitViewColumnWidth(min: 200, ideal: 250, max: 400)
                #endif
        } detail: {
            EditorDetailView()
        }
        .toolbar {
            #if os(macOS)
            ToolbarItemGroup(placement: .primaryAction) {
                // File operations
                Menu {
                    Button(action: { showProjectBrowser = true }) {
                        Label("Open Project", systemImage: "folder")
                    }
                    Button(action: { openFileDialog() }) {
                        Label("Import File", systemImage: "square.and.arrow.down")
                    }
                    if appState.selectedFile != nil {
                        Button(action: exportCurrentFile) {
                            Label("Export File", systemImage: "square.and.arrow.up")
                        }
                    }
                    Divider()
                    Button(action: { showNewFileDialog = true }) {
                        Label("New Specification", systemImage: "doc.badge.plus")
                    }
                } label: {
                    Label("File", systemImage: "doc")
                }
                .help("File Operations")

                // Tools menu
                Menu {
                    Button(action: { showSymbolNavigator = true }) {
                        Label("Symbol Navigator", systemImage: "list.bullet.indent")
                    }
                    Button(action: translatePlusCal) {
                        Label("Translate PlusCal", systemImage: "arrow.triangle.2.circlepath")
                    }
                    .disabled(appState.selectedFile == nil)

                    Divider()

                    ProofToolbarButton()
                } label: {
                    Label("Tools", systemImage: "wrench.and.screwdriver")
                }
                .help("Tools and Utilities")

                Divider()

                // Verification
                Button(action: runVerification) {
                    Label("Verify", systemImage: "checkmark.shield")
                }
                .disabled(appState.selectedFile == nil || appState.isVerifying)
                .help("Run Model Checker (⌘R)")

                if !appState.verificationResults.isEmpty {
                    Button(action: { showStateGraph = true }) {
                        Label("State Graph", systemImage: "point.3.connected.trianglepath.dotted")
                    }
                    .help("View State Space Graph")
                }
            }
            #else
            ToolbarItemGroup(placement: .primaryAction) {
                // File operations
                Menu {
                    Button(action: { showProjectBrowser = true }) {
                        Label("Open Project", systemImage: "folder")
                    }
                    Button(action: { documentManager.isImporting = true }) {
                        Label("Import File", systemImage: "square.and.arrow.down")
                    }
                    if appState.selectedFile != nil {
                        Button(action: exportCurrentFile) {
                            Label("Export File", systemImage: "square.and.arrow.up")
                        }
                    }
                    Divider()
                    Button(action: { showNewFileDialog = true }) {
                        Label("New Specification", systemImage: "doc.badge.plus")
                    }
                } label: {
                    Label("File", systemImage: "doc")
                }

                // Tools menu
                Menu {
                    Button(action: { showSymbolNavigator = true }) {
                        Label("Symbol Navigator", systemImage: "list.bullet.indent")
                    }
                    Button(action: translatePlusCal) {
                        Label("Translate PlusCal", systemImage: "arrow.triangle.2.circlepath")
                    }
                    .disabled(appState.selectedFile == nil)

                    Divider()

                    ProofToolbarButton()
                } label: {
                    Label("Tools", systemImage: "wrench.and.screwdriver")
                }

                Divider()

                // Verification
                Button(action: runVerification) {
                    Label("Verify", systemImage: "checkmark.shield")
                }
                .disabled(appState.selectedFile == nil || appState.isVerifying)

                if !appState.verificationResults.isEmpty {
                    Button(action: { showStateGraph = true }) {
                        Label("State Graph", systemImage: "point.3.connected.trianglepath.dotted")
                    }
                }
            }
            #endif
        }
        .sheet(isPresented: $showProjectBrowser) {
            ProjectBrowserView()
        }
        .sheet(isPresented: $showSymbolNavigator) {
            NavigationStack {
                if let file = appState.selectedFile {
                    SymbolListView(
                        symbols: SymbolNavigator.shared.extractSymbols(from: file.content),
                        onSelect: { symbol in
                            navigateToSymbol(symbol)
                            showSymbolNavigator = false
                        }
                    )
                    .navigationTitle("Symbols")
                    .toolbar {
                        ToolbarItem(placement: .cancellationAction) {
                            Button("Done") { showSymbolNavigator = false }
                        }
                    }
                } else {
                    ContentUnavailableView(
                        "No File Selected",
                        systemImage: "doc.text",
                        description: Text("Select a file to view its symbols")
                    )
                }
            }
            #if os(macOS)
            .frame(minWidth: 400, minHeight: 500)
            #endif
        }
        .sheet(isPresented: $showStateGraph) {
            NavigationStack {
                StateGraphView(states: graphStates, transitions: graphTransitions)
                    .toolbar {
                        ToolbarItem(placement: .cancellationAction) {
                            Button("Done") { showStateGraph = false }
                        }
                    }
            }
            #if os(macOS)
            .frame(minWidth: 600, minHeight: 500)
            #endif
        }
        #if !os(macOS)
        .documentImporter(isPresented: $documentManager.isImporting) { urls in
            documentManager.importFiles(from: urls, into: appState)
        }
        .fileExporter(
            isPresented: $documentManager.isExporting,
            document: TLADocument(content: documentManager.exportFile?.content ?? ""),
            contentType: .plainText,
            defaultFilename: documentManager.exportFile?.name ?? "Spec.tla"
        ) { result in
            switch result {
            case .success(let url):
                print("Exported to: \(url)")
            case .failure(let error):
                documentManager.errorMessage = error.localizedDescription
                documentManager.showError = true
            }
            documentManager.exportFile = nil
        }
        #endif
        .alert("Error", isPresented: $documentManager.showError) {
            Button("OK", role: .cancel) {}
        } message: {
            Text(documentManager.errorMessage ?? "An unknown error occurred")
        }
        .alert("New Specification", isPresented: $showNewFileDialog) {
            TextField("File name", text: $newFileName)
            Button("Cancel", role: .cancel) {
                newFileName = "NewSpec"
            }
            Button("Create") {
                createNewFile(named: newFileName)
                newFileName = "NewSpec"
            }
        } message: {
            Text("Enter a name for the new TLA+ specification")
        }
        .onReceive(NotificationCenter.default.publisher(for: .showNewFileDialog)) { _ in
            showNewFileDialog = true
        }
    }

    #if os(macOS)
    private func openFileDialog() {
        let panel = NSOpenPanel()
        panel.allowsMultipleSelection = true
        panel.canChooseDirectories = false
        panel.canChooseFiles = true
        panel.allowedContentTypes = [.plainText]

        if panel.runModal() == .OK {
            documentManager.importFiles(from: panel.urls, into: appState)
        }
    }
    #endif

    private func runVerification() {
        guard let file = appState.selectedFile else { return }
        Task {
            appState.isVerifying = true
            defer { appState.isVerifying = false }

            // Find associated .cfg file or use default config
            let config = findConfig(for: file)

            // Convert TLCConfig to ModelChecker parameters
            let checkerConfig = ModelChecker.Configuration(
                workers: config.workers,
                maxStates: config.maxStates,
                maxDepth: config.maxDepth,
                checkDeadlock: config.checkDeadlock,
                checkInvariants: true,
                checkProperties: !config.properties.isEmpty,
                checkLiveness: !config.properties.isEmpty || config.properties.isEmpty, // Check liveness by default
                simulationMode: config.simulationMode,
                simulationTraceCount: config.simulationTraceCount,
                simulationTraceDepth: config.simulationTraceDepth
            )

            // Convert constants
            let constants = config.constants.filter { !$0.name.isEmpty && !$0.value.isEmpty }.map {
                ModelChecker.ConstantOverride(name: $0.name, value: $0.value)
            }

            // Convert invariants
            let invariants = config.invariants.filter { !$0.name.isEmpty }.map {
                ModelChecker.InvariantSpec(name: $0.name)
            }

            // Convert properties
            let properties = config.properties.filter { !$0.name.isEmpty }.map {
                ModelChecker.PropertySpec(name: $0.name)
            }

            // Convert state constraints
            let constraints = config.constraints.filter { !$0.expression.isEmpty }.map {
                ModelChecker.ConstraintSpec(expression: $0.expression)
            }

            // Convert action constraints
            let actionConstraints = config.actionConstraints.filter { !$0.expression.isEmpty }.map {
                ModelChecker.ActionConstraintSpec(expression: $0.expression)
            }

            // Convert view
            let view: ModelChecker.ViewSpec? = config.view.isEmpty ? nil : ModelChecker.ViewSpec(expression: config.view)

            // Convert symmetry sets
            let symmetrySets = config.symmetrySets.filter { !$0.name.isEmpty }.map {
                ModelChecker.SymmetrySetSpec(name: $0.name)
            }

            let checker = ModelChecker()
            let result = await checker.verify(
                specification: file.content,
                config: checkerConfig,
                constants: constants,
                invariants: invariants,
                properties: properties,
                constraints: constraints,
                actionConstraints: actionConstraints,
                view: view,
                symmetrySets: symmetrySets
            )
            appState.verificationResults.append(result)

            // Write verification result to Validator.txt
            writeValidatorLog(result: result, fileName: file.name)

            // Build graph for visualization (simplified)
            if result.status == .success || result.status == .failure {
                buildStateGraph(from: result)
            }
        }
    }

    /// Finds the configuration for a given file
    private func findConfig(for file: TLAFile) -> TLCConfig {
        // Look for a .cfg file with matching name
        let baseName = file.name.replacingOccurrences(of: ".tla", with: "")
        let cfgFileName = baseName + ".cfg"

        // Check in current project's files
        if let project = appState.currentProject {
            if let cfgFile = project.files.first(where: { $0.name == cfgFileName && $0.type == .model }) {
                return TLCConfig.parse(from: cfgFile.content)
            }
        }

        // Check in open files
        if let cfgFile = appState.openFiles.first(where: { $0.name == cfgFileName && $0.type == .model }) {
            return TLCConfig.parse(from: cfgFile.content)
        }

        // Return default config
        return TLCConfig()
    }

    private func buildStateGraph(from result: VerificationResult) {
        // Use actual exploration result from model checker
        if let exploration = result.explorationResult {
            var states: [GraphState] = []
            var transitions: [GraphTransition] = []
            var hashToGraphId: [StateHash: UUID] = [:]

            // Limit states for visualization (max 100 for performance)
            let maxStates = min(exploration.states.count, 100)

            // Create graph states from exploration result
            for (index, tlaState) in exploration.states.prefix(maxStates).enumerated() {
                let hash = tlaState.hash
                let graphState = GraphState(
                    label: "S\(index)",
                    variables: tlaState.variables.mapValues { $0.description },
                    isInitial: exploration.initialStates.contains(hash),
                    isError: exploration.errorStates.contains(hash)
                )
                states.append(graphState)
                hashToGraphId[hash] = graphState.id
            }

            // Create transitions from exploration result
            for transition in exploration.transitions {
                if let fromId = hashToGraphId[transition.fromHash],
                   let toId = hashToGraphId[transition.toHash] {
                    // Avoid duplicate transitions
                    if !transitions.contains(where: { $0.fromId == fromId && $0.toId == toId }) {
                        transitions.append(GraphTransition(
                            fromId: fromId,
                            toId: toId,
                            action: transition.action
                        ))
                    }
                }
            }

            // Layout the graph
            GraphLayoutEngine.layout(states: &states, transitions: transitions)

            graphStates = states
            graphTransitions = transitions
        } else {
            // Fallback to minimal graph if no exploration data
            graphStates = [GraphState(
                label: "S0",
                variables: ["status": result.status.rawValue],
                isInitial: true,
                isError: result.status == .failure
            )]
            graphTransitions = []
        }
    }

    private func createNewFile(named name: String) {
        var fileName = name.trimmingCharacters(in: .whitespaces)
        if fileName.isEmpty {
            fileName = "NewSpec"
        }
        if !fileName.hasSuffix(".tla") {
            fileName += ".tla"
        }
        let newFile = TLAFile(
            name: fileName,
            type: .specification,
            content: TLATemplates.basicSpecification
        )
        appState.openFile(newFile)
        if appState.currentProject != nil {
            appState.currentProject?.files.append(newFile)
        }
    }

    private func exportCurrentFile() {
        guard let file = appState.selectedFile else { return }

        #if os(macOS)
        let panel = NSSavePanel()
        panel.nameFieldStringValue = file.name
        panel.allowedContentTypes = [.plainText]

        if panel.runModal() == .OK, let url = panel.url {
            documentManager.exportFile(file, to: url)
        }
        #else
        documentManager.exportFile = file
        documentManager.isExporting = true
        #endif
    }

    private func translatePlusCal() {
        guard let fileIndex = appState.openFiles.firstIndex(where: { $0.id == appState.selectedFileId }) else {
            return
        }

        let translator = PlusCalTranslator()
        let result = translator.translate(appState.openFiles[fileIndex].content)

        if result.isSuccess {
            appState.openFiles[fileIndex].content = result.tlaSpec
            appState.openFiles[fileIndex].hasUnsavedChanges = true
        }
    }

    private func navigateToSymbol(_ symbol: SymbolNavigator.Symbol) {
        // Post notification to scroll editor to symbol location
        NotificationCenter.default.post(
            name: .navigateToLine,
            object: symbol.location
        )
    }

    /// Writes verification result to Validator.txt for debugging/analysis
    private func writeValidatorLog(result: VerificationResult, fileName: String) {
        let timestamp = ISO8601DateFormatter().string(from: Date())
        var log = """
        ================================================================================
        [\(timestamp)] Verification: \(fileName)
        ================================================================================
        Specification: \(result.specificationName)
        Status: \(result.status.rawValue)
        States Explored: \(result.statesExplored)
        Distinct States: \(result.distinctStates)
        Duration: \(String(format: "%.2f", result.duration))s

        """

        if let error = result.error {
            log += "Error: \(error)\n"
        }

        if let violated = result.violatedInvariant {
            log += "\nViolated Invariant: \(violated)\n"
        }

        if let details = result.errorDetails {
            log += "\nError Details:\n"
            log += "  Kind: \(details.kind)\n"
            log += "  Message: \(details.message)\n"
            if let location = details.location {
                log += "  Location: Line \(location.line), Column \(location.column)\n"
            }
            if let context = details.context {
                log += "  Context: \(context)\n"
            }
            if !details.suggestions.isEmpty {
                log += "  Suggestions:\n"
                for suggestion in details.suggestions {
                    log += "    - \(suggestion)\n"
                }
            }
        }

        if !result.counterexample.isEmpty {
            log += "\nCounterexample Trace:\n"
            for (index, traceState) in result.counterexample.enumerated() {
                log += "  Step \(traceState.stepNumber): \(traceState.action)\n"
                for (varName, value) in traceState.variables.sorted(by: { $0.key < $1.key }) {
                    log += "    \(varName) = \(value)\n"
                }
            }
        }

        if !result.output.isEmpty {
            log += "\nOutput:\n\(result.output)\n"
        }

        log += "\n"

        // Write to file
        let path = "/Users/night/Documents/GitHub/MacTLA/Validator.txt"
        if let data = log.data(using: String.Encoding.utf8) {
            if FileManager.default.fileExists(atPath: path) {
                if let handle = FileHandle(forWritingAtPath: path) {
                    handle.seekToEndOfFile()
                    handle.write(data)
                    handle.closeFile()
                }
            } else {
                FileManager.default.createFile(atPath: path, contents: data)
            }
        }
    }
}

// Notification names moved to Utilities/NotificationNames.swift

#Preview {
    ContentView()
        .environmentObject(AppState())
}
