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
                    Button(action: createNewFile) {
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
                    Button(action: createNewFile) {
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
        #endif
        .alert("Error", isPresented: $documentManager.showError) {
            Button("OK", role: .cancel) {}
        } message: {
            Text(documentManager.errorMessage ?? "An unknown error occurred")
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

            let checker = ModelChecker()
            let result = await checker.verify(specification: file.content)
            appState.verificationResults.append(result)

            // Build graph for visualization (simplified)
            if result.status == .success || result.status == .failure {
                buildStateGraph(from: result)
            }
        }
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

    private func createNewFile() {
        let newFile = TLAFile(
            name: "NewSpec.tla",
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
}

// Notification names moved to Utilities/NotificationNames.swift

#Preview {
    ContentView()
        .environmentObject(AppState())
}
