import SwiftUI

struct EditorDetailView: View {
    @EnvironmentObject var appState: AppState
    @State private var showVerificationResults = false
    @State private var showSearch = false
    @State private var showDiagnostics = false
    @State private var diagnostics: [TLADiagnostics.Diagnostic] = []
    @State private var currentConfig: TLCConfig = TLCConfig()
    @State private var showConfigEditor = false
    @State private var showError = false
    @State private var errorMessage = ""

    var body: some View {
        if let file = appState.selectedFile {
            VStack(spacing: 0) {
                // Search bar at top
                if showSearch && file.type != .model {
                    SearchReplaceView(
                        content: binding(for: file).content,
                        isPresented: $showSearch
                    )
                    .padding()
                    .transition(.move(edge: .top).combined(with: .opacity))
                }

                // Main editor area
                if file.type == .model {
                    configEditorContent(for: file)
                } else {
                    TLAEditorView(file: binding(for: file))
                        .id(file.id)  // Force view recreation when file changes
                }

                // Verification results panel
                if showVerificationResults {
                    VerificationResultsView(results: appState.verificationResults)
                        .frame(minHeight: 150)
                }

                // Diagnostics panel
                if showDiagnostics && !diagnostics.isEmpty {
                    DiagnosticsListView(diagnostics: diagnostics) { diagnostic in
                        navigateToDiagnostic(diagnostic)
                    }
                    .frame(minHeight: 100, maxHeight: 200)
                }
            }
            .animation(.easeInOut(duration: 0.2), value: showSearch)
            .toolbar {
                ToolbarItemGroup(placement: .secondaryAction) {
                    Button(action: { showSearch.toggle() }) {
                        Label("Find", systemImage: "magnifyingglass")
                    }
                    .keyboardShortcut("f", modifiers: .command)
                    .help("Find and Replace (⌘F)")

                    Toggle(isOn: $showVerificationResults) {
                        Label("Results", systemImage: "list.bullet.rectangle")
                    }
                    .help("Show/Hide Verification Results")

                    Toggle(isOn: $showDiagnostics) {
                        Label("Problems", systemImage: "exclamationmark.triangle")
                    }
                    .help("Show/Hide Diagnostics Panel")

                    if appState.isVerifying {
                        ProgressView()
                            .progressViewStyle(.circular)
                            .scaleEffect(0.7)
                            .help("Verification in progress...")
                    }
                }
            }
            .navigationTitle(file.name)
            #if os(iOS)
            .navigationBarTitleDisplayMode(.inline)
            #endif
            .onChange(of: file.content) { _, newContent in
                if file.type == .specification || file.type == .pluscal {
                    updateDiagnostics(for: newContent)
                } else {
                    diagnostics = []
                }

                if file.type == .model {
                    currentConfig = TLCConfig.parse(from: newContent)
                }
            }
            .onAppear {
                if file.type == .specification || file.type == .pluscal {
                    updateDiagnostics(for: file.content)
                } else {
                    diagnostics = []
                }
            }
            .alert("Error", isPresented: $showError) {
                Button("OK", role: .cancel) {}
            } message: {
                Text(errorMessage)
            }
        } else {
            EmptyEditorView()
                .environmentObject(appState)
        }
    }

    private func binding(for file: TLAFile) -> Binding<TLAFile> {
        // Use id-based binding to avoid stale index issues when files are added/removed
        let fileId = file.id
        return Binding(
            get: {
                appState.openFiles.first { $0.id == fileId } ?? file
            },
            set: { newValue in
                if let index = appState.openFiles.firstIndex(where: { $0.id == fileId }) {
                    appState.openFiles[index] = newValue
                }
            }
        )
    }

    private func updateDiagnostics(for content: String) {
        diagnostics = TLADiagnostics.shared.analyze(content)
    }

    private func navigateToDiagnostic(_ diagnostic: TLADiagnostics.Diagnostic) {
        NotificationCenter.default.post(
            name: .navigateToLine,
            object: diagnostic.location
        )
    }

    @ViewBuilder
    private func configEditorContent(for file: TLAFile) -> some View {
        ConfigEditorView(config: configBinding(for: file))
            .onAppear {
                currentConfig = TLCConfig.parse(from: file.content)
            }
            .onChange(of: appState.selectedFileId) { _, newId in
                // Use selectedFile from appState to avoid stale capture
                if let currentFile = appState.selectedFile, currentFile.type == .model {
                    currentConfig = TLCConfig.parse(from: currentFile.content)
                }
            }
    }

    private func configBinding(for file: TLAFile) -> Binding<TLCConfig> {
        Binding(
            get: { currentConfig },
            set: { newConfig in
                currentConfig = newConfig
                // Update the file content with generated config
                if let index = appState.openFiles.firstIndex(where: { $0.id == file.id }) {
                    appState.openFiles[index].content = newConfig.generateConfigFile()
                    appState.openFiles[index].hasUnsavedChanges = true
                }
            }
        )
    }
}

// MARK: - Empty State View

struct EmptyEditorView: View {
    @EnvironmentObject var appState: AppState
    @ObservedObject private var fileStorage = FileStorage.shared
    @State private var showError = false
    @State private var errorMessage = ""
    @State private var showNewFileDialog = false
    @State private var newFileName = "Untitled"

    var body: some View {
        VStack(spacing: 32) {
            Spacer()

            // Icon
            Image(systemName: "doc.text.fill")
                .font(.system(size: 72))
                .foregroundStyle(.secondary)

            // Title and description
            VStack(spacing: 8) {
                Text("No File Open")
                    .font(.title)
                    .fontWeight(.semibold)

                Text("Create a new TLA+ specification or select an existing file")
                    .font(.body)
                    .foregroundStyle(.secondary)
                    .multilineTextAlignment(.center)
                    .padding(.horizontal, 40)
            }

            // Action buttons
            VStack(spacing: 16) {
                Button(action: { showNewFileDialog = true }) {
                    Label("New Specification", systemImage: "doc.badge.plus")
                        .frame(minWidth: 200)
                }
                .buttonStyle(.borderedProminent)
                .controlSize(.large)

                if !fileStorage.recentFiles.isEmpty {
                    Menu {
                        ForEach(fileStorage.recentFiles.prefix(5)) { recent in
                            Button(recent.name) {
                                openRecentFile(recent)
                            }
                        }
                    } label: {
                        Label("Open Recent", systemImage: "clock")
                            .frame(minWidth: 200)
                    }
                    .buttonStyle(.bordered)
                    .controlSize(.large)
                }
            }

            Spacer()

            // Keyboard shortcut hint
            Text("Tip: Press ⌘N to create a new file")
                .font(.caption)
                .foregroundStyle(.tertiary)
                .padding(.bottom, 20)
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
        #if os(macOS)
        .background(Color(NSColor.windowBackgroundColor))
        #else
        .background(Color(uiColor: .systemGroupedBackground))
        #endif
        .alert("Error", isPresented: $showError) {
            Button("OK", role: .cancel) {}
        } message: {
            Text(errorMessage)
        }
        .alert("New Specification", isPresented: $showNewFileDialog) {
            TextField("File name", text: $newFileName)
            Button("Cancel", role: .cancel) {
                newFileName = "Untitled"
            }
            Button("Create") {
                createNewFile(named: newFileName)
                newFileName = "Untitled"
            }
        } message: {
            Text("Enter a name for the new TLA+ specification")
        }
    }

    private func createNewFile(named name: String) {
        var fileName = name.trimmingCharacters(in: .whitespaces)
        if fileName.isEmpty {
            fileName = "Untitled"
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

    private func openRecentFile(_ recent: FileStorage.RecentFile) {
        Task {
            do {
                let file = try await fileStorage.loadFile(from: URL(fileURLWithPath: recent.path))
                await MainActor.run {
                    appState.openFile(file)
                }
            } catch {
                await MainActor.run {
                    errorMessage = "Failed to open recent file: \(error.localizedDescription)"
                    showError = true
                }
            }
        }
    }
}

struct VSplitView<Content: View>: View {
    @ViewBuilder let content: Content

    var body: some View {
        VStack(spacing: 0) {
            content
        }
    }
}

#Preview {
    EditorDetailView()
        .environmentObject(AppState())
}
