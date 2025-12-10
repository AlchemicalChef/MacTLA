import SwiftUI
#if os(macOS)
import AppKit
#endif

struct WelcomeView: View {
    @EnvironmentObject var appState: AppState
    @EnvironmentObject var documentManager: DocumentManager
    @Binding var isPresented: Bool
    @ObservedObject private var fileStorage = FileStorage.shared
    @ObservedObject private var settings = AppSettings.shared

    @State private var selectedTemplate: TemplateOption?
    @State private var showImportError = false
    @State private var importErrorMessage = ""
    @State private var showNewFileDialog = false
    @State private var newFileName = "NewSpec"

    var body: some View {
        NavigationStack {
            ScrollView {
                VStack(spacing: 32) {
                    // Header
                    VStack(spacing: 12) {
                        Image(systemName: "checkmark.shield.fill")
                            .font(.system(size: 64))
                            .foregroundStyle(.tint)

                        Text("TLA+ Toolbox")
                            .font(.largeTitle.bold())

                        #if os(macOS)
                        Text("Model checking and verification for macOS")
                            .font(.subheadline)
                            .foregroundStyle(.secondary)
                        #else
                        Text("Model checking and verification for iPad")
                            .font(.subheadline)
                            .foregroundStyle(.secondary)
                        #endif
                    }
                    .padding(.top, 40)

                    // Quick actions
                    LazyVGrid(columns: [
                        GridItem(.flexible()),
                        GridItem(.flexible())
                    ], spacing: 16) {
                        QuickActionButton(
                            title: "New Specification",
                            systemImage: "doc.badge.plus",
                            color: .blue
                        ) {
                            showNewFileDialog = true
                        }
                        .help("Create a new TLA+ specification (⌘N)")

                        QuickActionButton(
                            title: "Open Project",
                            systemImage: "folder",
                            color: .orange
                        ) {
                            openExistingProject()
                        }
                        .help("Open an existing project (⌘O)")

                        QuickActionButton(
                            title: "Import File",
                            systemImage: "square.and.arrow.down",
                            color: .green
                        ) {
                            importFile()
                        }
                        .help("Import a TLA+ file from disk")

                        QuickActionButton(
                            title: "Browse Templates",
                            systemImage: "doc.text.magnifyingglass",
                            color: .purple
                        ) {
                            // Show templates
                        }
                        .help("Browse example specifications")
                    }
                    .padding(.horizontal)

                    // Templates section
                    VStack(alignment: .leading, spacing: 12) {
                        Text("Templates")
                            .font(.headline)
                            .padding(.horizontal)

                        ScrollView(.horizontal, showsIndicators: false) {
                            HStack(spacing: 12) {
                                ForEach(TemplateOption.allCases) { template in
                                    TemplateCard(
                                        template: template,
                                        isSelected: selectedTemplate == template
                                    ) {
                                        selectedTemplate = template
                                        createFromTemplate(template)
                                    }
                                }
                            }
                            .padding(.horizontal)
                        }
                    }

                    // Recent files section
                    if !fileStorage.recentFiles.isEmpty {
                        VStack(alignment: .leading, spacing: 12) {
                            HStack {
                                Text("Recent Files")
                                    .font(.headline)

                                Spacer()

                                Button("Clear") {
                                    fileStorage.clearRecentFiles()
                                }
                                .font(.caption)
                            }
                            .padding(.horizontal)

                            ForEach(fileStorage.recentFiles.prefix(5)) { recent in
                                RecentFileRow(file: recent) {
                                    openRecentFile(recent)
                                }
                            }
                        }
                    }

                    // Tips section
                    VStack(alignment: .leading, spacing: 12) {
                        Text("Tips")
                            .font(.headline)
                            .padding(.horizontal)

                        TipCard(
                            title: "Keyboard Shortcuts",
                            description: "Use Cmd+R to run verification, Cmd+F to search",
                            systemImage: "keyboard"
                        )

                        TipCard(
                            title: "PlusCal Support",
                            description: "Write algorithms in PlusCal and translate to TLA+",
                            systemImage: "arrow.triangle.2.circlepath"
                        )

                        TipCard(
                            title: "State Graph",
                            description: "Visualize the state space after verification",
                            systemImage: "point.3.connected.trianglepath.dotted"
                        )
                    }

                    Spacer(minLength: 40)
                }
            }
            .navigationTitle("")
            #if os(iOS)
            .navigationBarTitleDisplayMode(.inline)
            #endif
            .toolbar {
                ToolbarItem(placement: .cancellationAction) {
                    Button("Close") {
                        isPresented = false
                    }
                }

                ToolbarItem(placement: .primaryAction) {
                    Button {
                        settings.showWelcome = false
                        isPresented = false
                    } label: {
                        Text("Don't show again")
                            .font(.caption)
                    }
                }
            }
            .alert("Import Error", isPresented: $showImportError) {
                Button("OK", role: .cancel) {}
            } message: {
                Text(importErrorMessage)
            }
            .alert("New Specification", isPresented: $showNewFileDialog) {
                TextField("File name", text: $newFileName)
                Button("Cancel", role: .cancel) {
                    newFileName = "NewSpec"
                }
                Button("Create") {
                    createNewSpecification(named: newFileName)
                    newFileName = "NewSpec"
                }
            } message: {
                Text("Enter a name for the new TLA+ specification")
            }
        }
    }

    private func createNewSpecification(named name: String) {
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
        isPresented = false
    }

    private func createFromTemplate(_ template: TemplateOption) {
        let newFile = TLAFile(
            name: template.fileName,
            type: .specification,
            content: template.content
        )
        appState.openFile(newFile)
        isPresented = false
    }

    private func openRecentFile(_ recent: FileStorage.RecentFile) {
        Task {
            do {
                let file = try await fileStorage.loadFile(from: URL(fileURLWithPath: recent.path))
                await MainActor.run {
                    appState.openFile(file)
                    isPresented = false
                }
            } catch {
                importErrorMessage = "Failed to open recent file: \(error.localizedDescription)"
                showImportError = true
            }
        }
    }

    #if os(macOS)
    private func openExistingProject() {
        let panel = NSOpenPanel()
        panel.allowsMultipleSelection = true
        panel.canChooseDirectories = true
        panel.canChooseFiles = true
        panel.allowedContentTypes = [.plainText]
        panel.title = "Open TLA+ Files"
        panel.message = "Select .tla or .cfg files to open"

        if panel.runModal() == .OK {
            importURLs(panel.urls)
        }
    }

    private func importFile() {
        let panel = NSOpenPanel()
        panel.allowsMultipleSelection = true
        panel.canChooseDirectories = false
        panel.canChooseFiles = true
        panel.allowedContentTypes = [.plainText]
        panel.title = "Import TLA+ Files"
        panel.message = "Select .tla or .cfg files to import"

        if panel.runModal() == .OK {
            importURLs(panel.urls)
        }
    }

    private func importURLs(_ urls: [URL]) {
        for url in urls {
            do {
                // Handle directories by scanning for .tla/.cfg files
                var isDirectory: ObjCBool = false
                if FileManager.default.fileExists(atPath: url.path, isDirectory: &isDirectory),
                   isDirectory.boolValue {
                    let contents = try FileManager.default.contentsOfDirectory(
                        at: url,
                        includingPropertiesForKeys: nil
                    )
                    let tlaFiles = contents.filter { $0.pathExtension == "tla" || $0.pathExtension == "cfg" }
                    importURLs(tlaFiles)
                } else {
                    // Import single file
                    let content = try String(contentsOf: url, encoding: .utf8)
                    let fileName = url.lastPathComponent
                    let fileType: TLAFileType = fileName.hasSuffix(".cfg") ? .model : .specification

                    let file = TLAFile(
                        name: fileName,
                        type: fileType,
                        content: content
                    )

                    appState.openFile(file)
                    fileStorage.addToRecentFiles(file, path: url.path, isCloud: false)
                }
            } catch {
                importErrorMessage = "Failed to import \(url.lastPathComponent): \(error.localizedDescription)"
                showImportError = true
                return
            }
        }
        isPresented = false
    }
    #else
    private func openExistingProject() {
        // iOS uses document picker - trigger import
        documentManager.isImporting = true
    }

    private func importFile() {
        documentManager.isImporting = true
    }
    #endif
}

// MARK: - Quick Action Button

struct QuickActionButton: View {
    let title: String
    let systemImage: String
    let color: Color
    let action: () -> Void

    var body: some View {
        Button(action: action) {
            VStack(spacing: 12) {
                Image(systemName: systemImage)
                    .font(.title)
                    .foregroundStyle(color)

                Text(title)
                    .font(.caption)
                    .foregroundStyle(.primary)
            }
            .frame(maxWidth: .infinity)
            .padding()
            .background(
                RoundedRectangle(cornerRadius: 12)
                    .fill(color.opacity(0.1))
            )
        }
        .buttonStyle(.plain)
    }
}

// MARK: - Template Option

enum TemplateOption: String, CaseIterable, Identifiable {
    case basic = "Basic Specification"
    case mutex = "Mutex Algorithm"
    case producerConsumer = "Producer-Consumer"
    case twoPhaseCommit = "Two-Phase Commit"
    case raft = "Raft Consensus"

    var id: String { rawValue }

    var fileName: String {
        switch self {
        case .basic: return "Spec.tla"
        case .mutex: return "Mutex.tla"
        case .producerConsumer: return "ProducerConsumer.tla"
        case .twoPhaseCommit: return "TwoPhaseCommit.tla"
        case .raft: return "Raft.tla"
        }
    }

    var description: String {
        switch self {
        case .basic: return "Empty TLA+ module template"
        case .mutex: return "Mutual exclusion algorithm"
        case .producerConsumer: return "Classic bounded buffer"
        case .twoPhaseCommit: return "Distributed transaction protocol"
        case .raft: return "Consensus algorithm for distributed systems"
        }
    }

    var systemImage: String {
        switch self {
        case .basic: return "doc.text"
        case .mutex: return "lock.shield"
        case .producerConsumer: return "arrow.left.arrow.right"
        case .twoPhaseCommit: return "checkmark.circle.badge.questionmark"
        case .raft: return "server.rack"
        }
    }

    var content: String {
        switch self {
        case .basic: return TLATemplates.basicSpecification
        case .mutex: return TLATemplates.mutexExample
        case .producerConsumer: return TLATemplates.plusCalMutex
        case .twoPhaseCommit: return TLATemplates.twoPhaseCommit
        case .raft: return TLATemplates.raftConsensus
        }
    }
}

// MARK: - Template Card

struct TemplateCard: View {
    let template: TemplateOption
    let isSelected: Bool
    let action: () -> Void

    var body: some View {
        Button(action: action) {
            VStack(alignment: .leading, spacing: 8) {
                Image(systemName: template.systemImage)
                    .font(.title2)
                    .foregroundStyle(.tint)

                Text(template.rawValue)
                    .font(.subheadline.bold())
                    .foregroundStyle(.primary)

                Text(template.description)
                    .font(.caption)
                    .foregroundStyle(.secondary)
                    .lineLimit(2)
            }
            .frame(width: 150, alignment: .leading)
            .padding()
            .background(
                RoundedRectangle(cornerRadius: 12)
                    .fill(isSelected ? Color.accentColor.opacity(0.1) : Color.gray.opacity(0.1))
            )
            .overlay(
                RoundedRectangle(cornerRadius: 12)
                    .stroke(isSelected ? Color.accentColor : Color.clear, lineWidth: 2)
            )
        }
        .buttonStyle(.plain)
    }
}

// MARK: - Recent File Row

struct RecentFileRow: View {
    let file: FileStorage.RecentFile
    let action: () -> Void

    var body: some View {
        Button(action: action) {
            HStack {
                Image(systemName: file.isCloud ? "icloud.fill" : "doc.text.fill")
                    .foregroundStyle(file.isCloud ? .blue : .secondary)

                VStack(alignment: .leading, spacing: 2) {
                    Text(file.name)
                        .font(.subheadline)
                        .foregroundStyle(.primary)

                    Text(file.lastOpened.formatted(date: .abbreviated, time: .shortened))
                        .font(.caption)
                        .foregroundStyle(.secondary)
                }

                Spacer()

                Image(systemName: "chevron.right")
                    .font(.caption)
                    .foregroundStyle(.tertiary)
            }
            .padding(.horizontal)
            .padding(.vertical, 8)
            .contentShape(Rectangle())
        }
        .buttonStyle(.plain)
    }
}

// MARK: - Tip Card

struct TipCard: View {
    let title: String
    let description: String
    let systemImage: String

    var body: some View {
        HStack(spacing: 12) {
            Image(systemName: systemImage)
                .font(.title2)
                .foregroundStyle(.tint)
                .frame(width: 44)

            VStack(alignment: .leading, spacing: 2) {
                Text(title)
                    .font(.subheadline.bold())

                Text(description)
                    .font(.caption)
                    .foregroundStyle(.secondary)
            }

            Spacer()
        }
        .padding()
        .background(
            RoundedRectangle(cornerRadius: 12)
                .fill(Color.gray.opacity(0.1))
        )
        .padding(.horizontal)
    }
}

// MARK: - Preview

#Preview {
    WelcomeView(isPresented: .constant(true))
        .environmentObject(AppState())
        .environmentObject(DocumentManager())
}
