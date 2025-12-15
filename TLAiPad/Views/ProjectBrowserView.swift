import SwiftUI
import UniformTypeIdentifiers
#if os(macOS)
import AppKit
#endif

struct ProjectBrowserView: View {
    @Environment(\.dismiss) private var dismiss
    @EnvironmentObject var appState: AppState
    @State private var recentProjects: [TLAProject] = []
    @State private var showError = false
    @State private var errorMessage = ""
    @State private var isImporting = false

    var body: some View {
        NavigationStack {
            List {
                Section("Recent Projects") {
                    if recentProjects.isEmpty {
                        Text("No recent projects")
                            .foregroundStyle(.secondary)
                    } else {
                        ForEach(recentProjects) { project in
                            Button(action: { openProject(project) }) {
                                VStack(alignment: .leading) {
                                    Text(project.name)
                                        .font(.headline)
                                    Text(project.path)
                                        .font(.caption)
                                        .foregroundStyle(.secondary)
                                }
                            }
                        }
                    }
                }

                Section("Actions") {
                    Button(action: createNewProject) {
                        Label("New Project", systemImage: "plus.rectangle")
                    }

                    Button(action: openExistingProject) {
                        Label("Open Project...", systemImage: "folder")
                    }

                    Button(action: openSampleProject) {
                        Label("Open Sample Project", systemImage: "book")
                    }
                }
            }
            .navigationTitle("Projects")
            .toolbar {
                ToolbarItem(placement: .cancellationAction) {
                    Button("Cancel") { dismiss() }
                }
            }
            .alert("Error", isPresented: $showError) {
                Button("OK", role: .cancel) {}
            } message: {
                Text(errorMessage)
            }
            #if !os(macOS)
            .fileImporter(
                isPresented: $isImporting,
                allowedContentTypes: [.plainText, .text, .folder],
                allowsMultipleSelection: true
            ) { result in
                switch result {
                case .success(let urls):
                    importProjectURLs(urls)
                case .failure(let error):
                    errorMessage = error.localizedDescription
                    showError = true
                }
            }
            #endif
        }
    }

    private func openProject(_ project: TLAProject) {
        appState.currentProject = project
        dismiss()
    }

    private func createNewProject() {
        let project = TLAProject(
            name: "New Project",
            path: "/Documents/TLA",
            files: [
                TLAFile(name: "Spec.tla", type: .specification, content: TLATemplates.basicSpecification)
            ]
        )
        openProject(project)
    }

    private func openExistingProject() {
        #if os(macOS)
        let panel = NSOpenPanel()
        panel.allowsMultipleSelection = true
        panel.canChooseDirectories = true
        panel.canChooseFiles = true
        panel.allowedContentTypes = [.plainText]
        panel.title = "Open TLA+ Project"
        panel.message = "Select a folder containing .tla files or select individual files"

        if panel.runModal() == .OK {
            importProjectURLs(panel.urls)
        }
        #else
        isImporting = true
        #endif
    }

    private func importProjectURLs(_ urls: [URL]) {
        var files: [TLAFile] = []
        var projectName = "Imported Project"

        for url in urls {
            // Start accessing security-scoped resource for iOS
            let didStartAccess = url.startAccessingSecurityScopedResource()
            defer {
                if didStartAccess {
                    url.stopAccessingSecurityScopedResource()
                }
            }

            do {
                var isDirectory: ObjCBool = false
                if FileManager.default.fileExists(atPath: url.path, isDirectory: &isDirectory),
                   isDirectory.boolValue {
                    // It's a directory - use it as project name and scan for files
                    projectName = url.lastPathComponent
                    let contents = try FileManager.default.contentsOfDirectory(
                        at: url,
                        includingPropertiesForKeys: nil
                    )
                    for fileURL in contents where fileURL.pathExtension == "tla" || fileURL.pathExtension == "cfg" {
                        let content = try String(contentsOf: fileURL, encoding: .utf8)
                        let fileType: TLAFileType = fileURL.pathExtension == "cfg" ? .model : .specification
                        files.append(TLAFile(name: fileURL.lastPathComponent, type: fileType, content: content))
                    }
                } else {
                    // Single file
                    let content = try String(contentsOf: url, encoding: .utf8)
                    let fileType: TLAFileType = url.pathExtension == "cfg" ? .model : .specification
                    files.append(TLAFile(name: url.lastPathComponent, type: fileType, content: content))
                    if files.count == 1 {
                        // Use first file name (without extension) as project name
                        projectName = url.deletingPathExtension().lastPathComponent
                    }
                }
            } catch {
                errorMessage = "Failed to import \(url.lastPathComponent): \(error.localizedDescription)"
                showError = true
                return
            }
        }

        if !files.isEmpty {
            let project = TLAProject(
                name: projectName,
                path: urls.first?.deletingLastPathComponent().path ?? "",
                files: files
            )
            openProject(project)
        }
    }

    private func openSampleProject() {
        let project = TLAProject(
            name: "Sample: Two-Phase Commit",
            path: "/Samples/TwoPhaseCommit",
            files: [
                TLAFile(name: "TwoPhaseCommit.tla", type: .specification, content: TLATemplates.twoPhaseCommit),
                TLAFile(name: "MC.tla", type: .model, content: TLATemplates.modelConfig)
            ]
        )
        openProject(project)
    }
}

#Preview {
    ProjectBrowserView()
        .environmentObject(AppState())
}
