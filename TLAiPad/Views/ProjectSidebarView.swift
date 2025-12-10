import SwiftUI

struct ProjectSidebarView: View {
    @EnvironmentObject var appState: AppState

    var body: some View {
        List(selection: $appState.selectedFileId) {
            // Open Files Section
            if !appState.openFiles.isEmpty {
                Section("Open Files") {
                    ForEach(appState.openFiles) { file in
                        HStack {
                            Image(systemName: file.type.iconName)
                                .foregroundStyle(file.type.color)
                            Text(file.name)
                            Spacer()
                            if file.hasUnsavedChanges {
                                Circle()
                                    .fill(.orange)
                                    .frame(width: 6, height: 6)
                            }
                            Button(action: { appState.closeFile(file) }) {
                                Image(systemName: "xmark")
                                    .font(.caption)
                                    .foregroundStyle(.secondary)
                            }
                            .buttonStyle(.plain)
                            .help("Close file")
                        }
                        .tag(file.id)
                    }
                }
            }

            // Project Files Section
            if let project = appState.currentProject {
                Section("Project: \(project.name)") {
                    ForEach(project.files.filter { $0.type == .specification }) { file in
                        FileRowView(file: file)
                    }
                    ForEach(project.files.filter { $0.type == .model }) { file in
                        FileRowView(file: file)
                    }
                    ForEach(project.files.filter { $0.type == .pluscal }) { file in
                        FileRowView(file: file)
                    }
                }
            }

            // Empty state when nothing is open
            if appState.openFiles.isEmpty && appState.currentProject == nil {
                ContentUnavailableView(
                    "No Files",
                    systemImage: "doc.text",
                    description: Text("Open a project or create a new file")
                )
            }
        }
        .listStyle(.sidebar)
    }
}

struct FileRowView: View {
    @EnvironmentObject var appState: AppState
    let file: TLAFile

    var body: some View {
        Button(action: { appState.openFile(file) }) {
            Label(file.name, systemImage: file.type.iconName)
        }
        .buttonStyle(.plain)
        .foregroundStyle(appState.selectedFileId == file.id ? .blue : .primary)
    }
}

#Preview {
    ProjectSidebarView()
        .environmentObject(AppState())
}
