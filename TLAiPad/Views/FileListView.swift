import SwiftUI

struct FileListView: View {
    @EnvironmentObject var appState: AppState

    var body: some View {
        if appState.openFiles.isEmpty {
            ContentUnavailableView(
                "No Files Open",
                systemImage: "doc.text",
                description: Text("Select a file from the sidebar")
            )
        } else {
            List(appState.openFiles, selection: $appState.selectedFileId) { file in
                HStack {
                    Image(systemName: file.type.iconName)
                        .foregroundStyle(file.type.color)
                    Text(file.name)
                    Spacer()
                    if file.hasUnsavedChanges {
                        Circle()
                            .fill(.orange)
                            .frame(width: 8, height: 8)
                    }
                    Button(action: { appState.closeFile(file) }) {
                        Image(systemName: "xmark")
                            .foregroundStyle(.secondary)
                    }
                    .buttonStyle(.plain)
                }
            }
            .listStyle(.sidebar)
            .navigationTitle("Open Files")
        }
    }
}

#Preview {
    FileListView()
        .environmentObject(AppState())
}
