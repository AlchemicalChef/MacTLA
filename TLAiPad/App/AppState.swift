import SwiftUI
import Combine

@MainActor
final class AppState: ObservableObject {
    @Published var currentProject: TLAProject?
    @Published var openFiles: [TLAFile] = []
    @Published var selectedFileId: UUID?
    @Published var isVerifying: Bool = false
    @Published var verificationResults: [VerificationResult] = []

    var selectedFile: TLAFile? {
        guard let id = selectedFileId else { return nil }
        return openFiles.first { $0.id == id }
    }

    func openFile(_ file: TLAFile) {
        if !openFiles.contains(where: { $0.id == file.id }) {
            openFiles.append(file)
        }
        selectedFileId = file.id
    }

    func closeFile(_ file: TLAFile) {
        openFiles.removeAll { $0.id == file.id }
        if selectedFileId == file.id {
            selectedFileId = openFiles.first?.id
        }
    }

    func closeFile(id: UUID) {
        openFiles.removeAll { $0.id == id }
        if selectedFileId == id {
            selectedFileId = openFiles.first?.id
        }
    }
}
