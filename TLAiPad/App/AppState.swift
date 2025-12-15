import SwiftUI
import Combine

/// Central application state manager for the TLA+ IDE
///
/// `AppState` serves as the single source of truth for the application's runtime state,
/// managing open files, the current project, and verification results. It is designed
/// to be used as an `@EnvironmentObject` throughout the app's view hierarchy.
///
/// ## Thread Safety
/// This class is marked `@MainActor` to ensure all state mutations occur on the main thread,
/// preventing race conditions in UI updates.
///
/// ## Usage
/// ```swift
/// @EnvironmentObject var appState: AppState
///
/// // Open a file
/// appState.openFile(myFile)
///
/// // Access the selected file
/// if let file = appState.selectedFile {
///     // Work with the file
/// }
/// ```
@MainActor
final class AppState: ObservableObject {
    // MARK: - Published State

    /// The currently active project, if any
    @Published var currentProject: TLAProject?

    /// All files currently open in the editor
    @Published var openFiles: [TLAFile] = []

    /// The ID of the currently selected file in the editor
    @Published var selectedFileId: UUID?

    /// Whether a verification (model checking) operation is in progress
    @Published var isVerifying: Bool = false

    /// History of verification results from model checker runs
    @Published var verificationResults: [VerificationResult] = []

    // MARK: - Computed Properties

    /// The currently selected file, if any
    ///
    /// Returns `nil` if no file is selected or if the selected file ID
    /// doesn't match any open file.
    var selectedFile: TLAFile? {
        guard let id = selectedFileId else { return nil }
        return openFiles.first { $0.id == id }
    }

    // MARK: - File Management

    /// Opens a file in the editor
    ///
    /// If the file is not already open, it will be added to `openFiles`.
    /// The file will become the selected file regardless of whether it was already open.
    ///
    /// - Parameter file: The TLA+ file to open
    func openFile(_ file: TLAFile) {
        if !openFiles.contains(where: { $0.id == file.id }) {
            openFiles.append(file)
        }
        selectedFileId = file.id
    }

    /// Closes a file in the editor
    ///
    /// Removes the file from `openFiles`. If the closed file was selected,
    /// the selection moves to the first remaining open file (if any).
    ///
    /// - Parameter file: The TLA+ file to close
    func closeFile(_ file: TLAFile) {
        openFiles.removeAll { $0.id == file.id }
        if selectedFileId == file.id {
            selectedFileId = openFiles.first?.id
        }
    }

    /// Closes a file by its ID
    ///
    /// Removes the file with the given ID from `openFiles`. If the closed file
    /// was selected, the selection moves to the first remaining open file (if any).
    ///
    /// - Parameter id: The UUID of the file to close
    func closeFile(id: UUID) {
        openFiles.removeAll { $0.id == id }
        if selectedFileId == id {
            selectedFileId = openFiles.first?.id
        }
    }
}
