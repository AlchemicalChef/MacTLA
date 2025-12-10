import SwiftUI
import UniformTypeIdentifiers

// MARK: - TLA+ Document Type

extension UTType {
    static var tlaSpec: UTType {
        UTType(exportedAs: "com.tlaipad.tla", conformingTo: .plainText)
    }

    static var tlaConfig: UTType {
        UTType(exportedAs: "com.tlaipad.cfg", conformingTo: .plainText)
    }
}

// MARK: - TLA+ Document

struct TLADocument: FileDocument {
    static var readableContentTypes: [UTType] { [.tlaSpec, .plainText] }
    static var writableContentTypes: [UTType] { [.tlaSpec, .plainText] }

    var content: String

    init(content: String = "") {
        self.content = content
    }

    init(configuration: ReadConfiguration) throws {
        guard let data = configuration.file.regularFileContents,
              let string = String(data: data, encoding: .utf8) else {
            throw CocoaError(.fileReadCorruptFile)
        }
        content = string
    }

    func fileWrapper(configuration: WriteConfiguration) throws -> FileWrapper {
        guard let data = content.data(using: .utf8) else {
            throw CocoaError(.fileWriteInapplicableStringEncoding)
        }
        return FileWrapper(regularFileWithContents: data)
    }
}

// MARK: - Document Manager

@MainActor
final class DocumentManager: ObservableObject {
    @Published var isImporting = false
    @Published var isExporting = false
    @Published var exportFile: TLAFile?
    @Published var errorMessage: String?
    @Published var showError = false

    func importFiles(from urls: [URL], into appState: AppState) {
        for url in urls {
            do {
                guard url.startAccessingSecurityScopedResource() else {
                    throw DocumentError.accessDenied
                }
                defer { url.stopAccessingSecurityScopedResource() }

                let content = try String(contentsOf: url, encoding: .utf8)
                let fileName = url.lastPathComponent
                let fileType = determineFileType(from: url)

                let file = TLAFile(
                    name: fileName,
                    type: fileType,
                    content: content
                )

                // Add to project or open directly
                if appState.currentProject != nil {
                    appState.currentProject?.files.append(file)
                }
                appState.openFile(file)

            } catch {
                errorMessage = "Failed to import \(url.lastPathComponent): \(error.localizedDescription)"
                showError = true
            }
        }
    }

    func exportFile(_ file: TLAFile, to url: URL) {
        do {
            guard url.startAccessingSecurityScopedResource() else {
                throw DocumentError.accessDenied
            }
            defer { url.stopAccessingSecurityScopedResource() }

            try file.content.write(to: url, atomically: true, encoding: .utf8)
        } catch {
            errorMessage = "Failed to export \(file.name): \(error.localizedDescription)"
            showError = true
        }
    }

    func saveFile(_ file: TLAFile, in project: TLAProject?) async throws {
        // For now, files are kept in memory
        // In a full implementation, this would persist to disk
    }

    private func determineFileType(from url: URL) -> TLAFileType {
        let ext = url.pathExtension.lowercased()
        switch ext {
        case "tla":
            return .specification
        case "cfg":
            return .model
        default:
            return .specification
        }
    }

    enum DocumentError: LocalizedError {
        case accessDenied
        case invalidFormat
        case saveFailed

        var errorDescription: String? {
            switch self {
            case .accessDenied: return "Access to the file was denied"
            case .invalidFormat: return "The file format is not supported"
            case .saveFailed: return "Failed to save the file"
            }
        }
    }
}

// MARK: - File Picker Views

struct DocumentImporter: ViewModifier {
    @Binding var isPresented: Bool
    let onImport: ([URL]) -> Void
    var onError: ((Error) -> Void)?

    func body(content: Content) -> some View {
        content
            .fileImporter(
                isPresented: $isPresented,
                allowedContentTypes: [.tlaSpec, .plainText, .text],
                allowsMultipleSelection: true
            ) { result in
                switch result {
                case .success(let urls):
                    onImport(urls)
                case .failure(let error):
                    onError?(error)
                }
            }
    }
}

struct DocumentExporter: ViewModifier {
    @Binding var isPresented: Bool
    let document: TLADocument
    let defaultFilename: String
    let onExport: (URL) -> Void
    var onError: ((Error) -> Void)?

    func body(content: Content) -> some View {
        content
            .fileExporter(
                isPresented: $isPresented,
                document: document,
                contentType: .tlaSpec,
                defaultFilename: defaultFilename
            ) { result in
                switch result {
                case .success(let url):
                    onExport(url)
                case .failure(let error):
                    onError?(error)
                }
            }
    }
}

extension View {
    func documentImporter(
        isPresented: Binding<Bool>,
        onImport: @escaping ([URL]) -> Void,
        onError: ((Error) -> Void)? = nil
    ) -> some View {
        modifier(DocumentImporter(isPresented: isPresented, onImport: onImport, onError: onError))
    }

    func documentExporter(
        isPresented: Binding<Bool>,
        document: TLADocument,
        defaultFilename: String,
        onExport: @escaping (URL) -> Void,
        onError: ((Error) -> Void)? = nil
    ) -> some View {
        modifier(DocumentExporter(
            isPresented: isPresented,
            document: document,
            defaultFilename: defaultFilename,
            onExport: onExport,
            onError: onError
        ))
    }
}

// Recent files functionality moved to FileStorage.swift
