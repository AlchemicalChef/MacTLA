import Foundation
import SwiftUI

/// Handles file storage and iCloud sync for TLA+ specifications
@MainActor
final class FileStorage: ObservableObject {
    static let shared = FileStorage()

    @Published var isCloudAvailable = false
    @Published var isSyncing = false
    @Published var recentFiles: [RecentFile] = []
    @Published var lastAutoSaveError: String?

    private let fileManager = FileManager.default

    // Directory URLs
    private var localDocumentsURL: URL {
        // Use .first with a fallback to handle the rare case of empty array
        fileManager.urls(for: .documentDirectory, in: .userDomainMask).first
            ?? URL(fileURLWithPath: NSTemporaryDirectory())
    }

    private var cloudDocumentsURL: URL? {
        fileManager.url(forUbiquityContainerIdentifier: nil)?
            .appendingPathComponent("Documents")
    }

    private var projectsDirectory: URL {
        let url = (cloudDocumentsURL ?? localDocumentsURL).appendingPathComponent("Projects")
        try? fileManager.createDirectory(at: url, withIntermediateDirectories: true)
        return url
    }

    private init() {
        checkCloudAvailability()
        loadRecentFiles()
    }

    // MARK: - Cloud Availability

    private func checkCloudAvailability() {
        Task {
            isCloudAvailable = fileManager.ubiquityIdentityToken != nil
        }
    }

    // MARK: - Recent Files

    struct RecentFile: Identifiable, Codable {
        let id: UUID
        let name: String
        let path: String
        let lastOpened: Date
        let isCloud: Bool
    }

    private var recentFilesURL: URL {
        localDocumentsURL.appendingPathComponent("recent_files.json")
    }

    func loadRecentFiles() {
        guard let data = try? Data(contentsOf: recentFilesURL),
              let files = try? JSONDecoder().decode([RecentFile].self, from: data) else {
            return
        }
        recentFiles = files.sorted { $0.lastOpened > $1.lastOpened }
    }

    func addToRecentFiles(_ file: TLAFile, path: String, isCloud: Bool) {
        // Remove existing entry for same path
        recentFiles.removeAll { $0.path == path }

        // Add new entry
        let recent = RecentFile(
            id: file.id,
            name: file.name,
            path: path,
            lastOpened: Date(),
            isCloud: isCloud
        )
        recentFiles.insert(recent, at: 0)

        // Limit to recent files count
        let limit = AppSettings.shared.recentFilesLimit
        if recentFiles.count > limit {
            recentFiles = Array(recentFiles.prefix(limit))
        }

        saveRecentFiles()
    }

    private func saveRecentFiles() {
        guard let data = try? JSONEncoder().encode(recentFiles) else { return }
        try? data.write(to: recentFilesURL)
    }

    func clearRecentFiles() {
        recentFiles = []
        try? fileManager.removeItem(at: recentFilesURL)
    }

    // MARK: - Project Operations

    func saveProject(_ project: TLAProject) async throws {
        let projectURL = projectsDirectory.appendingPathComponent(project.id.uuidString)
        try fileManager.createDirectory(at: projectURL, withIntermediateDirectories: true)

        // Save project metadata
        let metadataURL = projectURL.appendingPathComponent("project.json")
        let metadata = ProjectMetadata(
            id: project.id,
            name: project.name,
            createdAt: project.createdAt,
            modifiedAt: Date(),
            fileNames: project.files.map(\.name)
        )
        let metadataData = try JSONEncoder().encode(metadata)
        try metadataData.write(to: metadataURL)

        // Save each file
        for file in project.files {
            let fileURL = projectURL.appendingPathComponent(file.name)
            try file.content.write(to: fileURL, atomically: true, encoding: .utf8)
        }
    }

    func loadProject(id: UUID) async throws -> TLAProject {
        let projectURL = projectsDirectory.appendingPathComponent(id.uuidString)
        let metadataURL = projectURL.appendingPathComponent("project.json")

        let metadataData = try Data(contentsOf: metadataURL)
        let metadata = try JSONDecoder().decode(ProjectMetadata.self, from: metadataData)

        var files: [TLAFile] = []
        for fileName in metadata.fileNames {
            let fileURL = projectURL.appendingPathComponent(fileName)
            let content = try String(contentsOf: fileURL, encoding: .utf8)
            let fileType: TLAFileType = fileName.hasSuffix(".cfg") ? .model : .specification
            files.append(TLAFile(name: fileName, type: fileType, content: content))
        }

        return TLAProject(
            id: metadata.id,
            name: metadata.name,
            path: projectURL.path,
            files: files,
            createdAt: metadata.createdAt
        )
    }

    func listProjects() async throws -> [ProjectMetadata] {
        var projects: [ProjectMetadata] = []

        let contents = try fileManager.contentsOfDirectory(
            at: projectsDirectory,
            includingPropertiesForKeys: [.isDirectoryKey]
        )

        for url in contents {
            let metadataURL = url.appendingPathComponent("project.json")
            if let data = try? Data(contentsOf: metadataURL),
               let metadata = try? JSONDecoder().decode(ProjectMetadata.self, from: data) {
                projects.append(metadata)
            }
        }

        return projects.sorted { $0.modifiedAt > $1.modifiedAt }
    }

    func deleteProject(id: UUID) async throws {
        let projectURL = projectsDirectory.appendingPathComponent(id.uuidString)
        try fileManager.removeItem(at: projectURL)
    }

    // MARK: - File Operations

    func saveFile(_ file: TLAFile, in project: TLAProject) async throws -> URL {
        let projectURL = projectsDirectory.appendingPathComponent(project.id.uuidString)
        let fileURL = projectURL.appendingPathComponent(file.name)

        try file.content.write(to: fileURL, atomically: true, encoding: .utf8)

        addToRecentFiles(file, path: fileURL.path, isCloud: cloudDocumentsURL != nil)

        return fileURL
    }

    func loadFile(from url: URL) async throws -> TLAFile {
        let content = try String(contentsOf: url, encoding: .utf8)
        let name = url.lastPathComponent
        let fileType: TLAFileType = name.hasSuffix(".cfg") ? .model : .specification

        return TLAFile(name: name, type: fileType, content: content)
    }

    func exportFile(_ file: TLAFile, to url: URL) async throws {
        try file.content.write(to: url, atomically: true, encoding: .utf8)
    }

    // MARK: - Auto Save

    private var autoSaveTask: Task<Void, Never>?

    func startAutoSave(for appState: AppState) {
        guard AppSettings.shared.autoSave else { return }

        autoSaveTask?.cancel()
        autoSaveTask = Task {
            while !Task.isCancelled {
                let interval = TimeInterval(AppSettings.shared.autoSaveInterval)
                try? await Task.sleep(nanoseconds: UInt64(interval * 1_000_000_000))

                guard !Task.isCancelled else { return }

                await autoSaveFiles(appState)
            }
        }
    }

    func stopAutoSave() {
        autoSaveTask?.cancel()
        autoSaveTask = nil
    }

    private func autoSaveFiles(_ appState: AppState) async {
        guard let project = appState.currentProject else { return }

        for file in appState.openFiles where file.hasUnsavedChanges {
            do {
                _ = try await saveFile(file, in: project)
                // Update file state
                if let index = appState.openFiles.firstIndex(where: { $0.id == file.id }) {
                    await MainActor.run {
                        appState.openFiles[index].hasUnsavedChanges = false
                    }
                }
            } catch {
                await MainActor.run {
                    lastAutoSaveError = "Auto-save failed for \(file.name): \(error.localizedDescription)"
                }
            }
        }
    }
}

// MARK: - Project Metadata

struct ProjectMetadata: Identifiable, Codable {
    let id: UUID
    let name: String
    let createdAt: Date
    var modifiedAt: Date
    let fileNames: [String]
}

// MARK: - File Coordinator for iCloud

final class TLAFileCoordinator {
    static let shared = TLAFileCoordinator()

    private init() {}

    func coordinatedRead(at url: URL) async throws -> String {
        var coordinatorError: NSError?
        var readError: Error?
        var result: String?

        let coordinator = NSFileCoordinator()
        coordinator.coordinate(readingItemAt: url, options: [], error: &coordinatorError) { coordinatedURL in
            do {
                result = try String(contentsOf: coordinatedURL, encoding: .utf8)
            } catch {
                readError = error
            }
        }

        if let error = coordinatorError {
            throw error
        }
        if let error = readError {
            throw error
        }

        return result ?? ""
    }

    func coordinatedWrite(_ content: String, to url: URL) async throws {
        var coordinatorError: NSError?
        var writeError: Error?

        let coordinator = NSFileCoordinator()
        coordinator.coordinate(writingItemAt: url, options: .forReplacing, error: &coordinatorError) { coordinatedURL in
            do {
                try content.write(to: coordinatedURL, atomically: true, encoding: .utf8)
            } catch {
                writeError = error
            }
        }

        if let error = coordinatorError {
            throw error
        }
        if let error = writeError {
            throw error
        }
    }
}

// Document types defined in Models/TLAFile.swift as TLAFileType
