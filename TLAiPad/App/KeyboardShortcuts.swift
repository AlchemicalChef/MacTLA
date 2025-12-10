import SwiftUI

/// Keyboard shortcut definitions for the TLA+ editor
struct KeyboardShortcuts {
    // File operations
    static let newFile = KeyboardShortcut("n", modifiers: .command)
    static let openFile = KeyboardShortcut("o", modifiers: .command)
    static let saveFile = KeyboardShortcut("s", modifiers: .command)
    static let closeFile = KeyboardShortcut("w", modifiers: .command)

    // Edit operations
    static let find = KeyboardShortcut("f", modifiers: .command)
    static let findAndReplace = KeyboardShortcut("f", modifiers: [.command, .option])
    static let goToLine = KeyboardShortcut("g", modifiers: .command)
    static let commentLine = KeyboardShortcut("/", modifiers: .command)

    // View operations
    static let toggleSidebar = KeyboardShortcut("0", modifiers: .command)
    static let zoomIn = KeyboardShortcut("+", modifiers: .command)
    static let zoomOut = KeyboardShortcut("-", modifiers: .command)

    // Verification
    static let runVerification = KeyboardShortcut("r", modifiers: .command)
    static let stopVerification = KeyboardShortcut(".", modifiers: .command)

    // Navigation
    static let nextError = KeyboardShortcut("'", modifiers: .command)
    static let previousError = KeyboardShortcut("'", modifiers: [.command, .shift])
    static let jumpToDefinition = KeyboardShortcut(.return, modifiers: .command)
    static let showSymbols = KeyboardShortcut("o", modifiers: [.command, .shift])
}

// MARK: - Commands

struct TLACommands: Commands {
    @ObservedObject var appState: AppState

    var body: some Commands {
        CommandGroup(replacing: .newItem) {
            Button("New Specification") {
                createNewFile()
            }
            .keyboardShortcut(KeyboardShortcuts.newFile)
        }

        CommandGroup(after: .newItem) {
            Button("Save") {
                saveCurrentFile()
            }
            .keyboardShortcut(KeyboardShortcuts.saveFile)
            .disabled(appState.selectedFile == nil)

            Button("Close") {
                closeCurrentFile()
            }
            .keyboardShortcut(KeyboardShortcuts.closeFile)
            .disabled(appState.selectedFile == nil)
        }

        CommandGroup(replacing: .textEditing) {
            Button("Find...") {
                NotificationCenter.default.post(name: .toggleSearch, object: nil)
            }
            .keyboardShortcut(KeyboardShortcuts.find)

            Button("Find and Replace...") {
                NotificationCenter.default.post(name: .toggleSearch, object: true)
            }
            .keyboardShortcut(KeyboardShortcuts.findAndReplace)

            Divider()

            Button("Go to Line...") {
                NotificationCenter.default.post(name: .showGoToLine, object: nil)
            }
            .keyboardShortcut(KeyboardShortcuts.goToLine)

            Button("Toggle Comment") {
                NotificationCenter.default.post(name: .toggleComment, object: nil)
            }
            .keyboardShortcut(KeyboardShortcuts.commentLine)
        }

        CommandMenu("Verification") {
            Button("Run Model Checker") {
                NotificationCenter.default.post(name: .runVerification, object: nil)
            }
            .keyboardShortcut(KeyboardShortcuts.runVerification)
            .disabled(appState.selectedFile == nil || appState.isVerifying)

            Button("Stop Verification") {
                NotificationCenter.default.post(name: .stopVerification, object: nil)
            }
            .keyboardShortcut(KeyboardShortcuts.stopVerification)
            .disabled(!appState.isVerifying)

            Divider()

            Button("Translate PlusCal") {
                NotificationCenter.default.post(name: .translatePlusCal, object: nil)
            }
            .disabled(appState.selectedFile == nil)
        }

        CommandMenu("Navigate") {
            Button("Jump to Definition") {
                NotificationCenter.default.post(name: .jumpToDefinition, object: nil)
            }
            .keyboardShortcut(KeyboardShortcuts.jumpToDefinition)

            Button("Show Symbol Navigator") {
                NotificationCenter.default.post(name: .showSymbolNavigator, object: nil)
            }
            .keyboardShortcut(KeyboardShortcuts.showSymbols)

            Divider()

            Button("Next Error") {
                NotificationCenter.default.post(name: .nextDiagnostic, object: nil)
            }
            .keyboardShortcut(KeyboardShortcuts.nextError)

            Button("Previous Error") {
                NotificationCenter.default.post(name: .previousDiagnostic, object: nil)
            }
            .keyboardShortcut(KeyboardShortcuts.previousError)
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

    private func saveCurrentFile() {
        guard let fileId = appState.selectedFileId,
              let index = appState.openFiles.firstIndex(where: { $0.id == fileId }) else {
            return
        }
        appState.openFiles[index].hasUnsavedChanges = false
        // Trigger save notification for persistence layer
        NotificationCenter.default.post(name: .saveFile, object: appState.openFiles[index])
    }

    private func closeCurrentFile() {
        guard let fileId = appState.selectedFileId else { return }
        appState.closeFile(id: fileId)
    }
}

// Notification names moved to Utilities/NotificationNames.swift

// MARK: - Go To Line View

struct GoToLineView: View {
    @Binding var isPresented: Bool
    @Binding var content: String
    @State private var lineNumberText = ""
    @FocusState private var isFocused: Bool

    var body: some View {
        VStack(spacing: 16) {
            Text("Go to Line")
                .font(.headline)

            TextField("Line number", text: $lineNumberText)
                .textFieldStyle(.roundedBorder)
                #if os(iOS)
                .keyboardType(.numberPad)
                #endif
                .focused($isFocused)
                .onSubmit {
                    goToLine()
                }

            HStack {
                Button("Cancel") {
                    isPresented = false
                }
                .keyboardShortcut(.escape)

                Spacer()

                Button("Go") {
                    goToLine()
                }
                .keyboardShortcut(.return)
                .disabled(lineNumberText.isEmpty)
            }
        }
        .padding()
        .frame(width: 250)
        .onAppear {
            isFocused = true
        }
    }

    private func goToLine() {
        guard let lineNumber = Int(lineNumberText), lineNumber > 0 else {
            return
        }

        let lines = content.components(separatedBy: "\n")
        guard lineNumber <= lines.count else {
            return
        }

        // Calculate character offset
        var offset = 0
        for i in 0..<(lineNumber - 1) {
            offset += lines[i].count + 1 // +1 for newline
        }

        NotificationCenter.default.post(
            name: .navigateToLine,
            object: SourceLocation(line: lineNumber, column: 1, length: 0)
        )

        isPresented = false
    }
}

// MARK: - Comment Toggle

extension String {
    func toggleLineComment(at range: Range<String.Index>?) -> String {
        let lines = self.components(separatedBy: "\n")
        guard !lines.isEmpty else { return self }

        // Get line indices to toggle
        var lineIndices: Set<Int> = []
        if let range = range {
            let startOffset = self.distance(from: self.startIndex, to: range.lowerBound)
            let endOffset = self.distance(from: self.startIndex, to: range.upperBound)

            var currentOffset = 0
            for (index, line) in lines.enumerated() {
                let lineEnd = currentOffset + line.count
                if currentOffset <= endOffset && lineEnd >= startOffset {
                    lineIndices.insert(index)
                }
                currentOffset = lineEnd + 1 // +1 for newline
            }
        } else {
            lineIndices.insert(0) // Default to first line
        }

        // Determine if we should add or remove comments
        let shouldComment = lineIndices.contains { index in
            !lines[index].trimmingCharacters(in: .whitespaces).hasPrefix("\\*")
        }

        // Toggle comments
        var newLines = lines
        for index in lineIndices {
            let line = lines[index]
            if shouldComment {
                // Add comment
                newLines[index] = "\\* " + line
            } else {
                // Remove comment
                if let commentRange = line.range(of: "\\* ") {
                    newLines[index] = String(line[commentRange.upperBound...])
                } else if let commentRange = line.range(of: "\\*") {
                    newLines[index] = String(line[commentRange.upperBound...])
                }
            }
        }

        return newLines.joined(separator: "\n")
    }
}
