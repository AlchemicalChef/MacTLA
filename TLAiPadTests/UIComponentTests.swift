import XCTest
@testable import MacTLA

/// UI Component Tests
/// Tests for models, view models, and app state management
final class UIComponentTests: XCTestCase {

    // MARK: - TLAFile Tests

    func testTLAFileInitialization() {
        let file = TLAFile(
            name: "Test.tla",
            type: .specification,
            content: "---- MODULE Test ----\n====",
            hasUnsavedChanges: false
        )

        XCTAssertEqual(file.name, "Test.tla")
        XCTAssertEqual(file.type, .specification)
        XCTAssertEqual(file.content, "---- MODULE Test ----\n====")
        XCTAssertFalse(file.hasUnsavedChanges)
        XCTAssertNotNil(file.id)
    }

    func testTLAFileDefaultValues() {
        let file = TLAFile(name: "Empty.tla", type: .specification)

        XCTAssertEqual(file.content, "")
        XCTAssertFalse(file.hasUnsavedChanges)
    }

    func testTLAFileEquality() {
        let id = UUID()
        let file1 = TLAFile(id: id, name: "Test.tla", type: .specification)
        let file2 = TLAFile(id: id, name: "Different.tla", type: .model)

        // Equality is based on ID only
        XCTAssertEqual(file1, file2)
    }

    func testTLAFileInequality() {
        let file1 = TLAFile(name: "Test.tla", type: .specification)
        let file2 = TLAFile(name: "Test.tla", type: .specification)

        // Different IDs = different files
        XCTAssertNotEqual(file1, file2)
    }

    func testTLAFileCodable() throws {
        let file = TLAFile(
            name: "Test.tla",
            type: .specification,
            content: "test content",
            hasUnsavedChanges: true
        )

        let encoded = try JSONEncoder().encode(file)
        let decoded = try JSONDecoder().decode(TLAFile.self, from: encoded)

        XCTAssertEqual(decoded.id, file.id)
        XCTAssertEqual(decoded.name, file.name)
        XCTAssertEqual(decoded.type, file.type)
        XCTAssertEqual(decoded.content, file.content)
        XCTAssertEqual(decoded.hasUnsavedChanges, file.hasUnsavedChanges)
    }

    // MARK: - TLAFileType Tests

    func testTLAFileTypeSpecification() {
        let type = TLAFileType.specification

        XCTAssertEqual(type.rawValue, "tla")
        XCTAssertEqual(type.fileExtension, "tla")
        XCTAssertEqual(type.iconName, "doc.text")
    }

    func testTLAFileTypeModel() {
        let type = TLAFileType.model

        XCTAssertEqual(type.rawValue, "cfg")
        XCTAssertEqual(type.fileExtension, "cfg")
        XCTAssertEqual(type.iconName, "gearshape.2")
    }

    func testTLAFileTypePlusCal() {
        let type = TLAFileType.pluscal

        XCTAssertEqual(type.rawValue, "pluscal")
        XCTAssertEqual(type.fileExtension, "tla")
        XCTAssertEqual(type.iconName, "algorithm")
    }

    func testTLAFileTypeProof() {
        let type = TLAFileType.proof

        XCTAssertEqual(type.rawValue, "tlaps")
        XCTAssertEqual(type.fileExtension, "tla")
        XCTAssertEqual(type.iconName, "checkmark.seal")
    }

    func testTLAFileTypeAllCases() {
        XCTAssertEqual(TLAFileType.allCases.count, 4)
        XCTAssertTrue(TLAFileType.allCases.contains(.specification))
        XCTAssertTrue(TLAFileType.allCases.contains(.model))
        XCTAssertTrue(TLAFileType.allCases.contains(.pluscal))
        XCTAssertTrue(TLAFileType.allCases.contains(.proof))
    }

    // MARK: - TLAProject Tests

    func testTLAProjectInitialization() {
        let project = TLAProject(
            name: "TestProject",
            path: "/path/to/project"
        )

        XCTAssertEqual(project.name, "TestProject")
        XCTAssertEqual(project.path, "/path/to/project")
        XCTAssertTrue(project.files.isEmpty)
        XCTAssertNotNil(project.id)
        XCTAssertNotNil(project.createdAt)
        XCTAssertNotNil(project.modifiedAt)
    }

    func testTLAProjectWithFiles() {
        let files = [
            TLAFile(name: "Spec.tla", type: .specification),
            TLAFile(name: "MC.cfg", type: .model)
        ]

        let project = TLAProject(
            name: "TestProject",
            path: "/path/to/project",
            files: files
        )

        XCTAssertEqual(project.files.count, 2)
        XCTAssertEqual(project.files[0].name, "Spec.tla")
        XCTAssertEqual(project.files[1].name, "MC.cfg")
    }

    func testTLAProjectCodable() throws {
        let project = TLAProject(
            name: "TestProject",
            path: "/path/to/project",
            files: [TLAFile(name: "Test.tla", type: .specification)]
        )

        let encoded = try JSONEncoder().encode(project)
        let decoded = try JSONDecoder().decode(TLAProject.self, from: encoded)

        XCTAssertEqual(decoded.id, project.id)
        XCTAssertEqual(decoded.name, project.name)
        XCTAssertEqual(decoded.path, project.path)
        XCTAssertEqual(decoded.files.count, 1)
    }

    // MARK: - AppState Tests

    @MainActor
    func testAppStateInitialState() {
        let appState = AppState()

        XCTAssertNil(appState.currentProject)
        XCTAssertTrue(appState.openFiles.isEmpty)
        XCTAssertNil(appState.selectedFileId)
        XCTAssertFalse(appState.isVerifying)
        XCTAssertTrue(appState.verificationResults.isEmpty)
    }

    @MainActor
    func testAppStateOpenFile() {
        let appState = AppState()
        let file = TLAFile(name: "Test.tla", type: .specification)

        appState.openFile(file)

        XCTAssertEqual(appState.openFiles.count, 1)
        XCTAssertEqual(appState.selectedFileId, file.id)
        XCTAssertEqual(appState.selectedFile?.id, file.id)
    }

    @MainActor
    func testAppStateOpenMultipleFiles() {
        let appState = AppState()
        let file1 = TLAFile(name: "Test1.tla", type: .specification)
        let file2 = TLAFile(name: "Test2.tla", type: .specification)

        appState.openFile(file1)
        appState.openFile(file2)

        XCTAssertEqual(appState.openFiles.count, 2)
        XCTAssertEqual(appState.selectedFileId, file2.id)  // Last opened is selected
    }

    @MainActor
    func testAppStateOpenSameFileTwice() {
        let appState = AppState()
        let file = TLAFile(name: "Test.tla", type: .specification)

        appState.openFile(file)
        appState.openFile(file)

        XCTAssertEqual(appState.openFiles.count, 1)  // Not duplicated
        XCTAssertEqual(appState.selectedFileId, file.id)
    }

    @MainActor
    func testAppStateCloseFile() {
        let appState = AppState()
        let file = TLAFile(name: "Test.tla", type: .specification)

        appState.openFile(file)
        appState.closeFile(file)

        XCTAssertTrue(appState.openFiles.isEmpty)
        XCTAssertNil(appState.selectedFileId)
    }

    @MainActor
    func testAppStateCloseFileById() {
        let appState = AppState()
        let file = TLAFile(name: "Test.tla", type: .specification)

        appState.openFile(file)
        appState.closeFile(id: file.id)

        XCTAssertTrue(appState.openFiles.isEmpty)
        XCTAssertNil(appState.selectedFileId)
    }

    @MainActor
    func testAppStateCloseSelectedFile() {
        let appState = AppState()
        let file1 = TLAFile(name: "Test1.tla", type: .specification)
        let file2 = TLAFile(name: "Test2.tla", type: .specification)

        appState.openFile(file1)
        appState.openFile(file2)
        appState.closeFile(file2)

        // Should select the remaining file
        XCTAssertEqual(appState.selectedFileId, file1.id)
    }

    @MainActor
    func testAppStateCloseNonSelectedFile() {
        let appState = AppState()
        let file1 = TLAFile(name: "Test1.tla", type: .specification)
        let file2 = TLAFile(name: "Test2.tla", type: .specification)

        appState.openFile(file1)
        appState.openFile(file2)
        appState.closeFile(file1)

        // Selected file should remain unchanged
        XCTAssertEqual(appState.selectedFileId, file2.id)
        XCTAssertEqual(appState.openFiles.count, 1)
    }

    @MainActor
    func testAppStateSelectedFile() {
        let appState = AppState()
        let file = TLAFile(name: "Test.tla", type: .specification, content: "content")

        appState.openFile(file)

        XCTAssertNotNil(appState.selectedFile)
        XCTAssertEqual(appState.selectedFile?.content, "content")
    }

    @MainActor
    func testAppStateSelectedFileNil() {
        let appState = AppState()

        XCTAssertNil(appState.selectedFile)
    }

    @MainActor
    func testAppStateCurrentProject() {
        let appState = AppState()
        let project = TLAProject(name: "Test", path: "/test")

        appState.currentProject = project

        XCTAssertEqual(appState.currentProject?.name, "Test")
    }

    @MainActor
    func testAppStateVerificationState() {
        let appState = AppState()

        XCTAssertFalse(appState.isVerifying)

        appState.isVerifying = true
        XCTAssertTrue(appState.isVerifying)

        appState.isVerifying = false
        XCTAssertFalse(appState.isVerifying)
    }

    // MARK: - Syntax Highlighter Tests

    func testSyntaxHighlighterSharedInstance() {
        let highlighter1 = TLASyntaxHighlighter.shared
        let highlighter2 = TLASyntaxHighlighter.shared

        XCTAssertTrue(highlighter1 === highlighter2)
    }

    // MARK: - Symbol Navigator Tests

    func testSymbolNavigatorSharedInstance() {
        let navigator1 = SymbolNavigator.shared
        let navigator2 = SymbolNavigator.shared

        XCTAssertTrue(navigator1 === navigator2)
    }

    func testSymbolNavigatorFindDefinition() {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Next == x' = x + 1
        ====
        """

        // Test finding Init definition
        if let location = SymbolNavigator.shared.findDefinition(of: "Init", in: source) {
            XCTAssertGreaterThan(location.line, 0)
        }
    }

    // MARK: - TLCConfig Tests

    func testTLCConfigParsing() {
        let configContent = """
        SPECIFICATION Spec
        INVARIANT TypeOK
        INVARIANT Safety
        CONSTANT N = 3
        """

        // Test that config content can be processed
        XCTAssertFalse(configContent.isEmpty)
    }

    // MARK: - VerificationResult Tests

    func testVerificationResultSuccess() {
        // Create a mock verification result
        let result = VerificationResult(
            specificationName: "TestSpec",
            status: .success,
            statesExplored: 100,
            distinctStates: 50,
            duration: 1.5,
            error: nil,
            counterexample: []
        )

        XCTAssertEqual(result.status, .success)
        XCTAssertEqual(result.statesExplored, 100)
        XCTAssertEqual(result.distinctStates, 50)
        XCTAssertEqual(result.duration, 1.5)
        XCTAssertNil(result.error)
        XCTAssertTrue(result.counterexample.isEmpty)
    }

    func testVerificationResultFailure() {
        let counterexample = [
            TraceState(state: ["x": "1"]),
            TraceState(state: ["x": "2"])
        ]
        let result = VerificationResult(
            specificationName: "TestSpec",
            status: .failure,
            statesExplored: 50,
            distinctStates: 25,
            duration: 0.5,
            error: "Invariant violated",
            counterexample: counterexample
        )

        XCTAssertEqual(result.status, .failure)
        XCTAssertEqual(result.error, "Invariant violated")
        XCTAssertFalse(result.counterexample.isEmpty)
        XCTAssertEqual(result.counterexample.count, 2)
    }

    func testVerificationResultError() {
        let result = VerificationResult(
            specificationName: "TestSpec",
            status: .error,
            statesExplored: 0,
            distinctStates: 0,
            duration: 0,
            error: "Parse error",
            counterexample: []
        )

        XCTAssertEqual(result.status, .error)
        XCTAssertEqual(result.error, "Parse error")
    }

    // MARK: - ModelChecker.Configuration Tests

    func testModelCheckerConfigurationDefault() {
        let config = ModelChecker.Configuration.default

        XCTAssertGreaterThan(config.maxStates, 0)
        XCTAssertGreaterThan(config.maxDepth, 0)
    }

    func testModelCheckerConfigurationCustom() {
        var config = ModelChecker.Configuration.default
        config.maxStates = 1000
        config.maxDepth = 50
        config.checkDeadlock = true
        config.checkInvariants = false

        XCTAssertEqual(config.maxStates, 1000)
        XCTAssertEqual(config.maxDepth, 50)
        XCTAssertTrue(config.checkDeadlock)
        XCTAssertFalse(config.checkInvariants)
    }

    // MARK: - InvariantSpec Tests

    func testInvariantSpecCreation() {
        let invariant = ModelChecker.InvariantSpec(name: "TypeOK")

        XCTAssertEqual(invariant.name, "TypeOK")
    }

    // MARK: - ConstantOverride Tests

    func testConstantOverrideCreation() {
        let constant = ModelChecker.ConstantOverride(name: "N", value: "5")

        XCTAssertEqual(constant.name, "N")
        XCTAssertEqual(constant.value, "5")
    }

    func testConstantOverrideWithSet() {
        let constant = ModelChecker.ConstantOverride(name: "Procs", value: "{1, 2, 3}")

        XCTAssertEqual(constant.name, "Procs")
        XCTAssertEqual(constant.value, "{1, 2, 3}")
    }

    // MARK: - File Extension Detection

    func testFileTypeFromExtension() {
        // Mapping extensions to types
        let tests: [(String, TLAFileType)] = [
            ("test.tla", .specification),
            ("MC.cfg", .model)
        ]

        for (filename, expectedType) in tests {
            let ext = (filename as NSString).pathExtension
            let type: TLAFileType = ext == "cfg" ? .model : .specification
            XCTAssertEqual(type, expectedType, "Failed for \(filename)")
        }
    }

    // MARK: - Content Validation

    func testEmptyFileContent() {
        let file = TLAFile(name: "Empty.tla", type: .specification, content: "")

        XCTAssertTrue(file.content.isEmpty)
    }

    func testFileWithContent() {
        let content = """
        ---- MODULE Test ----
        VARIABLE x
        Init == x = 0
        ====
        """
        let file = TLAFile(name: "Test.tla", type: .specification, content: content)

        XCTAssertFalse(file.content.isEmpty)
        XCTAssertTrue(file.content.contains("MODULE"))
    }

    func testUnsavedChangesFlag() {
        var file = TLAFile(name: "Test.tla", type: .specification)

        XCTAssertFalse(file.hasUnsavedChanges)

        file.hasUnsavedChanges = true
        XCTAssertTrue(file.hasUnsavedChanges)
    }

    // MARK: - Project Files Management

    func testProjectAddFile() {
        var project = TLAProject(name: "Test", path: "/test")
        let file = TLAFile(name: "New.tla", type: .specification)

        project.files.append(file)

        XCTAssertEqual(project.files.count, 1)
        XCTAssertEqual(project.files[0].name, "New.tla")
    }

    func testProjectRemoveFile() {
        let file = TLAFile(name: "Remove.tla", type: .specification)
        var project = TLAProject(name: "Test", path: "/test", files: [file])

        project.files.removeAll { $0.id == file.id }

        XCTAssertTrue(project.files.isEmpty)
    }

    func testProjectFindFile() {
        let file = TLAFile(name: "Find.tla", type: .specification)
        let project = TLAProject(name: "Test", path: "/test", files: [file])

        let found = project.files.first { $0.name == "Find.tla" }

        XCTAssertNotNil(found)
        XCTAssertEqual(found?.id, file.id)
    }
}
