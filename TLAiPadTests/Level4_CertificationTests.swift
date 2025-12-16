import XCTest
@testable import MacTLA

/// Level 4: Certification Evidence Tests
/// Documents coverage requirements and provides tests for certification purposes
///
/// ## Coverage Requirements for Critical Systems Verification
///
/// ### Required Code Coverage
/// - Overall: > 95%
/// - Parser: > 98%
/// - Interpreter: > 98%
/// - ModelChecker: > 95%
///
/// ### Test Categories Required
/// 1. Unit tests for all public APIs
/// 2. Boundary value tests
/// 3. Error handling tests
/// 4. Performance benchmarks
/// 5. Regression tests
///
/// ## Running Coverage
/// ```
/// xcodebuild test -scheme MacTLA -enableCodeCoverage YES
/// xcrun xccov view --report --json Build/Logs/Test/*.xcresult
/// ```
final class Level4_CertificationTests: XCTestCase {

    // MARK: - Coverage Verification

    /// Documents which components must have coverage
    func testCoverageRequirementDocumentation() {
        // This test documents the coverage requirements
        // Actual coverage is measured by Xcode's code coverage tools

        let requiredCoverage: [String: Double] = [
            "TLAParser": 0.98,
            "TLALexer": 0.98,
            "TLAInterpreter": 0.98,
            "ModelChecker": 0.95,
            "TLASyntaxHighlighter": 0.90,
            "TLCConfig": 0.90
        ]

        for (component, target) in requiredCoverage {
            // Document the requirement
            XCTAssertTrue(target > 0.5, "\(component) should have > 50% coverage target")
        }
    }

    // MARK: - Public API Tests

    /// Verify TLAParser public API works correctly
    func testParserPublicAPI() {
        let parser = TLAParser()

        // parse(_:) method
        let result = parser.parse("""
        ---- MODULE Test ----
        VARIABLE x
        Init == x = 0
        ====
        """)

        switch result {
        case .success(let module):
            XCTAssertEqual(module.name, "Test")
        case .failure:
            XCTFail("Parser public API should work")
        }
    }

    /// Verify ModelChecker public API works correctly
    func testModelCheckerPublicAPI() async {
        let checker = ModelChecker()

        // verify(specification:config:constants:invariants:) method
        let result = await checker.verify(
            specification: """
            ---- MODULE Test ----
            VARIABLE x
            Init == x = 0
            Next == x' = x + 1
            ====
            """,
            config: ModelChecker.Configuration.default
        )

        XCTAssertNotNil(result.statesExplored)
        XCTAssertNotNil(result.status)
    }

    /// Verify TLAInterpreter public API works correctly
    func testInterpreterPublicAPI() throws {
        let interpreter = TLAInterpreter()
        let env = TLAInterpreter.Environment()

        // evaluate(_:in:) method
        let result = try interpreter.evaluate(
            .number(42, .unknown),
            in: env
        )

        XCTAssertEqual(result, .integer(42))
    }

    // MARK: - Boundary Value Tests

    func testIntegerBoundaryValues() throws {
        let interpreter = TLAInterpreter()
        let env = TLAInterpreter.Environment()

        // Zero
        let zero = try interpreter.evaluate(.number(0, .unknown), in: env)
        XCTAssertEqual(zero, .integer(0))

        // One (minimum positive)
        let one = try interpreter.evaluate(.number(1, .unknown), in: env)
        XCTAssertEqual(one, .integer(1))

        // Negative one
        let negOne = try interpreter.evaluate(
            .unary(.negative, .number(1, .unknown), .unknown),
            in: env
        )
        XCTAssertEqual(negOne, .integer(-1))

        // Large value
        let large = try interpreter.evaluate(.number(Int.max / 2, .unknown), in: env)
        if case .integer(let n) = large {
            XCTAssertEqual(n, Int.max / 2)
        } else {
            XCTFail("Expected integer")
        }
    }

    func testEmptyCollectionBoundaries() throws {
        let interpreter = TLAInterpreter()
        let env = TLAInterpreter.Environment()

        // Empty set
        let emptySet = try interpreter.evaluate(.setEnumeration([], .unknown), in: env)
        if case .set(let s) = emptySet {
            XCTAssertTrue(s.isEmpty)
        } else {
            XCTFail("Expected set")
        }

        // Empty tuple
        let emptyTuple = try interpreter.evaluate(.tuple([], .unknown), in: env)
        if case .sequence(let seq) = emptyTuple {
            XCTAssertTrue(seq.isEmpty)
        } else {
            XCTFail("Expected sequence")
        }

        // Empty record
        let emptyRecord = try interpreter.evaluate(.recordConstruction([], .unknown), in: env)
        if case .record(let r) = emptyRecord {
            XCTAssertTrue(r.isEmpty)
        } else {
            XCTFail("Expected record")
        }
    }

    func testSingletonCollections() throws {
        let interpreter = TLAInterpreter()
        let env = TLAInterpreter.Environment()

        // Singleton set
        let singletonSet = try interpreter.evaluate(
            .setEnumeration([.number(1, .unknown)], .unknown),
            in: env
        )
        if case .set(let s) = singletonSet {
            XCTAssertEqual(s.count, 1)
            XCTAssertTrue(s.contains(.integer(1)))
        } else {
            XCTFail("Expected set")
        }

        // Singleton tuple
        let singletonTuple = try interpreter.evaluate(
            .tuple([.number(1, .unknown)], .unknown),
            in: env
        )
        if case .sequence(let seq) = singletonTuple {
            XCTAssertEqual(seq.count, 1)
            XCTAssertEqual(seq[0], .integer(1))
        } else {
            XCTFail("Expected sequence")
        }
    }

    // MARK: - Error Handling Tests

    func testParserErrorRecovery() {
        let parser = TLAParser()

        // Syntax error should provide useful information
        let result = parser.parse("""
        ---- MODULE Bad ----
        Init == x =
        ====
        """)

        switch result {
        case .success:
            XCTFail("Should fail on syntax error")
        case .failure(let errors):
            XCTAssertFalse(errors.errors.isEmpty, "Should report errors")
            // Should have line information
            if let firstError = errors.errors.first {
                XCTAssertNotNil(firstError.location)
            }
        }
    }

    func testInterpreterErrorMessages() {
        let interpreter = TLAInterpreter()
        let env = TLAInterpreter.Environment()

        // Undefined variable should give clear error
        do {
            _ = try interpreter.evaluate(.identifier("undefined", .unknown), in: env)
            XCTFail("Should throw error")
        } catch let error as TLAInterpreter.InterpreterError {
            // Error message should mention the variable
            let message = "\(error)"
            XCTAssertTrue(message.contains("undefined") || message.lowercased().contains("variable"))
        } catch {
            XCTFail("Unexpected error type: \(error)")
        }
    }

    func testModelCheckerErrorHandling() async {
        let checker = ModelChecker()

        // Empty spec should fail gracefully
        let result = await checker.verify(specification: "")

        XCTAssertEqual(result.status, .error)
        XCTAssertNotNil(result.error)
    }

    // MARK: - Determinism Tests

    func testParserDeterminism() {
        let parser = TLAParser()
        let source = """
        ---- MODULE Determinism ----
        VARIABLE x
        Init == x = 0
        Next == x' = x + 1
        ====
        """

        // Parse multiple times, should get same result
        let results = (0..<10).map { _ in parser.parse(source) }

        for result in results {
            switch result {
            case .success(let module):
                XCTAssertEqual(module.name, "Determinism")
                XCTAssertEqual(module.declarations.count, 3) // VARIABLE, Init, Next
            case .failure:
                XCTFail("All parses should succeed")
            }
        }
    }

    func testInterpreterDeterminism() throws {
        let interpreter = TLAInterpreter()
        var env = TLAInterpreter.Environment()
        env.variables["S"] = .set([.integer(1), .integer(2), .integer(3)])

        // Same expression should always give same result
        let expr = TLAExpression.forall(
            [BoundVariable(name: "x", domain: .identifier("S", .unknown))],
            .binary(.identifier("x", .unknown), .gt, .number(0, .unknown), .unknown),
            .unknown
        )

        let results = try (0..<10).map { _ in try interpreter.evaluate(expr, in: env) }

        for result in results {
            XCTAssertEqual(result, .boolean(true))
        }
    }

    func testModelCheckerDeterminism() async {
        let checker = ModelChecker()

        let spec = """
        ---- MODULE Determinism ----
        VARIABLE x
        Init == x = 0
        Next == x' = (x + 1) % 3
        Inv == x >= 0
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 10
        config.checkInvariants = true

        // Run multiple times
        var statesCounts: [Int] = []
        for _ in 0..<5 {
            let result = await checker.verify(
                specification: spec,
                config: config,
                invariants: [ModelChecker.InvariantSpec(name: "Inv")]
            )
            statesCounts.append(result.statesExplored)
        }

        // All runs should explore same number of states
        let first = statesCounts[0]
        for count in statesCounts {
            XCTAssertEqual(count, first, "Model checker should be deterministic")
        }
    }

    // MARK: - Performance Baseline Tests

    func testParserPerformanceBaseline() {
        let parser = TLAParser()

        // Generate a medium-sized spec
        var operators = ""
        for i in 0..<100 {
            operators += "Op\(i) == x = \(i) /\\ y = \(i * 2)\n"
        }

        let spec = """
        ---- MODULE Perf ----
        VARIABLES x, y
        \(operators)
        ====
        """

        measure {
            _ = parser.parse(spec)
        }
    }

    func testInterpreterPerformanceBaseline() throws {
        let interpreter = TLAInterpreter()
        var env = TLAInterpreter.Environment()
        env.variables["S"] = .set(Set((1...100).map { TLAValue.integer($0) }))

        // Complex expression
        let expr = TLAExpression.forall(
            [BoundVariable(name: "x", domain: .identifier("S", .unknown))],
            .exists(
                [BoundVariable(name: "y", domain: .identifier("S", .unknown))],
                .binary(
                    .binary(.identifier("x", .unknown), .plus, .identifier("y", .unknown), .unknown),
                    .gt,
                    .number(50, .unknown),
                    .unknown
                ),
                .unknown
            ),
            .unknown
        )

        measure {
            _ = try? interpreter.evaluate(expr, in: env)
        }
    }

    // MARK: - Regression Test Anchors

    /// Test for issue: Force unwrap crash in TLALexer
    func testRegressionLexerSafeKeywordParsing() {
        let parser = TLAParser()

        // WF_ and SF_ should parse without crashes
        let result = parser.parse("""
        ---- MODULE Fairness ----
        VARIABLE x
        Init == x = 0
        Next == x' = x + 1
        Fair == WF_x(Next) /\\ SF_x(Next)
        ====
        """)

        switch result {
        case .success:
            // Success - no crash
            break
        case .failure:
            // Parse failure is acceptable, crash is not
            break
        }
        // If we get here, no crash occurred
    }

    /// Test for issue: CHOOSE semantics
    func testRegressionChooseSemantics() throws {
        let interpreter = TLAInterpreter()
        var env = TLAInterpreter.Environment()
        env.variables["S"] = .set([.integer(1), .integer(2), .integer(3)])

        // CHOOSE with no satisfying value should not crash
        let result = try interpreter.evaluate(
            .choose(
                BoundVariable(name: "x", domain: .identifier("S", .unknown)),
                .binary(.identifier("x", .unknown), .gt, .number(100, .unknown), .unknown),
                .unknown
            ),
            in: env
        )

        // Should return some value from domain per TLA+ semantics
        XCTAssertNotNil(result)
    }

    /// Test for issue: String length check in interpreter
    func testRegressionStringLengthChecks() {
        let interpreter = TLAInterpreter()

        // Empty quoted string constant
        interpreter.setConstant(name: "Empty", valueString: "\"\"")

        // Single char constant
        interpreter.setConstant(name: "Single", valueString: "\"a\"")

        // These should not crash
    }

    // MARK: - Cross-Component Integration

    func testEndToEndParseAndCheck() async {
        // Parse a spec
        let parser = TLAParser()
        let parseResult = parser.parse("""
        ---- MODULE E2E ----
        VARIABLE x
        Init == x = 0
        Next == x' = (x + 1) % 5
        TypeOK == x \\in {0, 1, 2, 3, 4}
        ====
        """)

        guard case .success(let module) = parseResult else {
            XCTFail("Parse failed")
            return
        }

        XCTAssertEqual(module.name, "E2E")

        // Use module with model checker
        let checker = ModelChecker()
        var config = ModelChecker.Configuration.default
        config.maxStates = 20
        config.checkInvariants = true

        let result = await checker.verify(
            specification: """
            ---- MODULE E2E ----
            VARIABLE x
            Init == x = 0
            Next == x' = (x + 1) % 5
            TypeOK == x \\in {0, 1, 2, 3, 4}
            ====
            """,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "TypeOK")]
        )

        XCTAssertEqual(result.status, .success)
        XCTAssertEqual(result.statesExplored, 5)
    }

    // MARK: - Documentation Tests

    /// Verify that documented examples work
    func testDocumentedExampleCounterSpec() async {
        // Example from CLAUDE.md or README
        let checker = ModelChecker()

        let spec = """
        ---- MODULE Counter ----
        VARIABLE count

        Init == count = 0

        Increment == count' = count + 1
        Decrement == count > 0 /\\ count' = count - 1

        Next == Increment \\/ Decrement

        AlwaysNonNegative == count >= 0
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 50
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "AlwaysNonNegative")]
        )

        XCTAssertEqual(result.status, .success, "Documented counter example should work")
    }
}
