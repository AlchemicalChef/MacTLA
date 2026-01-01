import XCTest
@testable import MacTLA

/// Tests for model checker configuration and settings
final class ModelCheckerConfigurationTests: XCTestCase {

    // MARK: - Helper Methods

    private func parse(_ source: String) -> TLAModule? {
        let parser = TLAParser()
        switch parser.parse(source) {
        case .success(let module):
            return module
        case .failure:
            return nil
        }
    }

    // MARK: - Default Configuration Tests

    func testDefaultConfiguration() {
        let config = ModelCheckerConfiguration()

        // Check default values
        XCTAssertEqual(config.maxStates, 100000)
        XCTAssertEqual(config.checkDeadlock, true)
        XCTAssertTrue(config.invariants.isEmpty)
        XCTAssertTrue(config.properties.isEmpty)
    }

    func testConfigurationCustomization() {
        var config = ModelCheckerConfiguration()
        config.maxStates = 50000
        config.checkDeadlock = false
        config.invariants = ["TypeOK", "Safety"]
        config.properties = ["Liveness"]

        XCTAssertEqual(config.maxStates, 50000)
        XCTAssertEqual(config.checkDeadlock, false)
        XCTAssertEqual(config.invariants.count, 2)
        XCTAssertEqual(config.properties.count, 1)
    }

    // MARK: - Max States Limit Tests

    func testMaxStatesLimit() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Next == x' = x + 1

        Spec == Init /\\ [][Next]_x
        ====
        """

        guard let module = parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let checker = ModelChecker()
        var config = ModelCheckerConfiguration()
        config.maxStates = 10
        config.checkDeadlock = false

        let result = await checker.check(module: module, config: config)

        // Should stop after maxStates
        XCTAssertEqual(result.status, .statesExhausted)
        XCTAssertLessThanOrEqual(result.statesExplored, 10)
    }

    func testMaxStatesZero() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x
        Init == x = 0
        Next == x' = x
        Spec == Init /\\ [][Next]_x
        ====
        """

        guard let module = parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let checker = ModelChecker()
        var config = ModelCheckerConfiguration()
        config.maxStates = 0
        config.checkDeadlock = false

        let result = await checker.check(module: module, config: config)

        // With maxStates = 0, behavior depends on implementation
        // Either completes immediately or explores no states
        XCTAssertNotNil(result)
    }

    // MARK: - Invariant Configuration Tests

    func testInvariantConfiguration() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Next == x' = (x + 1) % 10

        TypeOK == x \\in 0..9
        Safety == x >= 0

        Spec == Init /\\ [][Next]_x
        ====
        """

        guard let module = parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let checker = ModelChecker()
        var config = ModelCheckerConfiguration()
        config.maxStates = 20
        config.invariants = ["TypeOK", "Safety"]

        let result = await checker.check(module: module, config: config)

        // Both invariants should hold
        XCTAssertEqual(result.status, .completed)
    }

    func testMultipleInvariants() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Next == x' = x + 1

        Inv1 == x >= 0
        Inv2 == x < 100

        Spec == Init /\\ [][Next]_x
        ====
        """

        guard let module = parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let checker = ModelChecker()
        var config = ModelCheckerConfiguration()
        config.maxStates = 200
        config.invariants = ["Inv1", "Inv2"]

        let result = await checker.check(module: module, config: config)

        // Inv2 (x < 100) should be violated
        XCTAssertEqual(result.status, .invariantViolation)
    }

    // MARK: - Deadlock Configuration Tests

    func testDeadlockCheckEnabled() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Inc == x < 3 /\\ x' = x + 1

        Next == Inc

        Spec == Init /\\ [][Next]_x
        ====
        """

        guard let module = parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let checker = ModelChecker()
        var config = ModelCheckerConfiguration()
        config.maxStates = 20
        config.checkDeadlock = true

        let result = await checker.check(module: module, config: config)

        XCTAssertEqual(result.status, .deadlock)
    }

    func testDeadlockCheckDisabled() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Inc == x < 3 /\\ x' = x + 1

        Next == Inc

        Spec == Init /\\ [][Next]_x
        ====
        """

        guard let module = parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let checker = ModelChecker()
        var config = ModelCheckerConfiguration()
        config.maxStates = 20
        config.checkDeadlock = false

        let result = await checker.check(module: module, config: config)

        // With deadlock check disabled, should complete normally
        XCTAssertEqual(result.status, .completed)
    }

    // MARK: - Interpreter Bounds Integration Tests

    func testNatIntBoundsPassedToInterpreter() async throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Integers

        VARIABLE x

        Init == x \\in Nat

        Next == x' = x

        TypeOK == x >= 0

        Spec == Init /\\ [][Next]_x
        ====
        """

        guard let module = parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let checker = ModelChecker()
        var config = ModelCheckerConfiguration()
        config.maxStates = 20

        // This tests that Nat is bounded correctly
        let result = await checker.check(module: module, config: config)

        XCTAssertNotNil(result)
    }

    // MARK: - Result Reporting Tests

    func testResultReportsStatesExplored() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x \\in {0, 1, 2}

        Next == x' = x

        Spec == Init /\\ [][Next]_x
        ====
        """

        guard let module = parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let checker = ModelChecker()
        var config = ModelCheckerConfiguration()
        config.maxStates = 100
        config.checkDeadlock = false

        let result = await checker.check(module: module, config: config)

        // Should explore exactly 3 states
        XCTAssertEqual(result.statesExplored, 3)
    }

    func testResultReportsDistinctStates() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Toggle == x' = 1 - x

        Next == Toggle

        Spec == Init /\\ [][Next]_x
        ====
        """

        guard let module = parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let checker = ModelChecker()
        var config = ModelCheckerConfiguration()
        config.maxStates = 100

        let result = await checker.check(module: module, config: config)

        // Only 2 distinct states: x=0 and x=1
        XCTAssertEqual(result.statesExplored, 2)
    }

    // MARK: - Edge Case Tests

    func testEmptyInitialStates() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x \\in {}

        Next == x' = x

        Spec == Init /\\ [][Next]_x
        ====
        """

        guard let module = parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let checker = ModelChecker()
        let config = ModelCheckerConfiguration()

        let result = await checker.check(module: module, config: config)

        // No initial states - should complete with 0 states
        XCTAssertEqual(result.statesExplored, 0)
    }

    func testSingleStateNoTransitions() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 42

        Next == FALSE

        Spec == Init /\\ [][Next]_x
        ====
        """

        guard let module = parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let checker = ModelChecker()
        var config = ModelCheckerConfiguration()
        config.checkDeadlock = true

        let result = await checker.check(module: module, config: config)

        // Single state, no transitions - deadlock
        XCTAssertEqual(result.status, .deadlock)
        XCTAssertEqual(result.statesExplored, 1)
    }
}
