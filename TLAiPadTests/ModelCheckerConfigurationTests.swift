import XCTest
@testable import MacTLA

/// Tests for model checker configuration and settings
final class ModelCheckerConfigurationTests: XCTestCase {

    // MARK: - Default Configuration Tests

    func testDefaultConfiguration() {
        let config = ModelChecker.Configuration.default

        // Check default values
        XCTAssertEqual(config.maxStates, 1_000_000)
        XCTAssertEqual(config.checkDeadlock, true)
        XCTAssertEqual(config.checkInvariants, true)
        XCTAssertEqual(config.checkLiveness, true)
    }

    func testConfigurationCustomization() {
        var config = ModelChecker.Configuration()
        config.maxStates = 50000
        config.checkDeadlock = false
        config.maxDepth = 50

        XCTAssertEqual(config.maxStates, 50000)
        XCTAssertEqual(config.checkDeadlock, false)
        XCTAssertEqual(config.maxDepth, 50)
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

        let checker = ModelChecker()
        var config = ModelChecker.Configuration()
        config.maxStates = 10
        config.checkDeadlock = false

        let result = await checker.verify(
            specification: source,
            config: config
        )

        // Should stop after maxStates
        XCTAssertEqual(result.status, .success)
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

        let checker = ModelChecker()
        var config = ModelChecker.Configuration()
        config.maxStates = 0
        config.checkDeadlock = false

        let result = await checker.verify(
            specification: source,
            config: config
        )

        // With maxStates = 0, behavior depends on implementation
        // Either completes immediately or explores no states
        XCTAssertNotEqual(result.status, .error)
    }

    // MARK: - Max Depth Limit Tests

    func testMaxDepthLimit() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Next == x' = x + 1

        Spec == Init /\\ [][Next]_x
        ====
        """

        let checker = ModelChecker()
        var config = ModelChecker.Configuration()
        config.maxDepth = 5
        config.maxStates = 1000
        config.checkDeadlock = false

        let result = await checker.verify(
            specification: source,
            config: config
        )

        // Should respect depth limit
        XCTAssertEqual(result.status, .success)
    }

    // MARK: - Invariant Configuration Tests

    func testInvariantChecking() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Next == x' = x + 1

        TypeOK == x >= 0

        Spec == Init /\\ [][Next]_x
        ====
        """

        let checker = ModelChecker()
        var config = ModelChecker.Configuration()
        config.maxStates = 10
        config.checkDeadlock = false
        config.checkInvariants = true

        let result = await checker.verify(
            specification: source,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "TypeOK")]
        )

        // Invariant should hold
        XCTAssertEqual(result.status, .success)
    }

    func testInvariantViolation() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Next == x' = x + 1

        TypeOK == x < 5

        Spec == Init /\\ [][Next]_x
        ====
        """

        let checker = ModelChecker()
        var config = ModelChecker.Configuration()
        config.maxStates = 20
        config.checkDeadlock = false
        config.checkInvariants = true

        let result = await checker.verify(
            specification: source,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "TypeOK")]
        )

        // Invariant should be violated when x reaches 5
        XCTAssertEqual(result.status, .failure)
    }

    // MARK: - Deadlock Configuration Tests

    func testDeadlockCheckingEnabled() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Next == x < 2 /\\ x' = x + 1

        Spec == Init /\\ [][Next]_x
        ====
        """

        let checker = ModelChecker()
        var config = ModelChecker.Configuration()
        config.maxStates = 20
        config.checkDeadlock = true

        let result = await checker.verify(
            specification: source,
            config: config
        )

        // Should detect deadlock when x reaches 2
        XCTAssertEqual(result.status, .failure)
    }

    func testDeadlockCheckingDisabled() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Next == x < 2 /\\ x' = x + 1

        Spec == Init /\\ [][Next]_x
        ====
        """

        let checker = ModelChecker()
        var config = ModelChecker.Configuration()
        config.maxStates = 20
        config.checkDeadlock = false

        let result = await checker.verify(
            specification: source,
            config: config
        )

        // Should succeed because deadlock checking is disabled
        XCTAssertEqual(result.status, .success)
    }

    // MARK: - Constant Override Tests

    func testConstantOverride() async throws {
        let source = """
        ---- MODULE Test ----
        CONSTANT N
        VARIABLE x

        Init == x = 0

        Next == x < N /\\ x' = x + 1

        TypeOK == x <= N

        Spec == Init /\\ [][Next]_x
        ====
        """

        let checker = ModelChecker()
        var config = ModelChecker.Configuration()
        config.maxStates = 20
        config.checkDeadlock = false

        let result = await checker.verify(
            specification: source,
            config: config,
            constants: [ModelChecker.ConstantOverride(name: "N", value: "3")],
            invariants: [ModelChecker.InvariantSpec(name: "TypeOK")]
        )

        // TypeOK should hold with N = 3
        XCTAssertEqual(result.status, .success)
    }

    // MARK: - Workers Configuration Tests

    func testSingleWorker() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Next == x' = (x + 1) % 5

        Spec == Init /\\ [][Next]_x
        ====
        """

        let checker = ModelChecker()
        var config = ModelChecker.Configuration()
        config.workers = 1
        config.maxStates = 20

        let result = await checker.verify(
            specification: source,
            config: config
        )

        XCTAssertEqual(result.status, .success)
    }
}
