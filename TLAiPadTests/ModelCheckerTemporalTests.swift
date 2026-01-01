import XCTest
@testable import MacTLA

/// Extended temporal property tests for ModelChecker
final class ModelCheckerTemporalTests: XCTestCase {

    // MARK: - Always Tests

    func testAlwaysHolds() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Next == x' = (x + 1) % 5

        Inv == x >= 0 /\\ x < 5

        Spec == Init /\\ [][Next]_x
        ====
        """

        let checker = ModelChecker()
        var config = ModelChecker.Configuration()
        config.maxStates = 20

        let result = await checker.verify(
            specification: source,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "Inv")]
        )

        // Invariant should hold for all states
        XCTAssertEqual(result.status, .success)
    }

    func testAlwaysViolation() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Next == x' = x + 1

        Inv == x < 5

        Spec == Init /\\ [][Next]_x
        ====
        """

        let checker = ModelChecker()
        var config = ModelChecker.Configuration()
        config.maxStates = 20

        let result = await checker.verify(
            specification: source,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "Inv")]
        )

        // Invariant x < 5 should be violated when x reaches 5
        XCTAssertEqual(result.status, .failure)
    }

    // MARK: - Eventually Tests

    func testEventuallyHolds() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Inc == x < 3 /\\ x' = x + 1

        Next == Inc

        Spec == Init /\\ [][Next]_x /\\ WF_x(Inc)

        Liveness == <>(x = 3)
        ====
        """

        let checker = ModelChecker()
        var config = ModelChecker.Configuration()
        config.maxStates = 20
        config.checkLiveness = true

        let result = await checker.verify(
            specification: source,
            config: config,
            properties: [ModelChecker.PropertySpec(name: "Liveness")]
        )

        // x eventually reaches 3 with weak fairness
        XCTAssertEqual(result.status, .success)
    }

    // MARK: - Deadlock Tests

    func testDeadlockDetection() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Next == x < 3 /\\ x' = x + 1

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

        // System deadlocks when x reaches 3
        XCTAssertEqual(result.status, .failure)
    }

    func testNoDeadlockWithStuttering() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Inc == x < 3 /\\ x' = x + 1

        Stutter == x' = x

        Next == Inc \\/ Stutter

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

        // No deadlock because stuttering is always possible
        XCTAssertEqual(result.status, .success)
    }

    // MARK: - Bounded Model Checking

    func testBoundedModelChecking() async throws {
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
        config.maxStates = 10  // Bound to 10 states
        config.checkDeadlock = false  // Disable deadlock check - infinite spec

        let result = await checker.verify(
            specification: source,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "TypeOK")]
        )

        // TypeOK holds in all explored states
        XCTAssertEqual(result.status, .success)
        XCTAssertLessThanOrEqual(result.statesExplored, 10)
    }

    // MARK: - Multiple Invariants

    func testMultipleInvariants() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x, y

        Init == x = 0 /\\ y = 0

        Next == x' = (x + 1) % 3 /\\ y' = (y + 1) % 4

        InvX == x >= 0 /\\ x < 3
        InvY == y >= 0 /\\ y < 4
        InvSum == x + y < 10

        Spec == Init /\\ [][Next]_<<x, y>>
        ====
        """

        let checker = ModelChecker()
        var config = ModelChecker.Configuration()
        config.maxStates = 50

        let result = await checker.verify(
            specification: source,
            config: config,
            invariants: [
                ModelChecker.InvariantSpec(name: "InvX"),
                ModelChecker.InvariantSpec(name: "InvY"),
                ModelChecker.InvariantSpec(name: "InvSum")
            ]
        )

        // All invariants should hold
        XCTAssertEqual(result.status, .success)
    }

    // MARK: - State Space Exhaustion

    func testStateSpaceExhausted() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x \\in {0, 1, 2}

        Next == x' \\in {0, 1, 2}

        TypeOK == x \\in {0, 1, 2}

        Spec == Init /\\ [][Next]_x
        ====
        """

        let checker = ModelChecker()
        var config = ModelChecker.Configuration()
        config.maxStates = 100
        config.checkDeadlock = false

        let result = await checker.verify(
            specification: source,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "TypeOK")]
        )

        // Finite state space should be fully explored
        XCTAssertEqual(result.status, .success)
        // Exactly 3 distinct states
        XCTAssertEqual(result.distinctStates, 3)
    }
}
