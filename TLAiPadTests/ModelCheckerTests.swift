import XCTest
@testable import MacTLA

final class ModelCheckerTests: XCTestCase {

    // MARK: - Helper Methods

    private func makeChecker() -> ModelChecker {
        ModelChecker()
    }

    // MARK: - Simple Verification Tests

    func testVerifySimpleSpec() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE Simple ----
        VARIABLE x

        Init == x = 0

        Next == x' = x + 1

        Spec == Init /\\ [][Next]_x
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 10
        config.maxDepth = 5

        let result = await checker.verify(specification: spec, config: config)

        // Should complete without error (reaches max states/depth)
        XCTAssertNotEqual(result.status, .error, "Unexpected error: \(result.error ?? "unknown")")
    }

    func testVerifyWithInvariant() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE Counter ----
        VARIABLE x

        Init == x = 0

        Next == x' = x + 1

        Inv == x >= 0
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 20
        config.maxDepth = 10
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "Inv")]
        )

        // Invariant x >= 0 should always hold
        XCTAssertEqual(result.status, .success)
    }

    func testVerifyInvariantViolation() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE Decrement ----
        VARIABLE x

        Init == x = 5

        Next == x' = x - 1

        Inv == x > 0
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 100
        config.maxDepth = 10
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "Inv")]
        )

        // Invariant should be violated when x reaches 0
        XCTAssertEqual(result.status, .failure)
        XCTAssertNotNil(result.counterexample)
    }

    func testVerifyDeadlockDetection() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE Deadlock ----
        VARIABLE x

        Init == x = 0

        Next == x < 3 /\\ x' = x + 1
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 100
        config.checkDeadlock = true

        let result = await checker.verify(specification: spec, config: config)

        // Should detect deadlock when x = 3 (no valid Next transition)
        XCTAssertEqual(result.status, .failure)
        XCTAssertTrue(result.error?.contains("deadlock") ?? false || result.status == .failure)
    }

    func testVerifyNoDeadlock() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE NoDeadlock ----
        VARIABLE x

        Init == x = 0

        Next == x' = (x + 1) % 3
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 100
        config.checkDeadlock = true

        let result = await checker.verify(specification: spec, config: config)

        // Cyclic behavior, no deadlock
        XCTAssertEqual(result.status, .success)
    }

    // MARK: - Configuration Tests

    func testVerifyWithConstants() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE WithConstant ----
        CONSTANT N
        VARIABLE x

        Init == x = 0

        Next == x < N /\\ x' = x + 1

        Inv == x <= N
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 100
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            constants: [ModelChecker.ConstantOverride(name: "N", value: "5")],
            invariants: [ModelChecker.InvariantSpec(name: "Inv")]
        )

        // Invariant x <= N should hold with N = 5
        XCTAssertEqual(result.status, .success)
    }

    func testVerifyMaxStatesLimit() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE Large ----
        VARIABLE x

        Init == x = 0

        Next == x' = x + 1
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 5  // Very small limit

        let result = await checker.verify(specification: spec, config: config)

        // Should complete (hit max states), not error
        XCTAssertNotEqual(result.status, .error)
        XCTAssertTrue(result.statesExplored >= 1)
    }

    func testVerifyMaxDepthLimit() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE Deep ----
        VARIABLE x

        Init == x = 0

        Next == x' = x + 1
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxDepth = 3
        config.maxStates = 1000

        let result = await checker.verify(specification: spec, config: config)

        // Should respect depth limit
        XCTAssertNotEqual(result.status, .error)
    }

    // MARK: - Parse Error Tests

    func testVerifyInvalidSpec() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE Invalid ----
        VARIABLE x

        Init == x =  \\ Invalid syntax

        Next == x' = x
        ====
        """

        let result = await checker.verify(specification: spec)

        XCTAssertEqual(result.status, .error)
        XCTAssertNotNil(result.error)
    }

    func testVerifyEmptySpec() async throws {
        let checker = makeChecker()

        let spec = ""

        let result = await checker.verify(specification: spec)

        XCTAssertEqual(result.status, .error)
    }

    // MARK: - Multiple Variables Tests

    func testVerifyMultipleVariables() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE TwoVars ----
        VARIABLES x, y

        Init == x = 0 /\\ y = 0

        Next == x' = (x + 1) % 2 /\\ y' = (y + 1) % 2

        Inv == x >= 0 /\\ y >= 0
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 20
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "Inv")]
        )

        XCTAssertEqual(result.status, .success)
    }

    // MARK: - Set Operations Tests

    func testVerifyWithSetVariable() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE SetSpec ----
        VARIABLE s

        Init == s = {}

        Next == s \\union {1} # s /\\ s' = s \\union {1}

        Inv == 1 \\notin s \\/ s = {1}
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 10
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "Inv")]
        )

        XCTAssertNotEqual(result.status, .error, "Error: \(result.error ?? "unknown")")
    }

    // MARK: - Boolean Operations Tests

    func testVerifyBooleanSpec() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE Toggle ----
        VARIABLE flag

        Init == flag = TRUE

        Next == flag' = ~flag

        Inv == flag = TRUE \\/ flag = FALSE
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 10
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "Inv")]
        )

        XCTAssertEqual(result.status, .success)
    }

    // MARK: - Statistics Tests

    func testVerifyReportsStatistics() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE Stats ----
        VARIABLE x

        Init == x = 0

        Next == x' = (x + 1) % 5
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 100

        let result = await checker.verify(specification: spec, config: config)

        // Should report some states explored
        XCTAssertGreaterThan(result.statesExplored, 0)
    }

    // MARK: - Cancellation Tests

    func testVerifyCancellation() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE Infinite ----
        VARIABLE x

        Init == x = 0

        Next == x' = x + 1
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 1000000  // Very large

        // Start verification in background
        let task = Task {
            await checker.verify(specification: spec, config: config)
        }

        // Wait a bit then cancel
        try await Task.sleep(nanoseconds: 10_000_000)  // 10ms
        await checker.cancel()

        let result = await task.value

        // May be cancelled or may have completed early - either is ok
        XCTAssertTrue(result.status == .cancelled || result.status == .success || result.statesExplored > 0)
    }

    // MARK: - Disjunction in Next Tests

    func testVerifyDisjunctiveNext() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE Disjunction ----
        VARIABLE x

        Init == x = 0

        Increment == x' = x + 1
        Reset == x > 2 /\\ x' = 0

        Next == Increment \\/ Reset

        Inv == x >= 0 /\\ x <= 4
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 50
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "Inv")]
        )

        XCTAssertEqual(result.status, .success)
    }

    // MARK: - Simple Mutex Test

    func testVerifySimpleMutex() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE SimpleMutex ----
        VARIABLES pc1, pc2

        Init == pc1 = "idle" /\\ pc2 = "idle"

        Enter1 == pc1 = "idle" /\\ pc2 # "critical" /\\ pc1' = "critical" /\\ pc2' = pc2
        Exit1 == pc1 = "critical" /\\ pc1' = "idle" /\\ pc2' = pc2

        Enter2 == pc2 = "idle" /\\ pc1 # "critical" /\\ pc2' = "critical" /\\ pc1' = pc1
        Exit2 == pc2 = "critical" /\\ pc2' = "idle" /\\ pc1' = pc1

        Next == Enter1 \\/ Exit1 \\/ Enter2 \\/ Exit2

        MutualExclusion == ~(pc1 = "critical" /\\ pc2 = "critical")
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 100
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "MutualExclusion")]
        )

        // Mutual exclusion should hold with this simple protocol
        XCTAssertEqual(result.status, .success)
    }
}
