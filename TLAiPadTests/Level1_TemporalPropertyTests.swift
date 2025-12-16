import XCTest
@testable import MacTLA

/// Level 1: Temporal Property Checking Tests
/// Tests evaluation of temporal operators and model checking of temporal properties
final class Level1_TemporalPropertyTests: XCTestCase {

    private func makeChecker() -> ModelChecker { ModelChecker() }

    // MARK: - Always (Box) Operator

    func testAlwaysTrueProperty() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE AlwaysTrue ----
        VARIABLE x

        Init == x = 0

        Next == x' = (x + 1) % 5

        Inv == x >= 0

        Prop == []Inv
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

        XCTAssertEqual(result.status, .success, "[]Inv should hold")
    }

    func testAlwaysFalseProperty() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE AlwaysFalse ----
        VARIABLE x

        Init == x = 0

        Next == x' = (x + 1) % 5

        NeverThree == x # 3
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 20
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "NeverThree")]
        )

        XCTAssertEqual(result.status, .failure, "[]NeverThree should fail (x reaches 3)")
    }

    // MARK: - Eventually (Diamond) Operator

    func testEventuallyReachable() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE EventuallyReach ----
        VARIABLE x

        Init == x = 0

        Next == x < 5 /\\ x' = x + 1

        ReachesFive == x = 5
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 20
        config.checkDeadlock = false  // Allow termination

        let result = await checker.verify(specification: spec, config: config)

        // The state x = 5 should be reachable
        XCTAssertNotEqual(result.status, .error)
    }

    // MARK: - Safety Properties

    func testSafetyNeverViolated() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE SafetyOK ----
        VARIABLE counter

        Init == counter = 0

        Increment == counter' = counter + 1
        Decrement == counter > 0 /\\ counter' = counter - 1

        Next == Increment \\/ Decrement

        NonNegative == counter >= 0
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 50
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "NonNegative")]
        )

        XCTAssertEqual(result.status, .success, "Counter should never go negative")
    }

    func testSafetyViolated() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE SafetyBad ----
        VARIABLE counter

        Init == counter = 0

        Increment == counter' = counter + 1
        Decrement == counter' = counter - 1  \\ Bug: no guard

        Next == Increment \\/ Decrement

        NonNegative == counter >= 0
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 50
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "NonNegative")]
        )

        XCTAssertEqual(result.status, .failure, "Counter can go negative with buggy Decrement")
        XCTAssertNotNil(result.counterexample)
    }

    // MARK: - Liveness Properties (Limited)

    func testLivenessEventuallyTerminates() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE Terminates ----
        VARIABLE x

        Init == x = 0

        Next == x < 10 /\\ x' = x + 1

        Done == x = 10
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 20
        config.checkDeadlock = false

        let result = await checker.verify(specification: spec, config: config)

        // Should explore to termination (x = 10)
        XCTAssertNotEqual(result.status, .error)
        XCTAssertGreaterThanOrEqual(result.statesExplored, 11)
    }

    // MARK: - Stuttering Steps

    func testStutteringAllowed() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE Stuttering ----
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

        XCTAssertNotEqual(result.status, .error)
    }

    // MARK: - Action Properties

    func testActionFormula() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE ActionTest ----
        VARIABLE x

        Init == x = 0

        Next == x' = (x + 1) % 3

        TypeOK == x \\in {0, 1, 2}
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 20
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "TypeOK")]
        )

        XCTAssertEqual(result.status, .success)
    }

    // MARK: - Multiple Invariants

    func testMultipleInvariantsAllPass() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE MultiInv ----
        VARIABLES x, y

        Init == x = 0 /\\ y = 0

        Next == x' = (x + 1) % 5 /\\ y' = (y + 1) % 3

        Inv1 == x >= 0
        Inv2 == y >= 0
        Inv3 == x < 5 /\\ y < 3
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 50
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            invariants: [
                ModelChecker.InvariantSpec(name: "Inv1"),
                ModelChecker.InvariantSpec(name: "Inv2"),
                ModelChecker.InvariantSpec(name: "Inv3")
            ]
        )

        XCTAssertEqual(result.status, .success, "All invariants should hold")
    }

    func testMultipleInvariantsOneFails() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE MultiInvFail ----
        VARIABLE x

        Init == x = 0

        Next == x' = (x + 1) % 10

        Inv1 == x >= 0
        Inv2 == x < 5  \\ This will fail when x reaches 5
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 50
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            invariants: [
                ModelChecker.InvariantSpec(name: "Inv1"),
                ModelChecker.InvariantSpec(name: "Inv2")
            ]
        )

        XCTAssertEqual(result.status, .failure, "Inv2 should fail")
    }

    // MARK: - Cyclic State Spaces

    func testCyclicStateSpace() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE Cyclic ----
        VARIABLE state

        Init == state = "A"

        ToB == state = "A" /\\ state' = "B"
        ToC == state = "B" /\\ state' = "C"
        ToA == state = "C" /\\ state' = "A"

        Next == ToB \\/ ToC \\/ ToA

        TypeOK == state \\in {"A", "B", "C"}
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 20
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "TypeOK")]
        )

        XCTAssertEqual(result.status, .success)
        // Should find exactly 3 distinct states
        XCTAssertEqual(result.statesExplored, 3, "Should find exactly 3 states in cycle")
    }

    // MARK: - Branching State Spaces

    func testBranchingStateSpace() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE Branching ----
        VARIABLE x

        Init == x = 0

        GoLeft == x' = x - 1
        GoRight == x' = x + 1
        Stay == x' = x

        Next == GoLeft \\/ GoRight \\/ Stay

        Bounded == x >= -5 /\\ x <= 5
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 100
        config.maxDepth = 5
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "Bounded")]
        )

        // With depth 5, we can reach x in [-5, 5]
        XCTAssertEqual(result.status, .success)
        XCTAssertGreaterThan(result.statesExplored, 1)
    }

    // MARK: - State Space with Sets

    func testSetVariableStateSpace() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE SetVar ----
        VARIABLE items

        Init == items = {}

        Add == items' = items \\union {1}
        Remove == 1 \\in items /\\ items' = items \\ {1}

        Next == Add \\/ Remove

        TypeOK == items \\subseteq {1}
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 10
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "TypeOK")]
        )

        XCTAssertEqual(result.status, .success)
        // Two states: {} and {1}
        XCTAssertEqual(result.statesExplored, 2)
    }

    // MARK: - Counterexample Generation

    func testCounterexampleProvided() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE CounterEx ----
        VARIABLE x

        Init == x = 0

        Next == x' = x + 1

        SmallX == x < 3
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 10
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "SmallX")]
        )

        XCTAssertEqual(result.status, .failure)
        XCTAssertFalse(result.counterexample.isEmpty, "Should provide counterexample")

        // Counterexample should show path from x=0 to x=3
        XCTAssertGreaterThan(result.counterexample.count, 0)
    }

    // MARK: - Complex Temporal Formulas

    func testComplexInvariant() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE Complex ----
        VARIABLES x, y

        Init == x = 0 /\\ y = 0

        IncX == x' = x + 1 /\\ y' = y
        IncY == y' = y + 1 /\\ x' = x

        Next == IncX \\/ IncY

        Inv == (x = 0 \\/ x > 0) /\\ (y = 0 \\/ y > 0) /\\ x + y < 10
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 50
        config.maxDepth = 5
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "Inv")]
        )

        XCTAssertEqual(result.status, .success)
    }
}
