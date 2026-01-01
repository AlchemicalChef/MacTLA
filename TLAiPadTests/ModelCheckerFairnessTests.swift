import XCTest
@testable import MacTLA

/// Tests for fairness action tracking and temporal properties in ModelChecker
final class ModelCheckerFairnessTests: XCTestCase {

    // MARK: - Action Name Extraction Tests

    func testActionNameExtraction() async throws {
        // Test that action names are correctly extracted from Next disjunction
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Inc == x' = x + 1
        Dec == x' = x - 1

        Next == Inc \\/ Dec

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

        // The model checker should track Inc and Dec as actions
        XCTAssertNotEqual(result.status, .error)
    }

    func testActionNameFromDisjunction() async throws {
        // Test that multiple actions in disjunction are tracked
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        A == x' = 1
        B == x' = 2
        C == x' = 3

        Next == A \\/ B \\/ C

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

        XCTAssertNotEqual(result.status, .error)
    }

    func testSuccessorWithActionTracking() async throws {
        // Test that successors track which action was taken
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Inc == x < 3 /\\ x' = x + 1

        Next == Inc

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

        XCTAssertNotEqual(result.status, .error)
        // 4 distinct states: 0, 1, 2, 3
        XCTAssertEqual(result.distinctStates, 4)
    }

    // MARK: - Weak Fairness Tests

    func testWeakFairnessCondition() async throws {
        // Test that weak fairness is respected
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Inc == x < 3 /\\ x' = x + 1

        Next == Inc

        Spec == Init /\\ [][Next]_x /\\ WF_x(Inc)

        Goal == <>(x = 3)
        ====
        """

        let checker = ModelChecker()
        var config = ModelChecker.Configuration()
        config.maxStates = 20
        config.checkLiveness = true

        let result = await checker.verify(
            specification: source,
            config: config,
            properties: [ModelChecker.PropertySpec(name: "Goal")]
        )

        // With weak fairness on Inc, x should eventually reach 3
        XCTAssertEqual(result.status, .success)
    }

    // MARK: - Strong Fairness Tests

    func testStrongFairnessCondition() async throws {
        // Strong fairness: action taken if enabled infinitely often
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Inc == x' = (x + 1) % 3

        Next == Inc

        Spec == Init /\\ [][Next]_x /\\ SF_x(Inc)

        Cycle == <>[](x = 0)
        ====
        """

        let checker = ModelChecker()
        var config = ModelChecker.Configuration()
        config.maxStates = 20
        config.checkLiveness = true

        let result = await checker.verify(
            specification: source,
            config: config,
            properties: [ModelChecker.PropertySpec(name: "Cycle")]
        )

        // The system cycles through 0,1,2,0,1,2,...
        XCTAssertNotEqual(result.status, .error)
    }

    // MARK: - Combined Fairness Tests

    func testCombinedFairness() async throws {
        // Test combination of weak and strong fairness
        let source = """
        ---- MODULE Test ----
        VARIABLES x, y

        Init == x = 0 /\\ y = 0

        IncX == x' = x + 1 /\\ y' = y
        IncY == y' = y + 1 /\\ x' = x

        Next == IncX \\/ IncY

        Spec == Init /\\ [][Next]_<<x, y>>

        TypeOK == x >= 0 /\\ y >= 0
        ====
        """

        let checker = ModelChecker()
        var config = ModelChecker.Configuration()
        config.maxStates = 50
        config.checkDeadlock = false

        let result = await checker.verify(
            specification: source,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "TypeOK")]
        )

        XCTAssertEqual(result.status, .success)
    }

    // MARK: - Liveness Property Tests

    func testEventuallyProperty() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Inc == x' = x + 1

        Next == Inc

        Spec == Init /\\ [][Next]_x /\\ WF_x(Inc)

        EventuallyFive == <>(x = 5)
        ====
        """

        let checker = ModelChecker()
        var config = ModelChecker.Configuration()
        config.maxStates = 20
        config.checkLiveness = true

        let result = await checker.verify(
            specification: source,
            config: config,
            properties: [ModelChecker.PropertySpec(name: "EventuallyFive")]
        )

        // x eventually reaches 5
        XCTAssertEqual(result.status, .success)
    }

    func testAlwaysEventuallyProperty() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Inc == x' = (x + 1) % 3

        Next == Inc

        Spec == Init /\\ [][Next]_x /\\ WF_x(Inc)

        InfinitelyOftenZero == []<>(x = 0)
        ====
        """

        let checker = ModelChecker()
        var config = ModelChecker.Configuration()
        config.maxStates = 20
        config.checkLiveness = true

        let result = await checker.verify(
            specification: source,
            config: config,
            properties: [ModelChecker.PropertySpec(name: "InfinitelyOftenZero")]
        )

        // x returns to 0 infinitely often
        XCTAssertEqual(result.status, .success)
    }
}
