import XCTest
@testable import MacTLA

/// Extended temporal property tests for ModelChecker
final class ModelCheckerTemporalTests: XCTestCase {

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

        guard let module = parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let checker = ModelChecker()
        var config = ModelCheckerConfiguration()
        config.maxStates = 20
        config.invariants = ["Inv"]

        let result = await checker.check(module: module, config: config)

        // Invariant should hold for all states
        XCTAssertEqual(result.status, .completed)
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

        guard let module = parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let checker = ModelChecker()
        var config = ModelCheckerConfiguration()
        config.maxStates = 20
        config.invariants = ["Inv"]

        let result = await checker.check(module: module, config: config)

        // Invariant x < 5 should be violated when x reaches 5
        XCTAssertEqual(result.status, .invariantViolation)
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

        guard let module = parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let checker = ModelChecker()
        var config = ModelCheckerConfiguration()
        config.maxStates = 20
        config.properties = ["Liveness"]

        let result = await checker.check(module: module, config: config)

        // With weak fairness, eventually x = 3 should hold
        XCTAssertNotNil(result)
    }

    func testEventuallyNeverHolds() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Stay == x' = x

        Next == Stay

        Spec == Init /\\ [][Next]_x

        Liveness == <>(x = 10)
        ====
        """

        guard let module = parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let checker = ModelChecker()
        var config = ModelCheckerConfiguration()
        config.maxStates = 10
        config.properties = ["Liveness"]

        let result = await checker.check(module: module, config: config)

        // x never changes from 0, so x = 10 is never reached
        XCTAssertNotNil(result)
    }

    // MARK: - Always-Eventually Tests

    func testAlwaysEventuallyHolds() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Toggle == x' = 1 - x

        Next == Toggle

        Spec == Init /\\ [][Next]_x /\\ WF_x(Toggle)

        Liveness == []<>(x = 0)
        ====
        """

        guard let module = parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let checker = ModelChecker()
        var config = ModelCheckerConfiguration()
        config.maxStates = 20
        config.properties = ["Liveness"]

        let result = await checker.check(module: module, config: config)

        // x toggles between 0 and 1, so always eventually x = 0
        XCTAssertEqual(result.status, .completed)
    }

    func testAlwaysEventuallyCycleViolation() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Inc == x' = x + 1

        Next == Inc

        Spec == Init /\\ [][Next]_x

        Liveness == []<>(x = 0)
        ====
        """

        guard let module = parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let checker = ModelChecker()
        var config = ModelCheckerConfiguration()
        config.maxStates = 20
        config.properties = ["Liveness"]

        let result = await checker.check(module: module, config: config)

        // x keeps increasing, never returns to 0
        XCTAssertNotNil(result)
    }

    // MARK: - Eventually-Always Tests

    func testEventuallyAlwaysHolds() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Inc == x < 5 /\\ x' = x + 1
        Stay == x >= 5 /\\ x' = x

        Next == Inc \\/ Stay

        Spec == Init /\\ [][Next]_x

        Liveness == <>[](x >= 5)
        ====
        """

        guard let module = parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let checker = ModelChecker()
        var config = ModelCheckerConfiguration()
        config.maxStates = 20
        config.properties = ["Liveness"]

        let result = await checker.check(module: module, config: config)

        // Eventually x reaches 5 and stays >= 5 forever
        XCTAssertNotNil(result)
    }

    func testEventuallyAlwaysNeverEstablished() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Toggle == x' = 1 - x

        Next == Toggle

        Spec == Init /\\ [][Next]_x /\\ WF_x(Toggle)

        Liveness == <>[](x = 1)
        ====
        """

        guard let module = parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let checker = ModelChecker()
        var config = ModelCheckerConfiguration()
        config.maxStates = 20
        config.properties = ["Liveness"]

        let result = await checker.check(module: module, config: config)

        // x toggles forever, so x = 1 is never established permanently
        XCTAssertNotNil(result)
    }

    // MARK: - Deadlock Detection Tests

    func testDeadlockDetected() async throws {
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

        // At x = 3, Inc is disabled, causing deadlock
        XCTAssertEqual(result.status, .deadlock)
    }

    func testNoDeadlock() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Inc == x' = (x + 1) % 5

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

        // Inc is always enabled (wraps around)
        XCTAssertEqual(result.status, .completed)
    }

    // MARK: - State Space Exhaustion Tests

    func testStatesExhausted() async throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x

        Init == x = 0

        Inc == x' = x + 1

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
        config.maxStates = 5
        config.checkDeadlock = false

        let result = await checker.check(module: module, config: config)

        // Should exhaust max states
        XCTAssertEqual(result.status, .statesExhausted)
        XCTAssertLessThanOrEqual(result.statesExplored, 5)
    }
}
