import XCTest
@testable import MacTLA

final class TLAInterpreterTests: XCTestCase {

    func testEvaluateNumber() throws {
        let interpreter = TLAInterpreter()
        let env = TLAInterpreter.Environment()

        let result = try interpreter.evaluate(
            .number(42, .unknown),
            in: env
        )

        XCTAssertEqual(result, .integer(42))
    }

    func testEvaluateBoolean() throws {
        let interpreter = TLAInterpreter()
        let env = TLAInterpreter.Environment()

        let trueResult = try interpreter.evaluate(.boolean(true, .unknown), in: env)
        let falseResult = try interpreter.evaluate(.boolean(false, .unknown), in: env)

        XCTAssertEqual(trueResult, .boolean(true))
        XCTAssertEqual(falseResult, .boolean(false))
    }

    func testEvaluateArithmetic() throws {
        let interpreter = TLAInterpreter()
        let env = TLAInterpreter.Environment()

        // 2 + 3
        let addResult = try interpreter.evaluate(
            .binary(
                .number(2, .unknown),
                .plus,
                .number(3, .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(addResult, .integer(5))

        // 10 - 4
        let subResult = try interpreter.evaluate(
            .binary(
                .number(10, .unknown),
                .minus,
                .number(4, .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(subResult, .integer(6))

        // 3 * 4
        let mulResult = try interpreter.evaluate(
            .binary(
                .number(3, .unknown),
                .times,
                .number(4, .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(mulResult, .integer(12))
    }

    func testEvaluateComparison() throws {
        let interpreter = TLAInterpreter()
        let env = TLAInterpreter.Environment()

        // 3 < 5
        let ltResult = try interpreter.evaluate(
            .binary(
                .number(3, .unknown),
                .lt,
                .number(5, .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(ltResult, .boolean(true))

        // 5 = 5
        let eqResult = try interpreter.evaluate(
            .binary(
                .number(5, .unknown),
                .eq,
                .number(5, .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(eqResult, .boolean(true))
    }

    func testEvaluateLogical() throws {
        let interpreter = TLAInterpreter()
        let env = TLAInterpreter.Environment()

        // TRUE /\ FALSE
        let andResult = try interpreter.evaluate(
            .binary(
                .boolean(true, .unknown),
                .and,
                .boolean(false, .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(andResult, .boolean(false))

        // TRUE \/ FALSE
        let orResult = try interpreter.evaluate(
            .binary(
                .boolean(true, .unknown),
                .or,
                .boolean(false, .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(orResult, .boolean(true))

        // ~TRUE
        let notResult = try interpreter.evaluate(
            .unary(.not, .boolean(true, .unknown), .unknown),
            in: env
        )
        XCTAssertEqual(notResult, .boolean(false))
    }

    func testEvaluateSetEnumeration() throws {
        let interpreter = TLAInterpreter()
        let env = TLAInterpreter.Environment()

        // {1, 2, 3}
        let result = try interpreter.evaluate(
            .setEnumeration([
                .number(1, .unknown),
                .number(2, .unknown),
                .number(3, .unknown)
            ], .unknown),
            in: env
        )

        if case .set(let s) = result {
            XCTAssertEqual(s.count, 3)
            XCTAssertTrue(s.contains(.integer(1)))
            XCTAssertTrue(s.contains(.integer(2)))
            XCTAssertTrue(s.contains(.integer(3)))
        } else {
            XCTFail("Expected set")
        }
    }

    func testEvaluateSetMembership() throws {
        let interpreter = TLAInterpreter()
        var env = TLAInterpreter.Environment()
        env.variables["S"] = .set([.integer(1), .integer(2), .integer(3)])

        // 2 \in S
        let inResult = try interpreter.evaluate(
            .binary(
                .number(2, .unknown),
                .elementOf,
                .identifier("S", .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(inResult, .boolean(true))

        // 5 \in S
        let notInResult = try interpreter.evaluate(
            .binary(
                .number(5, .unknown),
                .elementOf,
                .identifier("S", .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(notInResult, .boolean(false))
    }

    func testEvaluateIfThenElse() throws {
        let interpreter = TLAInterpreter()
        let env = TLAInterpreter.Environment()

        // IF TRUE THEN 1 ELSE 2
        let result = try interpreter.evaluate(
            .ternary(
                .boolean(true, .unknown),
                .number(1, .unknown),
                .number(2, .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result, .integer(1))

        // IF FALSE THEN 1 ELSE 2
        let result2 = try interpreter.evaluate(
            .ternary(
                .boolean(false, .unknown),
                .number(1, .unknown),
                .number(2, .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result2, .integer(2))
    }

    func testEvaluateVariable() throws {
        let interpreter = TLAInterpreter()
        var env = TLAInterpreter.Environment()
        env.variables["x"] = .integer(42)

        let result = try interpreter.evaluate(
            .identifier("x", .unknown),
            in: env
        )
        XCTAssertEqual(result, .integer(42))
    }

    func testEvaluateUndefinedVariable() {
        let interpreter = TLAInterpreter()
        let env = TLAInterpreter.Environment()

        XCTAssertThrowsError(try interpreter.evaluate(
            .identifier("undefined", .unknown),
            in: env
        ))
    }
}
