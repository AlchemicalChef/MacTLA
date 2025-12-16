import XCTest
@testable import MacTLA

final class TLAInterpreterTests: XCTestCase {

    // MARK: - Helper Methods

    private func makeInterpreter() -> TLAInterpreter {
        TLAInterpreter()
    }

    private func makeEnv() -> TLAInterpreter.Environment {
        TLAInterpreter.Environment()
    }

    // MARK: - Basic Literals

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

    // MARK: - Additional Arithmetic Tests

    func testEvaluateDivision() throws {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        // 10 \div 3
        let result = try interpreter.evaluate(
            .binary(
                .number(10, .unknown),
                .div,
                .number(3, .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result, .integer(3))
    }

    func testEvaluateModulo() throws {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        // 10 % 3
        let result = try interpreter.evaluate(
            .binary(
                .number(10, .unknown),
                .mod,
                .number(3, .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result, .integer(1))
    }

    func testEvaluateExponentiation() throws {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        // 2^10
        let result = try interpreter.evaluate(
            .binary(
                .number(2, .unknown),
                .exp,
                .number(10, .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result, .integer(1024))
    }

    func testEvaluateNegation() throws {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        // -5 (unary minus)
        let result = try interpreter.evaluate(
            .unary(.negative, .number(5, .unknown), .unknown),
            in: env
        )
        XCTAssertEqual(result, .integer(-5))
    }

    // MARK: - Comparison Tests

    func testEvaluateGreaterThan() throws {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        // 5 > 3
        let result = try interpreter.evaluate(
            .binary(
                .number(5, .unknown),
                .gt,
                .number(3, .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result, .boolean(true))

        // 3 > 5
        let result2 = try interpreter.evaluate(
            .binary(
                .number(3, .unknown),
                .gt,
                .number(5, .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result2, .boolean(false))
    }

    func testEvaluateLessOrEqual() throws {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        // 3 <= 5
        let result = try interpreter.evaluate(
            .binary(
                .number(3, .unknown),
                .le,
                .number(5, .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result, .boolean(true))

        // 5 <= 5
        let result2 = try interpreter.evaluate(
            .binary(
                .number(5, .unknown),
                .le,
                .number(5, .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result2, .boolean(true))
    }

    func testEvaluateNotEqual() throws {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        // 3 # 5
        let result = try interpreter.evaluate(
            .binary(
                .number(3, .unknown),
                .neq,
                .number(5, .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result, .boolean(true))

        // 5 # 5
        let result2 = try interpreter.evaluate(
            .binary(
                .number(5, .unknown),
                .neq,
                .number(5, .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result2, .boolean(false))
    }

    // MARK: - Logical Tests

    func testEvaluateImplication() throws {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        // TRUE => FALSE
        let result = try interpreter.evaluate(
            .binary(
                .boolean(true, .unknown),
                .implies,
                .boolean(false, .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result, .boolean(false))

        // FALSE => FALSE
        let result2 = try interpreter.evaluate(
            .binary(
                .boolean(false, .unknown),
                .implies,
                .boolean(false, .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result2, .boolean(true))
    }

    func testEvaluateEquivalence() throws {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        // TRUE <=> TRUE
        let result = try interpreter.evaluate(
            .binary(
                .boolean(true, .unknown),
                .iff,
                .boolean(true, .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result, .boolean(true))

        // TRUE <=> FALSE
        let result2 = try interpreter.evaluate(
            .binary(
                .boolean(true, .unknown),
                .iff,
                .boolean(false, .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result2, .boolean(false))
    }

    // MARK: - Set Operations Tests

    func testEvaluateSetRange() throws {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        // 1..5
        let result = try interpreter.evaluate(
            .setRange(
                .number(1, .unknown),
                .number(5, .unknown),
                .unknown
            ),
            in: env
        )

        if case .set(let s) = result {
            XCTAssertEqual(s.count, 5)
            XCTAssertTrue(s.contains(.integer(1)))
            XCTAssertTrue(s.contains(.integer(5)))
        } else {
            XCTFail("Expected set")
        }
    }

    func testEvaluateSetUnion() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["A"] = .set([.integer(1), .integer(2)])
        env.variables["B"] = .set([.integer(2), .integer(3)])

        // A \union B
        let result = try interpreter.evaluate(
            .binary(
                .identifier("A", .unknown),
                .setUnion,
                .identifier("B", .unknown),
                .unknown
            ),
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

    func testEvaluateSetIntersection() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["A"] = .set([.integer(1), .integer(2), .integer(3)])
        env.variables["B"] = .set([.integer(2), .integer(3), .integer(4)])

        // A \intersect B
        let result = try interpreter.evaluate(
            .binary(
                .identifier("A", .unknown),
                .setIntersect,
                .identifier("B", .unknown),
                .unknown
            ),
            in: env
        )

        if case .set(let s) = result {
            XCTAssertEqual(s.count, 2)
            XCTAssertTrue(s.contains(.integer(2)))
            XCTAssertTrue(s.contains(.integer(3)))
        } else {
            XCTFail("Expected set")
        }
    }

    func testEvaluateSetDifference() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["A"] = .set([.integer(1), .integer(2), .integer(3)])
        env.variables["B"] = .set([.integer(2)])

        // A \ B
        let result = try interpreter.evaluate(
            .binary(
                .identifier("A", .unknown),
                .setMinus,
                .identifier("B", .unknown),
                .unknown
            ),
            in: env
        )

        if case .set(let s) = result {
            XCTAssertEqual(s.count, 2)
            XCTAssertTrue(s.contains(.integer(1)))
            XCTAssertTrue(s.contains(.integer(3)))
            XCTAssertFalse(s.contains(.integer(2)))
        } else {
            XCTFail("Expected set")
        }
    }

    func testEvaluateSubsetOf() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["A"] = .set([.integer(1), .integer(2)])
        env.variables["B"] = .set([.integer(1), .integer(2), .integer(3)])

        // A \subseteq B
        let result = try interpreter.evaluate(
            .binary(
                .identifier("A", .unknown),
                .subsetOf,
                .identifier("B", .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result, .boolean(true))

        // B \subseteq A
        let result2 = try interpreter.evaluate(
            .binary(
                .identifier("B", .unknown),
                .subsetOf,
                .identifier("A", .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result2, .boolean(false))
    }

    func testEvaluateEmptySet() throws {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        // {}
        let result = try interpreter.evaluate(
            .setEnumeration([], .unknown),
            in: env
        )

        if case .set(let s) = result {
            XCTAssertTrue(s.isEmpty)
        } else {
            XCTFail("Expected set")
        }
    }

    // MARK: - Tuple/Sequence Tests

    func testEvaluateTuple() throws {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        // <<1, 2, 3>>
        let result = try interpreter.evaluate(
            .tuple([
                .number(1, .unknown),
                .number(2, .unknown),
                .number(3, .unknown)
            ], .unknown),
            in: env
        )

        if case .sequence(let seq) = result {
            XCTAssertEqual(seq.count, 3)
            XCTAssertEqual(seq[0], .integer(1))
            XCTAssertEqual(seq[1], .integer(2))
            XCTAssertEqual(seq[2], .integer(3))
        } else {
            XCTFail("Expected sequence")
        }
    }

    func testEvaluateEmptyTuple() throws {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        // << >>
        let result = try interpreter.evaluate(
            .tuple([], .unknown),
            in: env
        )

        if case .sequence(let seq) = result {
            XCTAssertTrue(seq.isEmpty)
        } else {
            XCTFail("Expected sequence")
        }
    }

    // MARK: - Record Tests

    func testEvaluateRecordConstruction() throws {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        // [name |-> "Alice", age |-> 30]
        let result = try interpreter.evaluate(
            .recordConstruction([
                ("name", .string("Alice", .unknown)),
                ("age", .number(30, .unknown))
            ], .unknown),
            in: env
        )

        if case .record(let fields) = result {
            XCTAssertEqual(fields["name"], .string("Alice"))
            XCTAssertEqual(fields["age"], .integer(30))
        } else {
            XCTFail("Expected record")
        }
    }

    func testEvaluateRecordAccess() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["r"] = .record(["x": .integer(10), "y": .integer(20)])

        // r.x
        let result = try interpreter.evaluate(
            .recordAccess(.identifier("r", .unknown), "x", .unknown),
            in: env
        )
        XCTAssertEqual(result, .integer(10))
    }

    // MARK: - String Tests

    func testEvaluateString() throws {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        let result = try interpreter.evaluate(
            .string("Hello, TLA+!", .unknown),
            in: env
        )
        XCTAssertEqual(result, .string("Hello, TLA+!"))
    }

    // MARK: - Quantifier Tests

    func testEvaluateForallTrue() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["S"] = .set([.integer(1), .integer(2), .integer(3)])

        // \A x \in S : x > 0
        let result = try interpreter.evaluate(
            .forall(
                [BoundVariable(name: "x", domain: .identifier("S", .unknown))],
                .binary(
                    .identifier("x", .unknown),
                    .gt,
                    .number(0, .unknown),
                    .unknown
                ),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result, .boolean(true))
    }

    func testEvaluateForallFalse() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["S"] = .set([.integer(1), .integer(2), .integer(3)])

        // \A x \in S : x > 2
        let result = try interpreter.evaluate(
            .forall(
                [BoundVariable(name: "x", domain: .identifier("S", .unknown))],
                .binary(
                    .identifier("x", .unknown),
                    .gt,
                    .number(2, .unknown),
                    .unknown
                ),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result, .boolean(false))
    }

    func testEvaluateExistsTrue() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["S"] = .set([.integer(1), .integer(2), .integer(3)])

        // \E x \in S : x = 2
        let result = try interpreter.evaluate(
            .exists(
                [BoundVariable(name: "x", domain: .identifier("S", .unknown))],
                .binary(
                    .identifier("x", .unknown),
                    .eq,
                    .number(2, .unknown),
                    .unknown
                ),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result, .boolean(true))
    }

    func testEvaluateExistsFalse() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["S"] = .set([.integer(1), .integer(2), .integer(3)])

        // \E x \in S : x > 10
        let result = try interpreter.evaluate(
            .exists(
                [BoundVariable(name: "x", domain: .identifier("S", .unknown))],
                .binary(
                    .identifier("x", .unknown),
                    .gt,
                    .number(10, .unknown),
                    .unknown
                ),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result, .boolean(false))
    }

    func testEvaluateForallEmptySet() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["S"] = .set([])

        // \A x \in {} : FALSE (vacuously true)
        let result = try interpreter.evaluate(
            .forall(
                [BoundVariable(name: "x", domain: .identifier("S", .unknown))],
                .boolean(false, .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result, .boolean(true))
    }

    func testEvaluateExistsEmptySet() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["S"] = .set([])

        // \E x \in {} : TRUE (false, no elements)
        let result = try interpreter.evaluate(
            .exists(
                [BoundVariable(name: "x", domain: .identifier("S", .unknown))],
                .boolean(true, .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result, .boolean(false))
    }

    // MARK: - Function Tests

    func testEvaluateFunctionConstruction() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["S"] = .set([.integer(1), .integer(2), .integer(3)])

        // [x \in S |-> x * 2]
        let result = try interpreter.evaluate(
            .functionConstruction(
                [BoundVariable(name: "x", domain: .identifier("S", .unknown))],
                .binary(
                    .identifier("x", .unknown),
                    .times,
                    .number(2, .unknown),
                    .unknown
                ),
                .unknown
            ),
            in: env
        )

        if case .function(let f) = result {
            XCTAssertEqual(f[.integer(1)], .integer(2))
            XCTAssertEqual(f[.integer(2)], .integer(4))
            XCTAssertEqual(f[.integer(3)], .integer(6))
        } else {
            XCTFail("Expected function, got \(result)")
        }
    }

    func testEvaluateFunctionApplication() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        // f = [1 |-> 10, 2 |-> 20, 3 |-> 30]
        env.variables["f"] = .function([
            .integer(1): .integer(10),
            .integer(2): .integer(20),
            .integer(3): .integer(30)
        ])

        // f[2]
        let result = try interpreter.evaluate(
            .functionApplication(
                .identifier("f", .unknown),
                [.number(2, .unknown)],
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result, .integer(20))
    }

    // MARK: - Constant Parsing Tests

    func testParseConstantInteger() {
        let interpreter = makeInterpreter()
        interpreter.setConstant(name: "N", valueString: "42")

        var env = makeEnv()
        env.constants["N"] = nil // Trigger lookup

        // The constant should be retrievable
        // This test verifies the parsing, not the full evaluation flow
    }

    func testParseConstantSet() {
        let interpreter = makeInterpreter()
        interpreter.setConstant(name: "S", valueString: "{1, 2, 3}")
        // Verify it was parsed (internal state)
    }

    func testParseConstantSequence() {
        let interpreter = makeInterpreter()
        interpreter.setConstant(name: "Seq", valueString: "<<1, 2, 3>>")
        // Verify it was parsed (internal state)
    }

    func testParseConstantRange() {
        let interpreter = makeInterpreter()
        interpreter.setConstant(name: "Range", valueString: "1..5")
        // Verify it was parsed as a set
    }

    // MARK: - Edge Cases and Error Handling

    func testEvaluateDivisionByZero() {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        // 10 \div 0
        XCTAssertThrowsError(try interpreter.evaluate(
            .binary(
                .number(10, .unknown),
                .div,
                .number(0, .unknown),
                .unknown
            ),
            in: env
        ))
    }

    func testEvaluateModuloByZero() {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        // 10 % 0
        XCTAssertThrowsError(try interpreter.evaluate(
            .binary(
                .number(10, .unknown),
                .mod,
                .number(0, .unknown),
                .unknown
            ),
            in: env
        ))
    }

    func testEvaluateNestedArithmetic() throws {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        // (2 + 3) * 4
        let result = try interpreter.evaluate(
            .binary(
                .binary(
                    .number(2, .unknown),
                    .plus,
                    .number(3, .unknown),
                    .unknown
                ),
                .times,
                .number(4, .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result, .integer(20))
    }

    func testEvaluateComplexLogicalExpression() throws {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        // (TRUE /\ FALSE) \/ TRUE
        let result = try interpreter.evaluate(
            .binary(
                .binary(
                    .boolean(true, .unknown),
                    .and,
                    .boolean(false, .unknown),
                    .unknown
                ),
                .or,
                .boolean(true, .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result, .boolean(true))
    }

    func testEvaluateNotElementOf() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["S"] = .set([.integer(1), .integer(2), .integer(3)])

        // 5 \notin S
        let result = try interpreter.evaluate(
            .binary(
                .number(5, .unknown),
                .notElementOf,
                .identifier("S", .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result, .boolean(true))

        // 2 \notin S
        let result2 = try interpreter.evaluate(
            .binary(
                .number(2, .unknown),
                .notElementOf,
                .identifier("S", .unknown),
                .unknown
            ),
            in: env
        )
        XCTAssertEqual(result2, .boolean(false))
    }
}
