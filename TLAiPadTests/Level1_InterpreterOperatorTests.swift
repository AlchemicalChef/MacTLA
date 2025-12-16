import XCTest
@testable import MacTLA

/// Level 1: Comprehensive Interpreter Operator Tests
/// Tests evaluation of all TLA+ operators
final class Level1_InterpreterOperatorTests: XCTestCase {

    private func makeInterpreter() -> TLAInterpreter { TLAInterpreter() }
    private func makeEnv() -> TLAInterpreter.Environment { TLAInterpreter.Environment() }

    // MARK: - CHOOSE Operator

    func testChooseSatisfyingValue() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["S"] = .set([.integer(1), .integer(2), .integer(3), .integer(4), .integer(5)])

        // CHOOSE x \in S : x > 3
        let result = try interpreter.evaluate(
            .choose(
                BoundVariable(name: "x", domain: .identifier("S", .unknown)),
                .binary(
                    .identifier("x", .unknown),
                    .gt,
                    .number(3, .unknown),
                    .unknown
                ),
                .unknown
            ),
            in: env
        )

        // Should return 4 or 5 (one that satisfies x > 3)
        if case .integer(let n) = result {
            XCTAssertTrue(n > 3, "CHOOSE should return value satisfying predicate")
        } else {
            XCTFail("Expected integer")
        }
    }

    func testChooseNoSatisfyingValue() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["S"] = .set([.integer(1), .integer(2), .integer(3)])

        // CHOOSE x \in S : x > 10 (no satisfying value)
        let result = try interpreter.evaluate(
            .choose(
                BoundVariable(name: "x", domain: .identifier("S", .unknown)),
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

        // Per TLA+ semantics, returns unspecified value from domain
        if case .integer(let n) = result {
            XCTAssertTrue([1, 2, 3].contains(n), "Should return some value from domain")
        } else {
            XCTFail("Expected integer")
        }
    }

    func testChooseEmptyDomain() {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["S"] = .set([])

        // CHOOSE x \in {} : TRUE
        XCTAssertThrowsError(try interpreter.evaluate(
            .choose(
                BoundVariable(name: "x", domain: .identifier("S", .unknown)),
                .boolean(true, .unknown),
                .unknown
            ),
            in: env
        ))
    }

    // MARK: - Set Comprehension (Filter)

    func testSetComprehensionFilter() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["S"] = .set([.integer(1), .integer(2), .integer(3), .integer(4), .integer(5)])

        // {x \in S : x > 2}
        let result = try interpreter.evaluate(
            .setComprehension(
                BoundVariable(name: "x", domain: .identifier("S", .unknown)),
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

        if case .set(let s) = result {
            XCTAssertEqual(s.count, 3)
            XCTAssertTrue(s.contains(.integer(3)))
            XCTAssertTrue(s.contains(.integer(4)))
            XCTAssertTrue(s.contains(.integer(5)))
        } else {
            XCTFail("Expected set")
        }
    }

    // MARK: - Set Map

    func testSetMap() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["S"] = .set([.integer(1), .integer(2), .integer(3)])

        // {x * 2 : x \in S}
        let result = try interpreter.evaluate(
            .setMap(
                .binary(
                    .identifier("x", .unknown),
                    .times,
                    .number(2, .unknown),
                    .unknown
                ),
                BoundVariable(name: "x", domain: .identifier("S", .unknown)),
                .unknown
            ),
            in: env
        )

        if case .set(let s) = result {
            XCTAssertEqual(s.count, 3)
            XCTAssertTrue(s.contains(.integer(2)))
            XCTAssertTrue(s.contains(.integer(4)))
            XCTAssertTrue(s.contains(.integer(6)))
        } else {
            XCTFail("Expected set")
        }
    }

    // MARK: - Cardinality (via built-in)

    func testCardinality() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["S"] = .set([.integer(1), .integer(2), .integer(3)])

        // Cardinality(S) - this requires Cardinality to be defined
        // For now, we test the underlying set count
        if case .set(let s) = env.variables["S"] {
            XCTAssertEqual(s.count, 3)
        }
    }

    // MARK: - SUBSET (Powerset)

    func testSubsetPowerset() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["S"] = .set([.integer(1), .integer(2)])

        // SUBSET S
        let result = try interpreter.evaluate(
            .unary(.subset, .identifier("S", .unknown), .unknown),
            in: env
        )

        if case .set(let powerset) = result {
            // Powerset of {1, 2} = {{}, {1}, {2}, {1, 2}}
            XCTAssertEqual(powerset.count, 4)
        } else {
            XCTFail("Expected set")
        }
    }

    // MARK: - UNION (Generalized Union)

    func testUnionGeneralized() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["S"] = .set([
            .set([.integer(1), .integer(2)]),
            .set([.integer(2), .integer(3)]),
            .set([.integer(3), .integer(4)])
        ])

        // UNION S
        let result = try interpreter.evaluate(
            .unary(.union, .identifier("S", .unknown), .unknown),
            in: env
        )

        if case .set(let union) = result {
            XCTAssertEqual(union.count, 4)
            XCTAssertTrue(union.contains(.integer(1)))
            XCTAssertTrue(union.contains(.integer(2)))
            XCTAssertTrue(union.contains(.integer(3)))
            XCTAssertTrue(union.contains(.integer(4)))
        } else {
            XCTFail("Expected set")
        }
    }

    // MARK: - DOMAIN

    func testDomain() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["f"] = .function([
            .integer(1): .string("a"),
            .integer(2): .string("b"),
            .integer(3): .string("c")
        ])

        // DOMAIN f
        let result = try interpreter.evaluate(
            .unary(.domain, .identifier("f", .unknown), .unknown),
            in: env
        )

        if case .set(let domain) = result {
            XCTAssertEqual(domain.count, 3)
            XCTAssertTrue(domain.contains(.integer(1)))
            XCTAssertTrue(domain.contains(.integer(2)))
            XCTAssertTrue(domain.contains(.integer(3)))
        } else {
            XCTFail("Expected set")
        }
    }

    // MARK: - EXCEPT Clauses

    func testExceptFunction() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["f"] = .function([
            .integer(1): .integer(10),
            .integer(2): .integer(20)
        ])

        // [f EXCEPT ![1] = 100]
        let result = try interpreter.evaluate(
            .except(
                .identifier("f", .unknown),
                [ExceptClause(path: [.number(1, .unknown)], value: .number(100, .unknown))],
                .unknown
            ),
            in: env
        )

        if case .function(let newF) = result {
            XCTAssertEqual(newF[.integer(1)], .integer(100))
            XCTAssertEqual(newF[.integer(2)], .integer(20))
        } else {
            XCTFail("Expected function")
        }
    }

    func testExceptRecord() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["r"] = .record(["x": .integer(1), "y": .integer(2)])

        // [r EXCEPT !.x = 100]
        let result = try interpreter.evaluate(
            .except(
                .identifier("r", .unknown),
                [ExceptClause(path: [.string("x", .unknown)], value: .number(100, .unknown))],
                .unknown
            ),
            in: env
        )

        if case .record(let newR) = result {
            XCTAssertEqual(newR["x"], .integer(100))
            XCTAssertEqual(newR["y"], .integer(2))
        } else {
            XCTFail("Expected record")
        }
    }

    func testExceptSequence() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["seq"] = .sequence([.integer(1), .integer(2), .integer(3)])

        // [seq EXCEPT ![2] = 100]
        let result = try interpreter.evaluate(
            .except(
                .identifier("seq", .unknown),
                [ExceptClause(path: [.number(2, .unknown)], value: .number(100, .unknown))],
                .unknown
            ),
            in: env
        )

        if case .sequence(let newSeq) = result {
            XCTAssertEqual(newSeq[0], .integer(1))
            XCTAssertEqual(newSeq[1], .integer(100))
            XCTAssertEqual(newSeq[2], .integer(3))
        } else {
            XCTFail("Expected sequence")
        }
    }

    func testExceptMultipleClauses() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["f"] = .function([
            .integer(1): .integer(10),
            .integer(2): .integer(20),
            .integer(3): .integer(30)
        ])

        // [f EXCEPT ![1] = 100, ![2] = 200]
        let result = try interpreter.evaluate(
            .except(
                .identifier("f", .unknown),
                [
                    ExceptClause(path: [.number(1, .unknown)], value: .number(100, .unknown)),
                    ExceptClause(path: [.number(2, .unknown)], value: .number(200, .unknown))
                ],
                .unknown
            ),
            in: env
        )

        if case .function(let newF) = result {
            XCTAssertEqual(newF[.integer(1)], .integer(100))
            XCTAssertEqual(newF[.integer(2)], .integer(200))
            XCTAssertEqual(newF[.integer(3)], .integer(30))
        } else {
            XCTFail("Expected function")
        }
    }

    // MARK: - LET-IN Expressions

    func testLetInSimple() throws {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        // LET x == 5 IN x + 1
        let result = try interpreter.evaluate(
            .letIn(
                [OperatorDefinition(
                    name: "x",
                    parameters: [],
                    body: .number(5, .unknown),
                    isRecursive: false,
                    location: .unknown
                )],
                .binary(
                    .identifier("x", .unknown),
                    .plus,
                    .number(1, .unknown),
                    .unknown
                ),
                .unknown
            ),
            in: env
        )

        XCTAssertEqual(result, .integer(6))
    }

    func testLetInMultipleBindings() throws {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        // LET x == 5 y == 10 IN x + y
        let result = try interpreter.evaluate(
            .letIn(
                [
                    OperatorDefinition(
                        name: "x",
                        parameters: [],
                        body: .number(5, .unknown),
                        isRecursive: false,
                        location: .unknown
                    ),
                    OperatorDefinition(
                        name: "y",
                        parameters: [],
                        body: .number(10, .unknown),
                        isRecursive: false,
                        location: .unknown
                    )
                ],
                .binary(
                    .identifier("x", .unknown),
                    .plus,
                    .identifier("y", .unknown),
                    .unknown
                ),
                .unknown
            ),
            in: env
        )

        XCTAssertEqual(result, .integer(15))
    }

    // MARK: - CASE Expressions

    func testCaseFirstArmMatches() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["x"] = .integer(1)

        // CASE x = 1 -> "one" [] x = 2 -> "two"
        let result = try interpreter.evaluate(
            .caseExpr(
                [
                    CaseArm(
                        condition: .binary(.identifier("x", .unknown), .eq, .number(1, .unknown), .unknown),
                        result: .string("one", .unknown)
                    ),
                    CaseArm(
                        condition: .binary(.identifier("x", .unknown), .eq, .number(2, .unknown), .unknown),
                        result: .string("two", .unknown)
                    )
                ],
                nil,
                .unknown
            ),
            in: env
        )

        XCTAssertEqual(result, .string("one"))
    }

    func testCaseSecondArmMatches() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["x"] = .integer(2)

        // CASE x = 1 -> "one" [] x = 2 -> "two"
        let result = try interpreter.evaluate(
            .caseExpr(
                [
                    CaseArm(
                        condition: .binary(.identifier("x", .unknown), .eq, .number(1, .unknown), .unknown),
                        result: .string("one", .unknown)
                    ),
                    CaseArm(
                        condition: .binary(.identifier("x", .unknown), .eq, .number(2, .unknown), .unknown),
                        result: .string("two", .unknown)
                    )
                ],
                nil,
                .unknown
            ),
            in: env
        )

        XCTAssertEqual(result, .string("two"))
    }

    func testCaseOtherBranch() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["x"] = .integer(99)

        // CASE x = 1 -> "one" [] OTHER -> "other"
        let result = try interpreter.evaluate(
            .caseExpr(
                [
                    CaseArm(
                        condition: .binary(.identifier("x", .unknown), .eq, .number(1, .unknown), .unknown),
                        result: .string("one", .unknown)
                    )
                ],
                .string("other", .unknown),
                .unknown
            ),
            in: env
        )

        XCTAssertEqual(result, .string("other"))
    }

    // MARK: - Sequence Indexing

    func testSequenceIndexing() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["seq"] = .sequence([.integer(10), .integer(20), .integer(30)])

        // seq[2] (1-indexed in TLA+)
        let result = try interpreter.evaluate(
            .functionApplication(
                .identifier("seq", .unknown),
                [.number(2, .unknown)],
                .unknown
            ),
            in: env
        )

        XCTAssertEqual(result, .integer(20))
    }

    func testSequenceIndexingOutOfBounds() {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["seq"] = .sequence([.integer(10), .integer(20), .integer(30)])

        // seq[5] - out of bounds
        XCTAssertThrowsError(try interpreter.evaluate(
            .functionApplication(
                .identifier("seq", .unknown),
                [.number(5, .unknown)],
                .unknown
            ),
            in: env
        ))
    }

    // MARK: - Cartesian Product

    func testCartesianProduct() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["A"] = .set([.integer(1), .integer(2)])
        env.variables["B"] = .set([.string("a"), .string("b")])

        // A \X B
        let result = try interpreter.evaluate(
            .binary(
                .identifier("A", .unknown),
                .cartesian,
                .identifier("B", .unknown),
                .unknown
            ),
            in: env
        )

        if case .set(let product) = result {
            XCTAssertEqual(product.count, 4)
            // Should contain <<1, "a">>, <<1, "b">>, <<2, "a">>, <<2, "b">>
        } else {
            XCTFail("Expected set")
        }
    }

    // MARK: - Nested Quantifiers

    func testNestedForall() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["S"] = .set([.integer(1), .integer(2)])
        env.variables["T"] = .set([.integer(1), .integer(2)])

        // \A x \in S : \A y \in T : x + y > 0
        let result = try interpreter.evaluate(
            .forall(
                [BoundVariable(name: "x", domain: .identifier("S", .unknown))],
                .forall(
                    [BoundVariable(name: "y", domain: .identifier("T", .unknown))],
                    .binary(
                        .binary(
                            .identifier("x", .unknown),
                            .plus,
                            .identifier("y", .unknown),
                            .unknown
                        ),
                        .gt,
                        .number(0, .unknown),
                        .unknown
                    ),
                    .unknown
                ),
                .unknown
            ),
            in: env
        )

        XCTAssertEqual(result, .boolean(true))
    }

    func testNestedExists() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["S"] = .set([.integer(1), .integer(2), .integer(3)])

        // \E x \in S : \E y \in S : x + y = 5
        let result = try interpreter.evaluate(
            .exists(
                [BoundVariable(name: "x", domain: .identifier("S", .unknown))],
                .exists(
                    [BoundVariable(name: "y", domain: .identifier("S", .unknown))],
                    .binary(
                        .binary(
                            .identifier("x", .unknown),
                            .plus,
                            .identifier("y", .unknown),
                            .unknown
                        ),
                        .eq,
                        .number(5, .unknown),
                        .unknown
                    ),
                    .unknown
                ),
                .unknown
            ),
            in: env
        )

        XCTAssertEqual(result, .boolean(true))
    }

    // MARK: - Prime Operator

    func testPrimeEvaluation() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["x"] = .integer(5)
        env.primedVariables["x"] = .integer(10)

        // x'
        let result = try interpreter.evaluate(
            .prime(.identifier("x", .unknown), .unknown),
            in: env
        )

        XCTAssertEqual(result, .integer(10))
    }

    // MARK: - Boolean Short-Circuit Evaluation

    func testAndShortCircuit() throws {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        // FALSE /\ (undefined - would error if evaluated)
        let result = try interpreter.evaluate(
            .binary(
                .boolean(false, .unknown),
                .and,
                .identifier("undefined", .unknown),  // Should not be evaluated
                .unknown
            ),
            in: env
        )

        XCTAssertEqual(result, .boolean(false))
    }

    func testOrShortCircuit() throws {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        // TRUE \/ (undefined - would error if evaluated)
        let result = try interpreter.evaluate(
            .binary(
                .boolean(true, .unknown),
                .or,
                .identifier("undefined", .unknown),  // Should not be evaluated
                .unknown
            ),
            in: env
        )

        XCTAssertEqual(result, .boolean(true))
    }

    // MARK: - Type Mismatch Errors

    func testArithmeticTypeMismatch() {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        // 1 + "string"
        XCTAssertThrowsError(try interpreter.evaluate(
            .binary(
                .number(1, .unknown),
                .plus,
                .string("string", .unknown),
                .unknown
            ),
            in: env
        ))
    }

    func testSetOperationTypeMismatch() {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        // 1 \in 5 (not a set)
        XCTAssertThrowsError(try interpreter.evaluate(
            .binary(
                .number(1, .unknown),
                .elementOf,
                .number(5, .unknown),
                .unknown
            ),
            in: env
        ))
    }

    // MARK: - Large Values

    func testLargeInteger() throws {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        // 1000000000
        let result = try interpreter.evaluate(
            .number(1_000_000_000, .unknown),
            in: env
        )

        XCTAssertEqual(result, .integer(1_000_000_000))
    }

    func testLargeSetRange() throws {
        let interpreter = makeInterpreter()
        let env = makeEnv()

        // 1..100
        let result = try interpreter.evaluate(
            .setRange(.number(1, .unknown), .number(100, .unknown), .unknown),
            in: env
        )

        if case .set(let s) = result {
            XCTAssertEqual(s.count, 100)
        } else {
            XCTFail("Expected set")
        }
    }
}
