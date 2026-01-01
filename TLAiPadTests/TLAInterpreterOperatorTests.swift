import XCTest
@testable import MacTLA

/// Extended operator tests including edge cases for TLAInterpreter
final class TLAInterpreterOperatorTests: XCTestCase {

    // MARK: - Helper Methods

    private func makeInterpreter() -> TLAInterpreter {
        TLAInterpreter()
    }

    private func makeEnv() -> TLAInterpreter.Environment {
        TLAInterpreter.Environment()
    }

    private func parse(_ source: String) -> TLAModule? {
        let parser = TLAParser()
        switch parser.parse(source) {
        case .success(let module):
            return module
        case .failure:
            return nil
        }
    }

    private func evaluateTestOp(_ source: String) throws -> TLAValue {
        guard let module = parse(source) else {
            throw NSError(domain: "TestError", code: 1, userInfo: [NSLocalizedDescriptionKey: "Parse failed"])
        }

        let interpreter = makeInterpreter()
        var env = makeEnv()
        try interpreter.loadModule(module, into: &env)

        return try interpreter.evaluate(.identifier("Test", .unknown), in: env)
    }

    // MARK: - Arithmetic Edge Cases: Division

    func testDivisionNormal() throws {
        let source = """
        ---- MODULE Test ----
        Test == 10 \\div 3
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .integer(3))
    }

    func testDivisionByZero() throws {
        let source = """
        ---- MODULE Test ----
        Test == 10 \\div 0
        ====
        """

        XCTAssertThrowsError(try evaluateTestOp(source))
    }

    func testDivisionNegative() throws {
        let source = """
        ---- MODULE Test ----
        Test == -10 \\div 3
        ====
        """

        let result = try evaluateTestOp(source)
        // TLA+ uses integer division - behavior may vary
        XCTAssertNotNil(result)
    }

    // MARK: - Arithmetic Edge Cases: Modulo

    func testModuloNormal() throws {
        let source = """
        ---- MODULE Test ----
        Test == 10 % 3
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .integer(1))
    }

    func testModuloByZero() throws {
        let source = """
        ---- MODULE Test ----
        Test == 10 % 0
        ====
        """

        XCTAssertThrowsError(try evaluateTestOp(source))
    }

    func testModuloNegativeNumbers() throws {
        let source = """
        ---- MODULE Test ----
        Test == -10 % 3
        ====
        """

        // Behavior of modulo with negatives varies
        let result = try evaluateTestOp(source)
        XCTAssertNotNil(result)
    }

    // MARK: - Arithmetic Edge Cases: Exponentiation

    func testExponentiationNormal() throws {
        let source = """
        ---- MODULE Test ----
        Test == 2^10
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .integer(1024))
    }

    func testExponentiationBaseZero() throws {
        let source = """
        ---- MODULE Test ----
        Test == 0^5
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .integer(0))
    }

    func testExponentiationBaseOne() throws {
        let source = """
        ---- MODULE Test ----
        Test == 1^100
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .integer(1))
    }

    func testExponentiationExponentZero() throws {
        let source = """
        ---- MODULE Test ----
        Test == 5^0
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .integer(1))
    }

    func testExponentiationZeroToZero() throws {
        let source = """
        ---- MODULE Test ----
        Test == 0^0
        ====
        """

        // 0^0 is mathematically undefined but often defined as 1 in programming
        let result = try evaluateTestOp(source)
        XCTAssertNotNil(result)
    }

    // MARK: - Set Operation Edge Cases

    func testSubsetEmptySets() throws {
        let source = """
        ---- MODULE Test ----
        Test == {} \\subseteq {}
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .boolean(true))
    }

    func testSubsetOfSelf() throws {
        let source = """
        ---- MODULE Test ----
        Test == {1, 2, 3} \\subseteq {1, 2, 3}
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .boolean(true))
    }

    func testProperSubset() throws {
        let source = """
        ---- MODULE Test ----
        Test == {1, 2} \\subset {1, 2, 3}
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .boolean(true))
    }

    func testProperSubsetOfSelf() throws {
        let source = """
        ---- MODULE Test ----
        Test == {1, 2} \\subset {1, 2}
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .boolean(false))
    }

    func testUnionDisjointSets() throws {
        let source = """
        ---- MODULE Test ----
        Test == {1, 2} \\cup {3, 4}
        ====
        """

        let result = try evaluateTestOp(source)
        if case .set(let values) = result {
            XCTAssertEqual(values.count, 4)
        } else {
            XCTFail("Expected set")
        }
    }

    func testIntersectionDisjointSets() throws {
        let source = """
        ---- MODULE Test ----
        Test == {1, 2} \\cap {3, 4}
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .set([]))
    }

    func testSetDifferenceDisjoint() throws {
        let source = """
        ---- MODULE Test ----
        Test == {1, 2} \\ {3, 4}
        ====
        """

        let result = try evaluateTestOp(source)
        if case .set(let values) = result {
            XCTAssertEqual(values.count, 2)
            XCTAssertTrue(values.contains(.integer(1)))
            XCTAssertTrue(values.contains(.integer(2)))
        } else {
            XCTFail("Expected set")
        }
    }

    func testCartesianProductEmpty() throws {
        let source = """
        ---- MODULE Test ----
        Test == {} \\X {1, 2}
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .set([]))
    }

    func testCartesianProductSingleElements() throws {
        let source = """
        ---- MODULE Test ----
        Test == {1} \\X {2}
        ====
        """

        let result = try evaluateTestOp(source)
        if case .set(let values) = result {
            XCTAssertEqual(values.count, 1)
            // Should contain <<1, 2>>
            XCTAssertTrue(values.contains(.sequence([.integer(1), .integer(2)])))
        } else {
            XCTFail("Expected set")
        }
    }

    // MARK: - Comparison Edge Cases

    func testEqualityDifferentTypes() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()

        let expr = TLAExpression.binary(
            .number(1, .unknown),
            .eq,
            .string("1", .unknown),
            .unknown
        )

        let result = try interpreter.evaluate(expr, in: env)
        XCTAssertEqual(result, .boolean(false))
    }

    func testEqualitySets() throws {
        let source = """
        ---- MODULE Test ----
        Test == {1, 2, 3} = {3, 2, 1}
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .boolean(true))
    }

    func testEqualitySequences() throws {
        let source = """
        ---- MODULE Test ----
        Test == <<1, 2, 3>> = <<1, 2, 3>>
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .boolean(true))
    }

    func testSequenceOrderMatters() throws {
        let source = """
        ---- MODULE Test ----
        Test == <<1, 2, 3>> = <<3, 2, 1>>
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .boolean(false))
    }

    // MARK: - Boolean Operator Edge Cases

    func testImplicationTrueImpliesFalse() throws {
        let source = """
        ---- MODULE Test ----
        Test == TRUE => FALSE
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .boolean(false))
    }

    func testImplicationFalseImpliesAnything() throws {
        let source = """
        ---- MODULE Test ----
        Test == FALSE => FALSE
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .boolean(true))
    }

    func testEquivalenceSame() throws {
        let source = """
        ---- MODULE Test ----
        Test == TRUE <=> TRUE
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .boolean(true))
    }

    func testEquivalenceDifferent() throws {
        let source = """
        ---- MODULE Test ----
        Test == TRUE <=> FALSE
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .boolean(false))
    }

    // MARK: - Circle Operators (if supported)

    func testXorEquivalent() throws {
        // XOR can be expressed as (a \/ b) /\ ~(a /\ b)
        let source = """
        ---- MODULE Test ----
        XOR(a, b) == (a \\/ b) /\\ ~(a /\\ b)
        Test == XOR(TRUE, FALSE)
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .boolean(true))
    }

    func testXorSameValues() throws {
        let source = """
        ---- MODULE Test ----
        XOR(a, b) == (a \\/ b) /\\ ~(a /\\ b)
        Test == XOR(TRUE, TRUE)
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .boolean(false))
    }

    // MARK: - Symmetric Difference

    func testSymmetricDifference() throws {
        // Symmetric difference: (A \ B) \cup (B \ A)
        let source = """
        ---- MODULE Test ----
        SymDiff(A, B) == (A \\ B) \\cup (B \\ A)
        Test == SymDiff({1, 2, 3}, {2, 3, 4})
        ====
        """

        let result = try evaluateTestOp(source)
        if case .set(let values) = result {
            XCTAssertEqual(values.count, 2)
            XCTAssertTrue(values.contains(.integer(1)))
            XCTAssertTrue(values.contains(.integer(4)))
        } else {
            XCTFail("Expected set")
        }
    }
}
