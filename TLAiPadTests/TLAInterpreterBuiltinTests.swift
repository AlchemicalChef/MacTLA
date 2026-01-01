import XCTest
@testable import MacTLA

/// Comprehensive tests for all built-in functions in TLAInterpreter
final class TLAInterpreterBuiltinTests: XCTestCase {

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

    // MARK: - Sequence Functions: Head

    func testHeadNormal() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == Head(<<1, 2, 3>>)
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .integer(1))
    }

    func testHeadSingleElement() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == Head(<<42>>)
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .integer(42))
    }

    func testHeadEmptyError() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == Head(<<>>)
        ====
        """

        XCTAssertThrowsError(try evaluateTestOp(source))
    }

    // MARK: - Sequence Functions: Tail

    func testTailNormal() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == Tail(<<1, 2, 3>>)
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .sequence([.integer(2), .integer(3)]))
    }

    func testTailSingleElement() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == Tail(<<1>>)
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .sequence([]))
    }

    func testTailEmptyError() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == Tail(<<>>)
        ====
        """

        XCTAssertThrowsError(try evaluateTestOp(source))
    }

    // MARK: - Sequence Functions: Len

    func testLenEmpty() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == Len(<<>>)
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .integer(0))
    }

    func testLenNonEmpty() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == Len(<<1, 2, 3, 4, 5>>)
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .integer(5))
    }

    // MARK: - Sequence Functions: Append

    func testAppendToEmpty() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == Append(<<>>, 1)
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .sequence([.integer(1)]))
    }

    func testAppendToNonEmpty() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == Append(<<1, 2>>, 3)
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .sequence([.integer(1), .integer(2), .integer(3)]))
    }

    // MARK: - Sequence Functions: Last

    func testLastNormal() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == Last(<<1, 2, 3>>)
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .integer(3))
    }

    func testLastSingleElement() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == Last(<<42>>)
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .integer(42))
    }

    func testLastEmptyError() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == Last(<<>>)
        ====
        """

        XCTAssertThrowsError(try evaluateTestOp(source))
    }

    // MARK: - Sequence Functions: Front

    func testFrontNormal() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == Front(<<1, 2, 3>>)
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .sequence([.integer(1), .integer(2)]))
    }

    func testFrontSingleElement() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == Front(<<1>>)
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .sequence([]))
    }

    // MARK: - Sequence Functions: Reverse

    func testReverseEmpty() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == Reverse(<<>>)
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .sequence([]))
    }

    func testReverseNonEmpty() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == Reverse(<<1, 2, 3>>)
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .sequence([.integer(3), .integer(2), .integer(1)]))
    }

    // MARK: - Sequence Functions: SelectSeq

    func testSelectSeqWithLambda() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == SelectSeq(<<1, 2, 3, 4, 5>>, LAMBDA x: x > 2)
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .sequence([.integer(3), .integer(4), .integer(5)]))
    }

    func testSelectSeqNoMatches() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == SelectSeq(<<1, 2, 3>>, LAMBDA x: x > 10)
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .sequence([]))
    }

    func testSelectSeqAllMatch() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == SelectSeq(<<1, 2, 3>>, LAMBDA x: x > 0)
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .sequence([.integer(1), .integer(2), .integer(3)]))
    }

    // MARK: - Set Functions: Cardinality

    func testCardinalityEmpty() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS FiniteSets
        Test == Cardinality({})
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .integer(0))
    }

    func testCardinalityNonEmpty() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS FiniteSets
        Test == Cardinality({1, 2, 3, 4, 5})
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .integer(5))
    }

    func testCardinalityWithDuplicates() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS FiniteSets
        Test == Cardinality({1, 1, 2, 2, 3})
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .integer(3))
    }

    // MARK: - Set Functions: IsFiniteSet

    func testIsFiniteSetAlwaysTrue() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS FiniteSets
        Test == IsFiniteSet({1, 2, 3})
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .boolean(true))
    }

    func testIsFiniteSetEmpty() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS FiniteSets
        Test == IsFiniteSet({})
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .boolean(true))
    }

    // MARK: - Set Functions: Min/Max

    func testMinNormal() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Integers
        Test == Min({3, 1, 4, 1, 5})
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .integer(1))
    }

    func testMinNegatives() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Integers
        Test == Min({-5, -1, 0, 3})
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .integer(-5))
    }

    func testMinEmptyError() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Integers
        Test == Min({})
        ====
        """

        XCTAssertThrowsError(try evaluateTestOp(source))
    }

    func testMaxNormal() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Integers
        Test == Max({3, 1, 4, 1, 5})
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .integer(5))
    }

    func testMaxNegatives() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Integers
        Test == Max({-5, -1, 0})
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .integer(0))
    }

    func testMaxEmptyError() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Integers
        Test == Max({})
        ====
        """

        XCTAssertThrowsError(try evaluateTestOp(source))
    }

    // MARK: - TLC Functions: Print

    func testPrintReturnsValue() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS TLC
        Test == Print("hello", 42)
        ====
        """

        let result = try evaluateTestOp(source)
        // Print returns its second argument
        XCTAssertEqual(result, .integer(42))
    }

    // MARK: - TLC Functions: PrintT

    func testPrintTReturnsTrue() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS TLC
        Test == PrintT("debug message")
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .boolean(true))
    }

    // MARK: - TLC Functions: Assert

    func testAssertTrueCondition() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS TLC
        Test == Assert(1 + 1 = 2, "Math works")
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .boolean(true))
    }

    func testAssertFalseConditionError() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS TLC
        Test == Assert(1 + 1 = 3, "Math failed")
        ====
        """

        XCTAssertThrowsError(try evaluateTestOp(source))
    }

    // MARK: - TLC Functions: ToString

    func testToStringInteger() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS TLC
        Test == ToString(42)
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .string("42"))
    }

    func testToStringBoolean() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS TLC
        Test == ToString(TRUE)
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .string("TRUE"))
    }

    // MARK: - Range Function

    func testRangeOfFunction() throws {
        let source = """
        ---- MODULE Test ----
        f == [x \\in {1, 2, 3} |-> x * 2]
        Test == Range(f)
        ====
        """

        // Note: Range might be defined differently depending on the implementation
        // This test assumes Range returns the set of values in the function's codomain
        guard let module = parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let interpreter = makeInterpreter()
        var env = makeEnv()
        try interpreter.loadModule(module, into: &env)

        let result = try interpreter.evaluate(.identifier("Test", .unknown), in: env)

        if case .set(let values) = result {
            XCTAssertTrue(values.contains(.integer(2)))
            XCTAssertTrue(values.contains(.integer(4)))
            XCTAssertTrue(values.contains(.integer(6)))
        } else {
            XCTFail("Expected set result")
        }
    }

    // MARK: - Sequence Concatenation

    func testSequenceConcatenation() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == <<1, 2>> \\o <<3, 4>>
        ====
        """

        let result = try evaluateTestOp(source)
        XCTAssertEqual(result, .sequence([.integer(1), .integer(2), .integer(3), .integer(4)]))
    }

    // MARK: - DOMAIN Operator

    func testDomainOfFunction() throws {
        let source = """
        ---- MODULE Test ----
        f == [x \\in {1, 2, 3} |-> x * 2]
        Test == DOMAIN f
        ====
        """

        guard let module = parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let interpreter = makeInterpreter()
        var env = makeEnv()
        try interpreter.loadModule(module, into: &env)

        let result = try interpreter.evaluate(.identifier("Test", .unknown), in: env)

        if case .set(let values) = result {
            XCTAssertEqual(values.count, 3)
            XCTAssertTrue(values.contains(.integer(1)))
            XCTAssertTrue(values.contains(.integer(2)))
            XCTAssertTrue(values.contains(.integer(3)))
        } else {
            XCTFail("Expected set result")
        }
    }

    func testDomainOfSequence() throws {
        let source = """
        ---- MODULE Test ----
        Test == DOMAIN <<10, 20, 30>>
        ====
        """

        let result = try evaluateTestOp(source)

        if case .set(let values) = result {
            XCTAssertEqual(values.count, 3)
            XCTAssertTrue(values.contains(.integer(1)))
            XCTAssertTrue(values.contains(.integer(2)))
            XCTAssertTrue(values.contains(.integer(3)))
        } else {
            XCTFail("Expected set result")
        }
    }

    // MARK: - SUBSET (Power Set)

    func testSubsetOperator() throws {
        let source = """
        ---- MODULE Test ----
        Test == SUBSET {1, 2}
        ====
        """

        let result = try evaluateTestOp(source)

        if case .set(let powerSet) = result {
            // Power set of {1, 2} should have 4 elements: {}, {1}, {2}, {1, 2}
            XCTAssertEqual(powerSet.count, 4)
        } else {
            XCTFail("Expected set result")
        }
    }

    func testSubsetEmpty() throws {
        let source = """
        ---- MODULE Test ----
        Test == SUBSET {}
        ====
        """

        let result = try evaluateTestOp(source)

        if case .set(let powerSet) = result {
            // Power set of {} is {{}}
            XCTAssertEqual(powerSet.count, 1)
            XCTAssertTrue(powerSet.contains(.set([])))
        } else {
            XCTFail("Expected set result")
        }
    }

    // MARK: - UNION (Generalized Union)

    func testUnionOperator() throws {
        let source = """
        ---- MODULE Test ----
        Test == UNION {{1, 2}, {2, 3}, {3, 4}}
        ====
        """

        let result = try evaluateTestOp(source)

        if case .set(let union) = result {
            XCTAssertEqual(union.count, 4)
            XCTAssertTrue(union.contains(.integer(1)))
            XCTAssertTrue(union.contains(.integer(2)))
            XCTAssertTrue(union.contains(.integer(3)))
            XCTAssertTrue(union.contains(.integer(4)))
        } else {
            XCTFail("Expected set result")
        }
    }

    func testUnionEmpty() throws {
        let source = """
        ---- MODULE Test ----
        Test == UNION {}
        ====
        """

        let result = try evaluateTestOp(source)

        if case .set(let union) = result {
            XCTAssertEqual(union.count, 0)
        } else {
            XCTFail("Expected set result")
        }
    }
}
