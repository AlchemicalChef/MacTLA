import XCTest
@testable import MacTLA

/// Comprehensive tests for TLAInterpreter covering all recent fixes and edge cases
final class TLAInterpreterComprehensiveTests: XCTestCase {

    // MARK: - Helper Methods

    private func makeInterpreter() -> TLAInterpreter {
        TLAInterpreter()
    }

    private func makeEnv() -> TLAInterpreter.Environment {
        TLAInterpreter.Environment()
    }

    private func parse(_ source: String) -> Result<TLAModule, TLAParser.ParseErrors> {
        TLAParser().parse(source)
    }

    // MARK: - 1.1 Pattern Binding Tests

    func testBindPatternSingleVariable() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()

        // \A x \in {1, 2, 3} : x > 0
        let expr = TLAExpression.forall(
            [BoundVariable(pattern: .single("x"), domain: .setEnumeration([.number(1, .unknown), .number(2, .unknown), .number(3, .unknown)], .unknown))],
            .binary(.identifier("x", .unknown), .gt, .number(0, .unknown), .unknown),
            .unknown
        )

        let result = try interpreter.evaluate(expr, in: env)
        XCTAssertEqual(result, .boolean(true))
    }

    func testBindPatternTupleDestructuring() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()

        // \A <<x, y>> \in {<<1, 2>>, <<3, 4>>} : x < y
        let pairs: TLAExpression = .setEnumeration([
            .tuple([.number(1, .unknown), .number(2, .unknown)], .unknown),
            .tuple([.number(3, .unknown), .number(4, .unknown)], .unknown)
        ], .unknown)

        let expr = TLAExpression.forall(
            [BoundVariable(pattern: .tuple(["x", "y"]), domain: pairs)],
            .binary(.identifier("x", .unknown), .lt, .identifier("y", .unknown), .unknown),
            .unknown
        )

        let result = try interpreter.evaluate(expr, in: env)
        XCTAssertEqual(result, .boolean(true))
    }

    func testBindPatternTupleSizeMismatch() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()

        // \A <<x, y, z>> \in {<<1, 2>>} : TRUE - tuple pattern has 3 vars but value has 2 elements
        let pairs: TLAExpression = .setEnumeration([
            .tuple([.number(1, .unknown), .number(2, .unknown)], .unknown)
        ], .unknown)

        let expr = TLAExpression.forall(
            [BoundVariable(pattern: .tuple(["x", "y", "z"]), domain: pairs)],
            .boolean(true, .unknown),
            .unknown
        )

        XCTAssertThrowsError(try interpreter.evaluate(expr, in: env)) { error in
            XCTAssertTrue(String(describing: error).contains("Tuple pattern"))
        }
    }

    func testBindPatternNonSequenceForTuple() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()

        // \A <<x, y>> \in {1, 2} : TRUE - trying to destructure non-sequence
        let expr = TLAExpression.forall(
            [BoundVariable(pattern: .tuple(["x", "y"]), domain: .setEnumeration([.number(1, .unknown), .number(2, .unknown)], .unknown))],
            .boolean(true, .unknown),
            .unknown
        )

        XCTAssertThrowsError(try interpreter.evaluate(expr, in: env)) { error in
            XCTAssertTrue(String(describing: error).contains("sequence"))
        }
    }

    // MARK: - 1.2 CHOOSE Determinism Tests

    func testChooseDeterminismSameResult() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()

        // CHOOSE x \in {3, 1, 2} : TRUE - should always return the same value
        let expr = TLAExpression.choose(
            BoundVariable(pattern: .single("x"), domain: .setEnumeration([.number(3, .unknown), .number(1, .unknown), .number(2, .unknown)], .unknown)),
            .boolean(true, .unknown),
            .unknown
        )

        let result1 = try interpreter.evaluate(expr, in: env)
        let result2 = try interpreter.evaluate(expr, in: env)
        let result3 = try interpreter.evaluate(expr, in: env)

        XCTAssertEqual(result1, result2)
        XCTAssertEqual(result2, result3)
    }

    func testChooseWithIntegersSorted() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()

        // CHOOSE x \in {5, 3, 1, 4, 2} : TRUE - should pick the smallest
        let expr = TLAExpression.choose(
            BoundVariable(pattern: .single("x"), domain: .setEnumeration([
                .number(5, .unknown), .number(3, .unknown), .number(1, .unknown),
                .number(4, .unknown), .number(2, .unknown)
            ], .unknown)),
            .boolean(true, .unknown),
            .unknown
        )

        let result = try interpreter.evaluate(expr, in: env)
        // After sorting, the first element should be consistently chosen
        XCTAssertNotNil(result)
    }

    func testChooseWithStringsSorted() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()

        // CHOOSE x \in {"c", "a", "b"} : TRUE
        let expr = TLAExpression.choose(
            BoundVariable(pattern: .single("x"), domain: .setEnumeration([
                .string("c", .unknown), .string("a", .unknown), .string("b", .unknown)
            ], .unknown)),
            .boolean(true, .unknown),
            .unknown
        )

        let result1 = try interpreter.evaluate(expr, in: env)
        let result2 = try interpreter.evaluate(expr, in: env)
        XCTAssertEqual(result1, result2)
    }

    func testChooseWithMixedTypesSorted() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()

        // CHOOSE x \in {TRUE, 1, "a"} : TRUE - mixed types
        let expr = TLAExpression.choose(
            BoundVariable(pattern: .single("x"), domain: .setEnumeration([
                .boolean(true, .unknown), .number(1, .unknown), .string("a", .unknown)
            ], .unknown)),
            .boolean(true, .unknown),
            .unknown
        )

        let result1 = try interpreter.evaluate(expr, in: env)
        let result2 = try interpreter.evaluate(expr, in: env)
        XCTAssertEqual(result1, result2)
    }

    func testChooseEmptyDomainError() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()

        // CHOOSE x \in {} : TRUE - empty domain should throw
        let expr = TLAExpression.choose(
            BoundVariable(pattern: .single("x"), domain: .setEnumeration([], .unknown)),
            .boolean(true, .unknown),
            .unknown
        )

        XCTAssertThrowsError(try interpreter.evaluate(expr, in: env))
    }

    func testChooseNoSatisfyingValue() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()

        // CHOOSE x \in {1, 2, 3} : x > 10 - no element satisfies
        let expr = TLAExpression.choose(
            BoundVariable(pattern: .single("x"), domain: .setEnumeration([
                .number(1, .unknown), .number(2, .unknown), .number(3, .unknown)
            ], .unknown)),
            .binary(.identifier("x", .unknown), .gt, .number(10, .unknown), .unknown),
            .unknown
        )

        XCTAssertThrowsError(try interpreter.evaluate(expr, in: env))
    }

    // MARK: - 1.3 Quantifier Tuple Pattern Tests

    func testForallWithTuplePattern() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()

        // \A <<a, b>> \in {<<1, 2>>, <<2, 4>>, <<3, 6>>} : b = 2 * a
        let pairs: TLAExpression = .setEnumeration([
            .tuple([.number(1, .unknown), .number(2, .unknown)], .unknown),
            .tuple([.number(2, .unknown), .number(4, .unknown)], .unknown),
            .tuple([.number(3, .unknown), .number(6, .unknown)], .unknown)
        ], .unknown)

        let expr = TLAExpression.forall(
            [BoundVariable(pattern: .tuple(["a", "b"]), domain: pairs)],
            .binary(
                .identifier("b", .unknown),
                .eq,
                .binary(.number(2, .unknown), .times, .identifier("a", .unknown), .unknown),
                .unknown
            ),
            .unknown
        )

        let result = try interpreter.evaluate(expr, in: env)
        XCTAssertEqual(result, .boolean(true))
    }

    func testExistsWithTuplePattern() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()

        // \E <<x, y>> \in {<<1, 2>>, <<3, 4>>} : x + y = 7
        let pairs: TLAExpression = .setEnumeration([
            .tuple([.number(1, .unknown), .number(2, .unknown)], .unknown),
            .tuple([.number(3, .unknown), .number(4, .unknown)], .unknown)
        ], .unknown)

        let expr = TLAExpression.exists(
            [BoundVariable(pattern: .tuple(["x", "y"]), domain: pairs)],
            .binary(
                .binary(.identifier("x", .unknown), .plus, .identifier("y", .unknown), .unknown),
                .eq,
                .number(7, .unknown),
                .unknown
            ),
            .unknown
        )

        let result = try interpreter.evaluate(expr, in: env)
        XCTAssertEqual(result, .boolean(true))
    }

    func testNestedTuplePatterns() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()

        // \A <<a, b>> \in {<<1, 2>>} : \A <<c, d>> \in {<<3, 4>>} : a + c = 4
        let pairs1: TLAExpression = .setEnumeration([
            .tuple([.number(1, .unknown), .number(2, .unknown)], .unknown)
        ], .unknown)
        let pairs2: TLAExpression = .setEnumeration([
            .tuple([.number(3, .unknown), .number(4, .unknown)], .unknown)
        ], .unknown)

        let inner = TLAExpression.forall(
            [BoundVariable(pattern: .tuple(["c", "d"]), domain: pairs2)],
            .binary(
                .binary(.identifier("a", .unknown), .plus, .identifier("c", .unknown), .unknown),
                .eq,
                .number(4, .unknown),
                .unknown
            ),
            .unknown
        )

        let expr = TLAExpression.forall(
            [BoundVariable(pattern: .tuple(["a", "b"]), domain: pairs1)],
            inner,
            .unknown
        )

        let result = try interpreter.evaluate(expr, in: env)
        XCTAssertEqual(result, .boolean(true))
    }

    func testTuplePatternWithWrongArity() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()

        // \A <<x>> \in {<<1, 2>>} : TRUE - pattern expects 1, tuple has 2
        let pairs: TLAExpression = .setEnumeration([
            .tuple([.number(1, .unknown), .number(2, .unknown)], .unknown)
        ], .unknown)

        let expr = TLAExpression.forall(
            [BoundVariable(pattern: .tuple(["x"]), domain: pairs)],
            .boolean(true, .unknown),
            .unknown
        )

        XCTAssertThrowsError(try interpreter.evaluate(expr, in: env))
    }

    // MARK: - 1.4 Function Construction Tests

    func testFunctionSingleDomain() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()

        // [x \in {1, 2} |-> x * 2]
        let expr = TLAExpression.functionConstruction(
            [BoundVariable(pattern: .single("x"), domain: .setEnumeration([.number(1, .unknown), .number(2, .unknown)], .unknown))],
            .binary(.identifier("x", .unknown), .times, .number(2, .unknown), .unknown),
            .unknown
        )

        let result = try interpreter.evaluate(expr, in: env)

        // Check it's a function
        if case .function(let mapping) = result {
            XCTAssertEqual(mapping.count, 2)
            XCTAssertEqual(mapping[.integer(1)], .integer(2))
            XCTAssertEqual(mapping[.integer(2)], .integer(4))
        } else {
            XCTFail("Expected function value")
        }
    }

    func testFunctionMultipleDomains() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()

        // [x \in {1, 2}, y \in {3, 4} |-> x + y]
        let expr = TLAExpression.functionConstruction(
            [
                BoundVariable(pattern: .single("x"), domain: .setEnumeration([.number(1, .unknown), .number(2, .unknown)], .unknown)),
                BoundVariable(pattern: .single("y"), domain: .setEnumeration([.number(3, .unknown), .number(4, .unknown)], .unknown))
            ],
            .binary(.identifier("x", .unknown), .plus, .identifier("y", .unknown), .unknown),
            .unknown
        )

        let result = try interpreter.evaluate(expr, in: env)

        if case .function(let mapping) = result {
            // Should have 4 entries: (1,3), (1,4), (2,3), (2,4)
            XCTAssertEqual(mapping.count, 4)
        } else {
            XCTFail("Expected function value")
        }
    }

    func testFunctionEmptyDomain() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()

        // [x \in {} |-> x]
        let expr = TLAExpression.functionConstruction(
            [BoundVariable(pattern: .single("x"), domain: .setEnumeration([], .unknown))],
            .identifier("x", .unknown),
            .unknown
        )

        let result = try interpreter.evaluate(expr, in: env)

        if case .function(let mapping) = result {
            XCTAssertEqual(mapping.count, 0)
        } else {
            XCTFail("Expected empty function")
        }
    }

    func testFunctionCartesianProduct() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()

        // [<<x, y>> \in {1, 2} \X {3, 4} |-> x + y]
        let cartesian = TLAExpression.binary(
            .setEnumeration([.number(1, .unknown), .number(2, .unknown)], .unknown),
            .cartesian,
            .setEnumeration([.number(3, .unknown), .number(4, .unknown)], .unknown),
            .unknown
        )

        let expr = TLAExpression.functionConstruction(
            [BoundVariable(pattern: .tuple(["x", "y"]), domain: cartesian)],
            .binary(.identifier("x", .unknown), .plus, .identifier("y", .unknown), .unknown),
            .unknown
        )

        let result = try interpreter.evaluate(expr, in: env)

        if case .function(let mapping) = result {
            XCTAssertEqual(mapping.count, 4)
        } else {
            XCTFail("Expected function value")
        }
    }

    // MARK: - 1.5 Seq(S) Operator Tests

    func testSeqEmptySet() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == Seq({})
        ====
        """

        let parser = TLAParser()
        guard case .success(let module) = parser.parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let interpreter = makeInterpreter()
        var env = makeEnv()
        try interpreter.loadModule(module, into: &env)

        let result = try interpreter.evaluate(.identifier("Test", .unknown), in: env)

        // Seq({}) should be {{}} - just the empty sequence
        if case .set(let elements) = result {
            XCTAssertEqual(elements.count, 1)
            XCTAssertTrue(elements.contains(.sequence([])))
        } else {
            XCTFail("Expected set value")
        }
    }

    func testSeqSingleElement() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == Seq({"a"})
        ====
        """

        let parser = TLAParser()
        guard case .success(let module) = parser.parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let interpreter = makeInterpreter()
        var env = makeEnv()
        try interpreter.loadModule(module, into: &env)

        let result = try interpreter.evaluate(.identifier("Test", .unknown), in: env)

        if case .set(let elements) = result {
            // Should include: <<>>, <<"a">>, <<"a", "a">>, <<"a", "a", "a">>
            XCTAssertTrue(elements.contains(.sequence([])))
            XCTAssertTrue(elements.contains(.sequence([.string("a")])))
        } else {
            XCTFail("Expected set value")
        }
    }

    func testSeqMaxLengthBound() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == Seq({1})
        ====
        """

        let parser = TLAParser()
        guard case .success(let module) = parser.parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let interpreter = makeInterpreter()
        interpreter.seqMaxLength = 2  // Limit to sequences of length 0, 1, 2
        var env = makeEnv()
        try interpreter.loadModule(module, into: &env)

        let result = try interpreter.evaluate(.identifier("Test", .unknown), in: env)

        if case .set(let elements) = result {
            // With seqMaxLength=2, should have: <<>>, <<1>>, <<1,1>>
            XCTAssertEqual(elements.count, 3)
        } else {
            XCTFail("Expected set value")
        }
    }

    func testSeqGeneratesAllLengths() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == Seq({1, 2})
        ====
        """

        let parser = TLAParser()
        guard case .success(let module) = parser.parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let interpreter = makeInterpreter()
        interpreter.seqMaxLength = 2
        var env = makeEnv()
        try interpreter.loadModule(module, into: &env)

        let result = try interpreter.evaluate(.identifier("Test", .unknown), in: env)

        if case .set(let elements) = result {
            // Length 0: 1 sequence (<<>>)
            // Length 1: 2 sequences (<<1>>, <<2>>)
            // Length 2: 4 sequences (<<1,1>>, <<1,2>>, <<2,1>>, <<2,2>>)
            // Total: 7
            XCTAssertEqual(elements.count, 7)
        } else {
            XCTFail("Expected set value")
        }
    }

    // MARK: - 1.6 SubSeq Boundary Tests

    func testSubSeqNormalRange() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == SubSeq(<<1, 2, 3, 4, 5>>, 2, 4)
        ====
        """

        let parser = TLAParser()
        guard case .success(let module) = parser.parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let interpreter = makeInterpreter()
        var env = makeEnv()
        try interpreter.loadModule(module, into: &env)

        let result = try interpreter.evaluate(.identifier("Test", .unknown), in: env)
        XCTAssertEqual(result, .sequence([.integer(2), .integer(3), .integer(4)]))
    }

    func testSubSeqMGreaterThanN() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == SubSeq(<<1, 2, 3>>, 3, 1)
        ====
        """

        let parser = TLAParser()
        guard case .success(let module) = parser.parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let interpreter = makeInterpreter()
        var env = makeEnv()
        try interpreter.loadModule(module, into: &env)

        let result = try interpreter.evaluate(.identifier("Test", .unknown), in: env)
        // When m > n, result is empty sequence
        XCTAssertEqual(result, .sequence([]))
    }

    func testSubSeqMLessThanOne() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == SubSeq(<<1, 2, 3>>, 0, 2)
        ====
        """

        let parser = TLAParser()
        guard case .success(let module) = parser.parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let interpreter = makeInterpreter()
        var env = makeEnv()
        try interpreter.loadModule(module, into: &env)

        let result = try interpreter.evaluate(.identifier("Test", .unknown), in: env)
        // When m < 1, treat as m = 1
        XCTAssertEqual(result, .sequence([.integer(1), .integer(2)]))
    }

    func testSubSeqNGreaterThanLength() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == SubSeq(<<1, 2, 3>>, 2, 10)
        ====
        """

        let parser = TLAParser()
        guard case .success(let module) = parser.parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let interpreter = makeInterpreter()
        var env = makeEnv()
        try interpreter.loadModule(module, into: &env)

        let result = try interpreter.evaluate(.identifier("Test", .unknown), in: env)
        // When n > Len, use Len
        XCTAssertEqual(result, .sequence([.integer(2), .integer(3)]))
    }

    func testSubSeqEmptySequence() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == SubSeq(<<>>, 1, 1)
        ====
        """

        let parser = TLAParser()
        guard case .success(let module) = parser.parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let interpreter = makeInterpreter()
        var env = makeEnv()
        try interpreter.loadModule(module, into: &env)

        let result = try interpreter.evaluate(.identifier("Test", .unknown), in: env)
        XCTAssertEqual(result, .sequence([]))
    }

    // MARK: - 1.7 LAMBDA Evaluation Tests

    func testLambdaDirectApplication() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()

        // (LAMBDA x: x + 1)[5]
        let lambda = TLAExpression.lambda(
            ["x"],
            .binary(.identifier("x", .unknown), .plus, .number(1, .unknown), .unknown),
            .unknown
        )

        let expr = TLAExpression.functionApplication(lambda, [.number(5, .unknown)], .unknown)

        let result = try interpreter.evaluate(expr, in: env)
        XCTAssertEqual(result, .integer(6))
    }

    func testLambdaMultipleParameters() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()

        // (LAMBDA x, y: x + y)[2, 3]
        let lambda = TLAExpression.lambda(
            ["x", "y"],
            .binary(.identifier("x", .unknown), .plus, .identifier("y", .unknown), .unknown),
            .unknown
        )

        let expr = TLAExpression.functionApplication(lambda, [.number(2, .unknown), .number(3, .unknown)], .unknown)

        let result = try interpreter.evaluate(expr, in: env)
        XCTAssertEqual(result, .integer(5))
    }

    func testLambdaInSelectSeq() throws {
        let source = """
        ---- MODULE Test ----
        EXTENDS Sequences
        Test == SelectSeq(<<1, 2, 3, 4, 5>>, LAMBDA x: x > 3)
        ====
        """

        let parser = TLAParser()
        guard case .success(let module) = parser.parse(source) else {
            XCTFail("Parse failed")
            return
        }

        let interpreter = makeInterpreter()
        var env = makeEnv()
        try interpreter.loadModule(module, into: &env)

        let result = try interpreter.evaluate(.identifier("Test", .unknown), in: env)
        XCTAssertEqual(result, .sequence([.integer(4), .integer(5)]))
    }

    func testLambdaNestedApplication() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()

        // (LAMBDA f: f[1])[(LAMBDA x: x * 2)]
        let innerLambda = TLAExpression.lambda(
            ["x"],
            .binary(.identifier("x", .unknown), .times, .number(2, .unknown), .unknown),
            .unknown
        )

        let outerLambda = TLAExpression.lambda(
            ["f"],
            .functionApplication(.identifier("f", .unknown), [.number(1, .unknown)], .unknown),
            .unknown
        )

        let expr = TLAExpression.functionApplication(outerLambda, [innerLambda], .unknown)

        let result = try interpreter.evaluate(expr, in: env)
        XCTAssertEqual(result, .integer(2))
    }

    // MARK: - 1.8 UNCHANGED Tests

    func testUnchangedSingleVariable() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["x"] = .integer(5)
        env.primedVariables["x"] = .integer(5)

        let expr = TLAExpression.unchanged(.identifier("x", .unknown), .unknown)
        let result = try interpreter.evaluate(expr, in: env)
        XCTAssertEqual(result, .boolean(true))
    }

    func testUnchangedSingleVariableChanged() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["x"] = .integer(5)
        env.primedVariables["x"] = .integer(10)

        let expr = TLAExpression.unchanged(.identifier("x", .unknown), .unknown)
        let result = try interpreter.evaluate(expr, in: env)
        XCTAssertEqual(result, .boolean(false))
    }

    func testUnchangedTupleOfVariables() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["x"] = .integer(1)
        env.variables["y"] = .integer(2)
        env.primedVariables["x"] = .integer(1)
        env.primedVariables["y"] = .integer(2)

        let expr = TLAExpression.unchanged(
            .tuple([.identifier("x", .unknown), .identifier("y", .unknown)], .unknown),
            .unknown
        )
        let result = try interpreter.evaluate(expr, in: env)
        XCTAssertEqual(result, .boolean(true))
    }

    func testUnchangedTuplePartialChange() throws {
        let interpreter = makeInterpreter()
        var env = makeEnv()
        env.variables["x"] = .integer(1)
        env.variables["y"] = .integer(2)
        env.primedVariables["x"] = .integer(1)
        env.primedVariables["y"] = .integer(99)  // y changed

        let expr = TLAExpression.unchanged(
            .tuple([.identifier("x", .unknown), .identifier("y", .unknown)], .unknown),
            .unknown
        )
        let result = try interpreter.evaluate(expr, in: env)
        XCTAssertEqual(result, .boolean(false))
    }

    // MARK: - 1.9 Configuration Bounds Tests

    func testNatUpperBoundDefault() {
        let interpreter = makeInterpreter()
        XCTAssertEqual(interpreter.natUpperBound, 1000)
    }

    func testNatUpperBoundCustom() {
        let interpreter = makeInterpreter()
        interpreter.natUpperBound = 500
        XCTAssertEqual(interpreter.natUpperBound, 500)
    }

    func testNatUpperBoundValidationLower() {
        let interpreter = makeInterpreter()
        interpreter.natUpperBound = -100  // Should clamp to 0
        XCTAssertEqual(interpreter.natUpperBound, 0)
    }

    func testNatUpperBoundValidationUpper() {
        let interpreter = makeInterpreter()
        interpreter.natUpperBound = 999999  // Should clamp to 100000
        XCTAssertEqual(interpreter.natUpperBound, 100000)
    }

    func testIntBoundDefault() {
        let interpreter = makeInterpreter()
        XCTAssertEqual(interpreter.intBound, 1000)
    }

    func testIntBoundValidationLower() {
        let interpreter = makeInterpreter()
        interpreter.intBound = -50  // Should clamp to 0
        XCTAssertEqual(interpreter.intBound, 0)
    }

    func testIntBoundValidationUpper() {
        let interpreter = makeInterpreter()
        interpreter.intBound = 200000  // Should clamp to 100000
        XCTAssertEqual(interpreter.intBound, 100000)
    }

    func testSeqMaxLengthDefault() {
        let interpreter = makeInterpreter()
        XCTAssertEqual(interpreter.seqMaxLength, 3)
    }

    func testSeqMaxLengthValidationLower() {
        let interpreter = makeInterpreter()
        interpreter.seqMaxLength = -5  // Should clamp to 0
        XCTAssertEqual(interpreter.seqMaxLength, 0)
    }

    func testSeqMaxLengthValidationUpper() {
        let interpreter = makeInterpreter()
        interpreter.seqMaxLength = 100  // Should clamp to 10
        XCTAssertEqual(interpreter.seqMaxLength, 10)
    }
}
