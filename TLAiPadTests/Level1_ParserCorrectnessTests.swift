import XCTest
@testable import MacTLA

/// Level 1: Comprehensive Parser Correctness Tests
/// Tests all TLA+ syntax constructs for correct parsing
final class Level1_ParserCorrectnessTests: XCTestCase {

    private func parse(_ source: String) -> Result<TLAModule, TLAParser.ParseErrors> {
        TLAParser().parse(source)
    }

    private func assertParses(_ source: String, file: StaticString = #file, line: UInt = #line) {
        let result = parse(source)
        if case .failure(let errors) = result {
            XCTFail("Parse failed: \(errors.errors)", file: file, line: line)
        }
    }

    private func assertParseError(_ source: String, file: StaticString = #file, line: UInt = #line) {
        let result = parse(source)
        if case .success = result {
            XCTFail("Expected parse error but succeeded", file: file, line: line)
        }
    }

    // MARK: - Module Structure

    func testModuleWithAllDeclarationTypes() {
        let source = """
        ---- MODULE Complete ----
        EXTENDS Naturals, Sequences
        CONSTANTS N, M
        VARIABLES x, y, z
        ASSUME N > 0

        Init == x = 0 /\\ y = 0 /\\ z = 0
        Next == x' = x + 1 /\\ y' = y /\\ z' = z

        TypeOK == x \\in Nat
        Spec == Init /\\ [][Next]_<<x, y, z>>

        THEOREM Safety == []TypeOK
        ====
        """
        assertParses(source)
    }

    func testModuleWithDashes() {
        let source = """
        -------- MODULE WithDashes --------
        ====
        """
        assertParses(source)
    }

    func testModuleWithMinimalDashes() {
        let source = """
        ---- MODULE Min ----
        ====
        """
        assertParses(source)
    }

    // MARK: - All Unary Operators

    func testUnaryNot() {
        assertParses("""
        ---- MODULE Test ----
        Test == ~TRUE
        ====
        """)
    }

    func testUnaryNegative() {
        assertParses("""
        ---- MODULE Test ----
        Test == -5
        ====
        """)
    }

    func testUnaryDomain() {
        assertParses("""
        ---- MODULE Test ----
        Test == DOMAIN f
        ====
        """)
    }

    func testUnarySubset() {
        assertParses("""
        ---- MODULE Test ----
        Test == SUBSET S
        ====
        """)
    }

    func testUnaryUnion() {
        assertParses("""
        ---- MODULE Test ----
        Test == UNION S
        ====
        """)
    }

    func testUnaryEnabled() {
        assertParses("""
        ---- MODULE Test ----
        Test == ENABLED Next
        ====
        """)
    }

    func testUnaryUnchanged() {
        assertParses("""
        ---- MODULE Test ----
        Test == UNCHANGED x
        ====
        """)
    }

    // MARK: - All Binary Operators

    func testLogicalOperators() {
        assertParses("""
        ---- MODULE Test ----
        And == a /\\ b
        Or == a \\/ b
        Implies == a => b
        Iff == a <=> b
        ====
        """)
    }

    func testComparisonOperators() {
        assertParses("""
        ---- MODULE Test ----
        Eq == a = b
        Neq == a # b
        Neq2 == a /= b
        Lt == a < b
        Le == a <= b
        Le2 == a =< b
        Gt == a > b
        Ge == a >= b
        ====
        """)
    }

    func testArithmeticOperators() {
        assertParses("""
        ---- MODULE Test ----
        Plus == a + b
        Minus == a - b
        Times == a * b
        Div == a \\div b
        Mod == a % b
        Exp == a ^ b
        ====
        """)
    }

    func testSetOperators() {
        assertParses("""
        ---- MODULE Test ----
        ElementOf == a \\in S
        NotElementOf == a \\notin S
        SubsetOf == A \\subseteq B
        SupersetOf == A \\supseteq B
        ProperSubset == A \\subset B
        ProperSuperset == A \\supset B
        Union == A \\union B
        Intersect == A \\intersect B
        SetMinus == A \\ B
        Cartesian == A \\X B
        ====
        """)
    }

    func testSequenceOperators() {
        assertParses("""
        ---- MODULE Test ----
        Concat == s \\o t
        Append == Append(s, x)
        ====
        """)
    }

    func testFunctionOperators() {
        assertParses("""
        ---- MODULE Test ----
        Compose == f @@ g
        Override == f @@ g
        Pair == x :> y
        ====
        """)
    }

    // MARK: - Set Constructs

    func testSetEnumerationVariants() {
        assertParses("""
        ---- MODULE Test ----
        Empty == {}
        Single == {1}
        Multiple == {1, 2, 3}
        Nested == {{1}, {2}, {3}}
        Mixed == {1, "a", TRUE, {}}
        ====
        """)
    }

    func testSetComprehensionFilter() {
        assertParses("""
        ---- MODULE Test ----
        Filtered == {x \\in S : x > 0}
        ====
        """)
    }

    func testSetComprehensionMap() {
        assertParses("""
        ---- MODULE Test ----
        Mapped == {x * 2 : x \\in S}
        ====
        """)
    }

    func testSetComprehensionWithTuplePattern() {
        assertParses("""
        ---- MODULE Test ----
        Pairs == {<<x, y>> \\in S \\X T : x < y}
        ====
        """)
    }

    func testSetRangeVariants() {
        assertParses("""
        ---- MODULE Test ----
        Simple == 1..10
        WithVars == a..b
        Nested == (a + 1)..(b - 1)
        ====
        """)
    }

    // MARK: - Quantifiers

    func testForallVariants() {
        assertParses("""
        ---- MODULE Test ----
        Simple == \\A x \\in S : P(x)
        Multiple == \\A x, y \\in S : P(x, y)
        Tuple == \\A <<x, y>> \\in S : x < y
        Unbounded == \\A x : P(x)
        ====
        """)
    }

    func testExistsVariants() {
        assertParses("""
        ---- MODULE Test ----
        Simple == \\E x \\in S : P(x)
        Multiple == \\E x, y \\in S : P(x, y)
        Tuple == \\E <<x, y>> \\in S : x = y
        Unbounded == \\E x : P(x)
        ====
        """)
    }

    func testChooseVariants() {
        assertParses("""
        ---- MODULE Test ----
        Simple == CHOOSE x \\in S : P(x)
        Unbounded == CHOOSE x : P(x)
        ====
        """)
    }

    // MARK: - Functions and Records

    func testFunctionConstructionVariants() {
        assertParses("""
        ---- MODULE Test ----
        Simple == [x \\in S |-> x * 2]
        MultiArg == [x \\in S, y \\in T |-> x + y]
        Nested == [x \\in S |-> [y \\in T |-> x + y]]
        ====
        """)
    }

    func testFunctionApplicationVariants() {
        assertParses("""
        ---- MODULE Test ----
        Simple == f[x]
        Multiple == f[x, y]
        Nested == f[x][y]
        Chained == f[g[x]]
        ====
        """)
    }

    func testRecordConstructionVariants() {
        assertParses("""
        ---- MODULE Test ----
        Simple == [x |-> 1, y |-> 2]
        Nested == [a |-> [b |-> 1]]
        WithExpr == [x |-> 1 + 2, y |-> f[z]]
        ====
        """)
    }

    func testRecordAccessVariants() {
        assertParses("""
        ---- MODULE Test ----
        Simple == r.x
        Chained == r.a.b.c
        WithIndex == r.items[i]
        ====
        """)
    }

    func testExceptVariants() {
        assertParses("""
        ---- MODULE Test ----
        SimpleFunc == [f EXCEPT ![1] = 42]
        SimpleRecord == [r EXCEPT !.x = 42]
        Multiple == [f EXCEPT ![1] = 42, ![2] = 43]
        Nested == [f EXCEPT ![1][2] = 42]
        WithAt == [f EXCEPT ![1] = @ + 1]
        ====
        """)
    }

    // MARK: - Tuples/Sequences

    func testTupleVariants() {
        assertParses("""
        ---- MODULE Test ----
        Empty == <<>>
        Single == <<1>>
        Multiple == <<1, 2, 3>>
        Nested == <<<<1, 2>>, <<3, 4>>>>
        Mixed == <<1, "a", TRUE>>
        ====
        """)
    }

    // MARK: - Control Flow

    func testIfThenElseVariants() {
        assertParses("""
        ---- MODULE Test ----
        Simple == IF c THEN a ELSE b
        Nested == IF c1 THEN IF c2 THEN a ELSE b ELSE c
        WithExpr == IF x > 0 THEN x ELSE -x
        ====
        """)
    }

    func testCaseVariants() {
        assertParses("""
        ---- MODULE Test ----
        Simple == CASE x = 1 -> "one" [] OTHER -> "other"
        Multiple == CASE x = 1 -> "one" [] x = 2 -> "two" [] OTHER -> "other"
        NoOther == CASE x = 1 -> "one" [] x = 2 -> "two"
        ====
        """)
    }

    func testLetInVariants() {
        assertParses("""
        ---- MODULE Test ----
        Simple == LET x == 5 IN x + 1
        Multiple == LET x == 5 y == 10 IN x + y
        WithParams == LET F(a) == a + 1 IN F(5)
        Nested == LET x == LET y == 5 IN y + 1 IN x * 2
        ====
        """)
    }

    // MARK: - Lambda

    func testLambdaVariants() {
        assertParses("""
        ---- MODULE Test ----
        Single == LAMBDA x : x + 1
        Multiple == LAMBDA x, y : x + y
        Nested == LAMBDA x : LAMBDA y : x + y
        ====
        """)
    }

    // MARK: - Temporal Operators

    func testTemporalAlways() {
        assertParses("""
        ---- MODULE Test ----
        Test == []P
        Nested == [][](P /\\ Q)
        ====
        """)
    }

    func testTemporalEventually() {
        assertParses("""
        ---- MODULE Test ----
        Test == <>P
        Nested == <><>(P \\/ Q)
        ====
        """)
    }

    func testTemporalLeadsto() {
        assertParses("""
        ---- MODULE Test ----
        Test == P ~> Q
        Chained == P ~> Q ~> R
        ====
        """)
    }

    func testTemporalStuttering() {
        assertParses("""
        ---- MODULE Test ----
        Simple == [Next]_x
        Tuple == [Next]_<<x, y>>
        ====
        """)
    }

    func testTemporalAction() {
        assertParses("""
        ---- MODULE Test ----
        Simple == <<Next>>_x
        Tuple == <<Next>>_<<x, y>>
        ====
        """)
    }

    func testTemporalFairness() {
        assertParses("""
        ---- MODULE Test ----
        Weak == WF_x(A)
        Strong == SF_x(A)
        WeakTuple == WF_<<x, y>>(A)
        StrongTuple == SF_<<x, y>>(A)
        ====
        """)
    }

    // MARK: - Operator Definitions

    func testOperatorDefinitionVariants() {
        assertParses("""
        ---- MODULE Test ----
        NoParams == 42
        OneParam(x) == x + 1
        TwoParams(x, y) == x + y
        HigherOrder(F(_)) == F(5)
        HigherOrderBinary(G(_, _)) == G(1, 2)
        ====
        """)
    }

    func testRecursiveOperator() {
        assertParses("""
        ---- MODULE Test ----
        RECURSIVE Fact(_)
        Fact(n) == IF n = 0 THEN 1 ELSE n * Fact(n - 1)
        ====
        """)
    }

    // MARK: - Proofs

    func testProofVariants() {
        assertParses("""
        ---- MODULE Test ----
        THEOREM T1 == 1 + 1 = 2 PROOF OBVIOUS
        THEOREM T2 == TRUE PROOF OMITTED
        THEOREM T3 == TRUE BY DEF Init
        ====
        """)
    }

    // MARK: - Instance

    func testInstanceVariants() {
        assertParses("""
        ---- MODULE Test ----
        INSTANCE Other
        INSTANCE Other WITH x <- y
        M == INSTANCE Other WITH a <- b, c <- d
        ====
        """)
    }

    // MARK: - Unicode Operators

    func testUnicodeLogical() {
        assertParses("""
        ---- MODULE Test ----
        And == a \u{2227} b
        Or == a \u{2228} b
        Not == \u{00AC}a
        ====
        """)
    }

    func testUnicodeQuantifiers() {
        assertParses("""
        ---- MODULE Test ----
        Forall == \u{2200} x \u{2208} S : P(x)
        Exists == \u{2203} x \u{2208} S : P(x)
        ====
        """)
    }

    func testUnicodeComparison() {
        assertParses("""
        ---- MODULE Test ----
        Le == a \u{2264} b
        Ge == a \u{2265} b
        Neq == a \u{2260} b
        ====
        """)
    }

    func testUnicodeSet() {
        assertParses("""
        ---- MODULE Test ----
        ElementOf == a \u{2208} S
        NotElementOf == a \u{2209} S
        Subset == A \u{2286} B
        Union == A \u{222A} B
        Intersect == A \u{2229} B
        ====
        """)
    }

    func testUnicodeTemporal() {
        assertParses("""
        ---- MODULE Test ----
        Always == \u{25A1}P
        Eventually == \u{25C7}P
        ====
        """)
    }

    // MARK: - Operator Precedence

    func testPrecedenceArithmetic() {
        // * has higher precedence than +
        let result = parse("""
        ---- MODULE Test ----
        Test == 1 + 2 * 3
        ====
        """)

        if case .success(let module) = result,
           case .operatorDef(let def) = module.declarations.first,
           case .binary(_, let op, _, _) = def.body {
            XCTAssertEqual(op, .plus, "Expected + as outer operator (2 * 3 binds tighter)")
        } else {
            XCTFail("Unexpected parse result")
        }
    }

    func testPrecedenceLogical() {
        // /\ has higher precedence than \/
        let result = parse("""
        ---- MODULE Test ----
        Test == a \\/ b /\\ c
        ====
        """)

        if case .success(let module) = result,
           case .operatorDef(let def) = module.declarations.first,
           case .binary(_, let op, _, _) = def.body {
            XCTAssertEqual(op, .or, "Expected \\/ as outer operator (b /\\ c binds tighter)")
        } else {
            XCTFail("Unexpected parse result")
        }
    }

    func testPrecedenceComparison() {
        // Comparison < has lower precedence than +
        let result = parse("""
        ---- MODULE Test ----
        Test == a + b < c
        ====
        """)

        if case .success(let module) = result,
           case .operatorDef(let def) = module.declarations.first,
           case .binary(_, let op, _, _) = def.body {
            XCTAssertEqual(op, .lt, "Expected < as outer operator (a + b binds tighter)")
        } else {
            XCTFail("Unexpected parse result")
        }
    }

    // MARK: - Complex Expressions

    func testComplexNestedExpression() {
        assertParses("""
        ---- MODULE Test ----
        Complex == \\A x \\in {y \\in S : y > 0} :
                       \\E z \\in T :
                           x + z < LET max == 100 IN max
        ====
        """)
    }

    func testComplexFunctionExpression() {
        assertParses("""
        ---- MODULE Test ----
        ComplexFunc == [x \\in 1..10 |->
                           [y \\in 1..x |->
                               IF y = x THEN 1 ELSE x * y]]
        ====
        """)
    }

    // MARK: - Error Cases

    func testMissingModuleEnd() {
        assertParseError("""
        ---- MODULE Test ----
        Test == 1
        """)
    }

    func testMissingModuleName() {
        assertParseError("""
        ---- MODULE ----
        ====
        """)
    }

    func testIncompleteOperatorDefinition() {
        assertParseError("""
        ---- MODULE Test ----
        Test ==
        ====
        """)
    }

    func testUnbalancedParentheses() {
        assertParseError("""
        ---- MODULE Test ----
        Test == (1 + 2
        ====
        """)
    }

    func testUnbalancedBrackets() {
        assertParseError("""
        ---- MODULE Test ----
        Test == {1, 2, 3
        ====
        """)
    }

    func testInvalidOperator() {
        assertParseError("""
        ---- MODULE Test ----
        Test == a @@@ b
        ====
        """)
    }
}
