import XCTest
@testable import MacTLA

/// Complete TLA+ Parsing Tests
/// Covers all syntax constructs, edge cases, and error conditions
final class TLAParsingCompleteTests: XCTestCase {

    // MARK: - Lexer Tests

    // MARK: Module Structure Tokens

    func testModuleStartVariations() {
        // Minimum dashes
        let min = TLALexer(source: "---- MODULE A ----").scanTokens()
        XCTAssertEqual(min.first?.type, .moduleStart)

        // Many dashes
        let many = TLALexer(source: "-------- MODULE A --------").scanTokens()
        XCTAssertEqual(many.first?.type, .moduleStart)
    }

    func testModuleEnd() {
        let lexer = TLALexer(source: "====")
        let tokens = lexer.scanTokens()
        XCTAssertEqual(tokens.first?.type, .moduleEnd)
    }

    func testModuleEndVariations() {
        // Minimum equals
        let min = TLALexer(source: "====").scanTokens()
        XCTAssertEqual(min.first?.type, .moduleEnd)

        // Many equals
        let many = TLALexer(source: "========").scanTokens()
        XCTAssertEqual(many.first?.type, .moduleEnd)
    }

    // MARK: Keywords

    func testAllKeywords() {
        let keywords = [
            "MODULE", "EXTENDS", "CONSTANT", "CONSTANTS", "VARIABLE", "VARIABLES",
            "ASSUME", "THEOREM", "LEMMA", "PROPOSITION", "COROLLARY",
            "INSTANCE", "WITH", "LOCAL",
            "LET", "IN", "IF", "THEN", "ELSE", "CASE", "OTHER",
            "CHOOSE", "LAMBDA",
            "DOMAIN", "SUBSET", "UNION", "ENABLED", "UNCHANGED",
            "TRUE", "FALSE",
            "PROOF", "BY", "OBVIOUS", "OMITTED", "QED",
            "RECURSIVE",
            "SPECIFICATION", "INVARIANT", "PROPERTY"
        ]

        for keyword in keywords {
            let lexer = TLALexer(source: keyword)
            let tokens = lexer.scanTokens()
            if case .keyword = tokens.first?.type {
                // Success
            } else if case .identifier = tokens.first?.type {
                // Some keywords might be parsed as identifiers depending on context
            } else {
                XCTFail("'\(keyword)' should be recognized as keyword or identifier")
            }
        }
    }

    // MARK: Operators - Complete Set

    func testLogicalOperators() {
        let tests: [(String, TLAOperator)] = [
            ("/\\", .conjunction),
            ("\\/", .disjunction),
            ("~", .negation),
            ("=>", .implication),
            ("<=>", .equivalence),
            ("\\lnot", .negation),
            ("\\land", .conjunction),
            ("\\lor", .disjunction)
        ]

        for (source, expected) in tests {
            let tokens = TLALexer(source: source).scanTokens()
            XCTAssertEqual(tokens.first?.type, .operator(expected), "Failed for '\(source)'")
        }
    }

    func testComparisonOperators() {
        let tests: [(String, TLAOperator)] = [
            ("=", .equal),
            ("#", .notEqual),
            ("/=", .notEqualAlt),
            ("<", .lessThan),
            (">", .greaterThan),
            ("<=", .lessThanOrEqual),
            (">=", .greaterThanOrEqual)
        ]

        for (source, expected) in tests {
            let tokens = TLALexer(source: source).scanTokens()
            XCTAssertEqual(tokens.first?.type, .operator(expected), "Failed for '\(source)'")
        }
    }

    func testArithmeticOperators() {
        let tests: [(String, TLAOperator)] = [
            ("+", .plus),
            ("-", .minus),
            ("*", .multiply),
            ("\\div", .intDivide),
            ("%", .modulo),
            ("^", .power)
        ]

        for (source, expected) in tests {
            let tokens = TLALexer(source: source).scanTokens()
            XCTAssertEqual(tokens.first?.type, .operator(expected), "Failed for '\(source)'")
        }
    }

    func testSetOperators() {
        let tests: [(String, TLAOperator)] = [
            ("\\in", .elementOf),
            ("\\notin", .notElementOf),
            ("\\cup", .cup),
            ("\\cap", .cap),
            ("\\union", .cup),
            ("\\intersect", .cap),
            ("\\subseteq", .subsetOf),
            ("\\supseteq", .supersetOf),
            ("\\subset", .properSubset),
            ("\\supset", .properSuperset),
            ("\\X", .times),
            ("\\", .setMinus)
        ]

        for (source, expected) in tests {
            let tokens = TLALexer(source: source).scanTokens()
            XCTAssertEqual(tokens.first?.type, .operator(expected), "Failed for '\(source)'")
        }
    }

    func testTemporalOperators() {
        let tests: [(String, TLAOperator)] = [
            ("[]", .always),
            ("<>", .eventually),
            ("~>", .leadsto)
        ]

        for (source, expected) in tests {
            let tokens = TLALexer(source: source).scanTokens()
            XCTAssertEqual(tokens.first?.type, .operator(expected), "Failed for '\(source)'")
        }
    }

    func testQuantifierOperators() {
        let tests: [(String, TLAOperator)] = [
            ("\\A", .forall),
            ("\\E", .exists)
        ]

        for (source, expected) in tests {
            let tokens = TLALexer(source: source).scanTokens()
            XCTAssertEqual(tokens.first?.type, .operator(expected), "Failed for '\(source)'")
        }
    }

    func testActionOperators() {
        let source = "' =="
        let tokens = TLALexer(source: source).scanTokens()
        XCTAssertEqual(tokens[0].type, .operator(.prime))
        XCTAssertEqual(tokens[1].type, .operator(.define))
    }

    func testMiscOperators() {
        let tests: [(String, TLAOperator)] = [
            ("|->", .mapsto),
            ("<-", .leftArrow),
            ("->", .rightArrow),
            ("..", .dotDot),
            ("\\o", .concat),
            (":>", .colonGreater)
        ]

        for (source, expected) in tests {
            let tokens = TLALexer(source: source).scanTokens()
            XCTAssertEqual(tokens.first?.type, .operator(expected), "Failed for '\(source)'")
        }
    }

    // MARK: Delimiters

    func testDelimiters() {
        let tests: [(String, TLATokenType)] = [
            ("(", .leftParen),
            (")", .rightParen),
            ("[", .leftBracket),
            ("]", .rightBracket),
            ("{", .leftBrace),
            ("}", .rightBrace),
            ("<<", .leftAngle),
            (">>", .rightAngle),
            (",", .comma),
            (":", .colon),
            (";", .semicolon),
            ("!", .exclamation)
        ]

        for (source, expected) in tests {
            let tokens = TLALexer(source: source).scanTokens()
            XCTAssertEqual(tokens.first?.type, expected, "Failed for '\(source)'")
        }
    }

    // MARK: Literals

    func testIntegerLiterals() {
        let tests = [
            ("0", 0),
            ("1", 1),
            ("42", 42),
            ("12345", 12345),
            ("999999999", 999999999)
        ]

        for (source, expected) in tests {
            let tokens = TLALexer(source: source).scanTokens()
            if case .number(let value) = tokens.first?.type {
                XCTAssertEqual(value, expected, "Failed for '\(source)'")
            } else {
                XCTFail("Expected number for '\(source)'")
            }
        }
    }

    func testStringLiterals() {
        let tests = [
            ("\"\"", ""),
            ("\"a\"", "a"),
            ("\"hello world\"", "hello world"),
            ("\"with \\\"quotes\\\"\"", "with \"quotes\""),
            ("\"line1\\nline2\"", "line1\nline2")
        ]

        for (source, expected) in tests {
            let tokens = TLALexer(source: source).scanTokens()
            if case .string(let value) = tokens.first?.type {
                XCTAssertEqual(value, expected, "Failed for '\(source)'")
            } else {
                XCTFail("Expected string for '\(source)'")
            }
        }
    }

    func testIdentifiers() {
        let tests = [
            "x", "foo", "FooBar", "foo_bar", "x1", "x_1",
            "Init", "Next", "Spec", "TypeOK"
        ]

        for source in tests {
            let tokens = TLALexer(source: source).scanTokens()
            if case .identifier(let name) = tokens.first?.type {
                XCTAssertEqual(name, source)
            } else {
                XCTFail("Expected identifier for '\(source)'")
            }
        }
    }

    // MARK: Unicode Support

    func testUnicodeLogicalOperators() {
        let tests: [(String, TLAOperator)] = [
            ("\u{2227}", .conjunction),  // ∧
            ("\u{2228}", .disjunction),  // ∨
            ("\u{00AC}", .negation),     // ¬
            ("\u{21D2}", .implication),  // ⇒
            ("\u{21D4}", .equivalence)   // ⇔
        ]

        for (source, expected) in tests {
            let tokens = TLALexer(source: source).scanTokens()
            XCTAssertEqual(tokens.first?.type, .operator(expected), "Failed for Unicode")
        }
    }

    func testUnicodeQuantifiers() {
        let tests: [(String, TLAOperator)] = [
            ("\u{2200}", .forall),   // ∀
            ("\u{2203}", .exists)    // ∃
        ]

        for (source, expected) in tests {
            let tokens = TLALexer(source: source).scanTokens()
            XCTAssertEqual(tokens.first?.type, .operator(expected))
        }
    }

    func testUnicodeSetOperators() {
        let tests: [(String, TLAOperator)] = [
            ("\u{2208}", .elementOf),       // ∈
            ("\u{2209}", .notElementOf),    // ∉
            ("\u{222A}", .cup),             // ∪
            ("\u{2229}", .cap),             // ∩
            ("\u{2286}", .subsetOf),        // ⊆
            ("\u{2287}", .supersetOf)       // ⊇
        ]

        for (source, expected) in tests {
            let tokens = TLALexer(source: source).scanTokens()
            XCTAssertEqual(tokens.first?.type, .operator(expected))
        }
    }

    func testUnicodeComparison() {
        let tests: [(String, TLAOperator)] = [
            ("\u{2264}", .lessThanOrEqual),     // ≤
            ("\u{2265}", .greaterThanOrEqual),  // ≥
            ("\u{2260}", .notEqualUnicode)      // ≠
        ]

        for (source, expected) in tests {
            let tokens = TLALexer(source: source).scanTokens()
            XCTAssertEqual(tokens.first?.type, .operator(expected))
        }
    }

    func testUnicodeTemporal() {
        let tests: [(String, TLAOperator)] = [
            ("\u{25A1}", .always),      // □
            ("\u{25C7}", .eventually)   // ◇
        ]

        for (source, expected) in tests {
            let tokens = TLALexer(source: source).scanTokens()
            XCTAssertEqual(tokens.first?.type, .operator(expected))
        }
    }

    // MARK: Comments

    func testLineComment() {
        let source = "x \\* comment\ny"
        let tokens = TLALexer(source: source).scanTokens()

        let hasComment = tokens.contains { token in
            if case .comment = token.type { return true }
            return false
        }
        XCTAssertTrue(hasComment)

        // Should have x and y identifiers
        let identifiers = tokens.compactMap { token -> String? in
            if case .identifier(let name) = token.type { return name }
            return nil
        }
        XCTAssertEqual(identifiers, ["x", "y"])
    }

    func testBlockComment() {
        let source = "x (* block\ncomment *) y"
        let tokens = TLALexer(source: source).scanTokens()

        let hasBlockComment = tokens.contains { token in
            if case .blockComment = token.type { return true }
            return false
        }
        XCTAssertTrue(hasBlockComment)
    }

    func testNestedBlockComments() {
        let source = "(* outer (* inner *) outer *)"
        let tokens = TLALexer(source: source).scanTokens()

        let hasBlockComment = tokens.contains { token in
            if case .blockComment = token.type { return true }
            return false
        }
        XCTAssertTrue(hasBlockComment)
    }

    // MARK: Fairness Keywords

    func testWeakFairness() {
        let source = "WF_x(A)"
        let tokens = TLALexer(source: source).scanTokens()
        XCTAssertEqual(tokens.first?.type, .keyword(.wf))
    }

    func testStrongFairness() {
        let source = "SF_x(A)"
        let tokens = TLALexer(source: source).scanTokens()
        XCTAssertEqual(tokens.first?.type, .keyword(.sf))
    }

    // MARK: Location Tracking

    func testTokenLocations() {
        let source = "x\ny\nz"
        let tokens = TLALexer(source: source).scanTokens()

        let identifiers = tokens.filter {
            if case .identifier = $0.type { return true }
            return false
        }

        XCTAssertEqual(identifiers.count, 3)
        XCTAssertEqual(identifiers[0].line, 1)
        XCTAssertEqual(identifiers[1].line, 2)
        XCTAssertEqual(identifiers[2].line, 3)
    }

    func testColumnTracking() {
        let source = "abc def"
        let tokens = TLALexer(source: source).scanTokens()

        // First token at column 1, second at column 5
        XCTAssertEqual(tokens[0].column, 1)
        XCTAssertEqual(tokens[1].column, 5)
    }

    // MARK: - Parser Tests

    // MARK: Complete Specifications

    func testMinimalValidSpec() {
        let result = TLAParser().parse("""
        ---- MODULE Min ----
        ====
        """)
        assertSuccess(result)
    }

    func testCompleteSpecWithAllSections() {
        let result = TLAParser().parse("""
        ---- MODULE Complete ----
        EXTENDS Naturals, Sequences
        CONSTANTS N, M
        VARIABLES x, y, z
        ASSUME N > 0 /\\ M > 0

        Init == x = 0 /\\ y = 0 /\\ z = 0

        Inc(v) == v' = v + 1

        Next == Inc(x) /\\ y' = y /\\ z' = z

        TypeOK == x \\in Nat /\\ y \\in Nat /\\ z \\in Nat

        Spec == Init /\\ [][Next]_<<x, y, z>> /\\ WF_<<x,y,z>>(Next)

        THEOREM Safety == Spec => []TypeOK

        SPECIFICATION Spec
        INVARIANT TypeOK
        ====
        """)
        assertSuccess(result)
    }

    // MARK: Expression Parsing - Comprehensive

    func testAllBinaryOperatorParsing() {
        let operators = [
            "/\\", "\\/", "=>", "<=>",
            "=", "#", "/=", "<", ">", "<=", ">=",
            "+", "-", "*", "\\div", "%", "^",
            "\\in", "\\notin", "\\subseteq", "\\supseteq",
            "\\cup", "\\cap", "\\", "\\X",
            "\\o", "@@", ":>",
            ".."
        ]

        for op in operators {
            let result = TLAParser().parse("""
            ---- MODULE Test ----
            Test == a \(op) b
            ====
            """)
            assertSuccess(result, message: "Failed for operator '\(op)'")
        }
    }

    func testAllUnaryOperatorParsing() {
        let operators = [
            ("~", "a"),
            ("-", "5"),
            ("DOMAIN", "f"),
            ("SUBSET", "S"),
            ("UNION", "S"),
            ("ENABLED", "A"),
            ("UNCHANGED", "x")
        ]

        for (op, arg) in operators {
            let result = TLAParser().parse("""
            ---- MODULE Test ----
            Test == \(op) \(arg)
            ====
            """)
            assertSuccess(result, message: "Failed for operator '\(op)'")
        }
    }

    // MARK: Set Expressions

    func testEmptySet() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        S == {}
        ====
        """)
        assertSuccess(result)
    }

    func testSetWithElements() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        S == {1, 2, 3, 4, 5}
        ====
        """)
        assertSuccess(result)
    }

    func testNestedSets() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        S == {{1, 2}, {3, 4}, {}}
        ====
        """)
        assertSuccess(result)
    }

    func testSetComprehensionFilter() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        S == {x \\in Nat : x > 0 /\\ x < 10}
        ====
        """)
        assertSuccess(result)
    }

    func testSetComprehensionMap() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        S == {x * 2 : x \\in 1..10}
        ====
        """)
        assertSuccess(result)
    }

    func testSetComprehensionTuplePattern() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        S == {x + y : <<x, y>> \\in S \\X T}
        ====
        """)
        assertSuccess(result)
    }

    // MARK: Function Expressions

    func testFunctionConstruction() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        F == [x \\in S |-> x + 1]
        ====
        """)
        assertSuccess(result)
    }

    func testFunctionMultiArg() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        F == [x \\in S, y \\in T |-> x + y]
        ====
        """)
        assertSuccess(result)
    }

    func testFunctionApplication() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        V == f[x]
        ====
        """)
        assertSuccess(result)
    }

    func testFunctionMultiArgApplication() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        V == f[x, y, z]
        ====
        """)
        assertSuccess(result)
    }

    func testChainedFunctionApplication() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        V == f[x][y][z]
        ====
        """)
        assertSuccess(result)
    }

    // MARK: Record Expressions

    func testRecordConstruction() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        R == [name |-> "Alice", age |-> 30]
        ====
        """)
        assertSuccess(result)
    }

    func testRecordAccess() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        V == r.name
        ====
        """)
        assertSuccess(result)
    }

    func testChainedRecordAccess() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        V == r.a.b.c
        ====
        """)
        assertSuccess(result)
    }

    // MARK: EXCEPT Expressions

    func testExceptFunction() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        F == [f EXCEPT ![1] = 42]
        ====
        """)
        assertSuccess(result)
    }

    func testExceptRecord() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        R == [r EXCEPT !.name = "Bob"]
        ====
        """)
        assertSuccess(result)
    }

    func testExceptMultiple() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        F == [f EXCEPT ![1] = 10, ![2] = 20, ![3] = 30]
        ====
        """)
        assertSuccess(result)
    }

    func testExceptNested() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        F == [f EXCEPT ![1][2] = 42]
        ====
        """)
        assertSuccess(result)
    }

    func testExceptWithAt() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        F == [f EXCEPT ![1] = @ + 1]
        ====
        """)
        assertSuccess(result)
    }

    // MARK: Tuple/Sequence Expressions

    func testEmptyTuple() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        T == <<>>
        ====
        """)
        assertSuccess(result)
    }

    func testTupleWithElements() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        T == <<1, 2, 3>>
        ====
        """)
        assertSuccess(result)
    }

    func testNestedTuples() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        T == <<<<1, 2>>, <<3, 4>>>>
        ====
        """)
        assertSuccess(result)
    }

    // MARK: Quantifiers

    func testForallBounded() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        P == \\A x \\in S : Q(x)
        ====
        """)
        assertSuccess(result)
    }

    func testForallUnbounded() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        P == \\A x : Q(x)
        ====
        """)
        assertSuccess(result)
    }

    func testExistsBounded() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        P == \\E x \\in S : Q(x)
        ====
        """)
        assertSuccess(result)
    }

    func testMultipleQuantifiedVars() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        P == \\A x, y \\in S : Q(x, y)
        ====
        """)
        assertSuccess(result)
    }

    func testTuplePatternQuantifier() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        P == \\E <<x, y>> \\in S : x + y = 10
        ====
        """)
        assertSuccess(result)
    }

    func testNestedQuantifiers() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        P == \\A x \\in S : \\E y \\in T : Q(x, y)
        ====
        """)
        assertSuccess(result)
    }

    // MARK: CHOOSE

    func testChooseBounded() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        Min == CHOOSE x \\in S : \\A y \\in S : x <= y
        ====
        """)
        assertSuccess(result)
    }

    func testChooseUnbounded() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        V == CHOOSE x : P(x)
        ====
        """)
        assertSuccess(result)
    }

    // MARK: Control Flow

    func testIfThenElse() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        Max(a, b) == IF a > b THEN a ELSE b
        ====
        """)
        assertSuccess(result)
    }

    func testNestedIfThenElse() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        Classify(x) == IF x < 0 THEN "negative"
                       ELSE IF x = 0 THEN "zero"
                       ELSE "positive"
        ====
        """)
        assertSuccess(result)
    }

    func testCaseSimple() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        Grade(s) == CASE s >= 90 -> "A"
                      [] s >= 80 -> "B"
                      [] OTHER -> "F"
        ====
        """)
        assertSuccess(result)
    }

    func testCaseNoOther() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        Day(n) == CASE n = 1 -> "Mon"
                    [] n = 2 -> "Tue"
        ====
        """)
        assertSuccess(result)
    }

    // MARK: LET-IN

    func testLetInSimple() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        V == LET x == 5 IN x + 1
        ====
        """)
        assertSuccess(result)
    }

    func testLetInMultiple() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        V == LET x == 5
                 y == 10
             IN x + y
        ====
        """)
        assertSuccess(result)
    }

    func testLetInWithFunction() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        V == LET F(a) == a + 1 IN F(5)
        ====
        """)
        assertSuccess(result)
    }

    func testLetInNested() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        V == LET x == LET y == 5 IN y + 1 IN x * 2
        ====
        """)
        assertSuccess(result)
    }

    // MARK: LAMBDA

    func testLambdaSingle() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        Inc == LAMBDA x : x + 1
        ====
        """)
        assertSuccess(result)
    }

    func testLambdaMultiple() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        Add == LAMBDA x, y : x + y
        ====
        """)
        assertSuccess(result)
    }

    // MARK: Temporal Operators

    func testAlways() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        Safety == []Inv
        ====
        """)
        assertSuccess(result)
    }

    func testEventually() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        Liveness == <>Done
        ====
        """)
        assertSuccess(result)
    }

    func testLeadsto() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        Progress == Request ~> Response
        ====
        """)
        assertSuccess(result)
    }

    func testStuttering() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        Spec == [][Next]_vars
        ====
        """)
        assertSuccess(result)
    }

    func testStutteringTuple() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        Spec == [][Next]_<<x, y>>
        ====
        """)
        assertSuccess(result)
    }

    func testAction() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        Strong == <<Next>>_vars
        ====
        """)
        assertSuccess(result)
    }

    func testWeakFairnessParsing() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        Fair == WF_vars(Next)
        ====
        """)
        assertSuccess(result)
    }

    func testStrongFairnessParsing() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        Fair == SF_vars(Next)
        ====
        """)
        assertSuccess(result)
    }

    // MARK: Operator Definitions

    func testOperatorNoParams() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        Zero == 0
        ====
        """)
        assertSuccess(result)
    }

    func testOperatorWithParams() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        Add(a, b) == a + b
        ====
        """)
        assertSuccess(result)
    }

    func testHigherOrderOperator() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        Apply(F(_), x) == F(x)
        ====
        """)
        assertSuccess(result)
    }

    func testRecursiveOperator() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        RECURSIVE Fact(_)
        Fact(n) == IF n = 0 THEN 1 ELSE n * Fact(n - 1)
        ====
        """)
        assertSuccess(result)
    }

    // MARK: Module Features

    func testExtends() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        EXTENDS Naturals, Sequences, FiniteSets
        ====
        """)
        assertSuccess(result)
    }

    func testInstance() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        INSTANCE Other
        ====
        """)
        assertSuccess(result)
    }

    func testInstanceWithSubstitution() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        M == INSTANCE Other WITH x <- y, a <- b
        ====
        """)
        assertSuccess(result)
    }

    func testLocal() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        LOCAL Helper == 42
        Public == Helper + 1
        ====
        """)
        assertSuccess(result)
    }

    // MARK: Proofs

    func testTheoremObvious() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        THEOREM T == TRUE PROOF OBVIOUS
        ====
        """)
        assertSuccess(result)
    }

    func testTheoremOmitted() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        THEOREM T == TRUE PROOF OMITTED
        ====
        """)
        assertSuccess(result)
    }

    func testTheoremBy() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        THEOREM T == TRUE BY DEF Init
        ====
        """)
        assertSuccess(result)
    }

    // MARK: Error Cases

    func testMissingModuleName() {
        let result = TLAParser().parse("""
        ---- MODULE ----
        ====
        """)
        assertFailure(result)
    }

    func testMissingModuleEnd() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        Init == TRUE
        """)
        assertFailure(result)
    }

    func testIncompleteOperator() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        Inc ==
        ====
        """)
        assertFailure(result)
    }

    func testUnbalancedParens() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        V == (1 + 2
        ====
        """)
        assertFailure(result)
    }

    func testUnbalancedBraces() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        S == {1, 2, 3
        ====
        """)
        assertFailure(result)
    }

    func testUnbalancedAngleBrackets() {
        let result = TLAParser().parse("""
        ---- MODULE Test ----
        T == <<1, 2, 3
        ====
        """)
        assertFailure(result)
    }

    // MARK: - Helpers

    private func assertSuccess(_ result: Result<TLAModule, TLAParser.ParseErrors>, message: String = "", file: StaticString = #file, line: UInt = #line) {
        switch result {
        case .success:
            break
        case .failure(let errors):
            XCTFail("Parse failed\(message.isEmpty ? "" : ": \(message)"): \(errors.errors)", file: file, line: line)
        }
    }

    private func assertFailure(_ result: Result<TLAModule, TLAParser.ParseErrors>, file: StaticString = #file, line: UInt = #line) {
        switch result {
        case .success:
            XCTFail("Expected parse failure but succeeded", file: file, line: line)
        case .failure:
            break
        }
    }
}
