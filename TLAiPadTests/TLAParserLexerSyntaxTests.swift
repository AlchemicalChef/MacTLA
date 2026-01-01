import XCTest
@testable import MacTLA

/// Tests for \forall/\exists and other syntax aliases in TLAParser and TLALexer
final class TLAParserLexerSyntaxTests: XCTestCase {

    // MARK: - Helper Methods

    private func parse(_ source: String) -> Result<TLAModule, TLAParser.ParseErrors> {
        TLAParser().parse(source)
    }

    private func lex(_ source: String) -> [TLAToken] {
        TLALexer().tokenize(source)
    }

    // MARK: - Quantifier Backslash Syntax Tests

    func testForallBackslashSyntax() throws {
        let source = """
        ---- MODULE Test ----
        Test == \\A x \\in {1, 2, 3}: x > 0
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            let opDefs = module.declarations.compactMap { decl -> OperatorDefinition? in
                if case .operatorDef(let op) = decl { return op }
                return nil
            }
            let testDef = opDefs.first { $0.name == "Test" }
            XCTAssertNotNil(testDef)

            // The body should be a forall expression
            if case .forall = testDef?.body {
                // Good
            } else {
                XCTFail("Expected forall expression")
            }
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }

    func testExistsBackslashSyntax() throws {
        let source = """
        ---- MODULE Test ----
        Test == \\E x \\in {1, 2, 3}: x = 2
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            let opDefs = module.declarations.compactMap { decl -> OperatorDefinition? in
                if case .operatorDef(let op) = decl { return op }
                return nil
            }
            let testDef = opDefs.first { $0.name == "Test" }
            XCTAssertNotNil(testDef)

            // The body should be an exists expression
            if case .exists = testDef?.body {
                // Good
            } else {
                XCTFail("Expected exists expression")
            }
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }

    // MARK: - Lexer Token Tests

    func testLexerTokenizesForall() {
        let tokens = lex("\\A")

        let forallTokens = tokens.filter {
            if case .forall = $0.type { return true }
            return false
        }
        XCTAssertEqual(forallTokens.count, 1)
    }

    func testLexerTokenizesExists() {
        let tokens = lex("\\E")

        let existsTokens = tokens.filter {
            if case .exists = $0.type { return true }
            return false
        }
        XCTAssertEqual(existsTokens.count, 1)
    }

    func testLexerTokenizesElementOf() {
        let tokens = lex("\\in")

        let inTokens = tokens.filter {
            if case .in_ = $0.type { return true }
            return false
        }
        XCTAssertEqual(inTokens.count, 1)
    }

    // MARK: - Temporal Operator Syntax Tests

    func testAlwaysSyntax() throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x
        Prop == []x
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            let opDefs = module.declarations.compactMap { decl -> OperatorDefinition? in
                if case .operatorDef(let op) = decl { return op }
                return nil
            }
            let propDef = opDefs.first { $0.name == "Prop" }
            XCTAssertNotNil(propDef)

            if case .always = propDef?.body {
                // Good
            } else {
                XCTFail("Expected always expression, got: \(String(describing: propDef?.body))")
            }
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }

    func testEventuallySyntax() throws {
        let source = """
        ---- MODULE Test ----
        VARIABLE x
        Prop == <>x
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            let opDefs = module.declarations.compactMap { decl -> OperatorDefinition? in
                if case .operatorDef(let op) = decl { return op }
                return nil
            }
            let propDef = opDefs.first { $0.name == "Prop" }
            XCTAssertNotNil(propDef)

            if case .eventually = propDef?.body {
                // Good
            } else {
                XCTFail("Expected eventually expression, got: \(String(describing: propDef?.body))")
            }
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }

    // MARK: - Logical Operator Syntax Tests

    func testConjunctionSyntax() throws {
        let source = """
        ---- MODULE Test ----
        Test == TRUE /\\ FALSE
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            let opDefs = module.declarations.compactMap { decl -> OperatorDefinition? in
                if case .operatorDef(let op) = decl { return op }
                return nil
            }
            let testDef = opDefs.first { $0.name == "Test" }
            XCTAssertNotNil(testDef)

            if case .binary(_, .and, _, _) = testDef?.body {
                // Good
            } else {
                XCTFail("Expected and expression")
            }
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }

    func testDisjunctionSyntax() throws {
        let source = """
        ---- MODULE Test ----
        Test == TRUE \\/ FALSE
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            let opDefs = module.declarations.compactMap { decl -> OperatorDefinition? in
                if case .operatorDef(let op) = decl { return op }
                return nil
            }
            let testDef = opDefs.first { $0.name == "Test" }
            XCTAssertNotNil(testDef)

            if case .binary(_, .or, _, _) = testDef?.body {
                // Good
            } else {
                XCTFail("Expected or expression")
            }
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }

    func testNegationSyntax() throws {
        let source = """
        ---- MODULE Test ----
        Test == ~TRUE
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            let opDefs = module.declarations.compactMap { decl -> OperatorDefinition? in
                if case .operatorDef(let op) = decl { return op }
                return nil
            }
            let testDef = opDefs.first { $0.name == "Test" }
            XCTAssertNotNil(testDef)

            if case .unary(.not, _, _) = testDef?.body {
                // Good
            } else {
                XCTFail("Expected not expression")
            }
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }

    // MARK: - Set Operator Syntax Tests

    func testSetUnionSyntax() throws {
        let source = """
        ---- MODULE Test ----
        Test == {1} \\cup {2}
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            let opDefs = module.declarations.compactMap { decl -> OperatorDefinition? in
                if case .operatorDef(let op) = decl { return op }
                return nil
            }
            let testDef = opDefs.first { $0.name == "Test" }
            XCTAssertNotNil(testDef)

            if case .binary(_, .setUnion, _, _) = testDef?.body {
                // Good
            } else {
                XCTFail("Expected union expression")
            }
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }

    func testSetIntersectionSyntax() throws {
        let source = """
        ---- MODULE Test ----
        Test == {1, 2} \\cap {2, 3}
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            let opDefs = module.declarations.compactMap { decl -> OperatorDefinition? in
                if case .operatorDef(let op) = decl { return op }
                return nil
            }
            let testDef = opDefs.first { $0.name == "Test" }
            XCTAssertNotNil(testDef)

            if case .binary(_, .setIntersect, _, _) = testDef?.body {
                // Good
            } else {
                XCTFail("Expected intersection expression")
            }
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }

    func testSubsetSyntax() throws {
        let source = """
        ---- MODULE Test ----
        Test == {1} \\subseteq {1, 2}
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            let opDefs = module.declarations.compactMap { decl -> OperatorDefinition? in
                if case .operatorDef(let op) = decl { return op }
                return nil
            }
            let testDef = opDefs.first { $0.name == "Test" }
            XCTAssertNotNil(testDef)

            if case .binary(_, .subsetOf, _, _) = testDef?.body {
                // Good
            } else {
                XCTFail("Expected subset expression")
            }
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }
}
