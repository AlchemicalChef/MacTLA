import XCTest
@testable import MacTLA

final class TLALexerTests: XCTestCase {

    func testModuleHeader() {
        let source = "---- MODULE Test ----"
        let lexer = TLALexer(source: source)
        let tokens = lexer.scanTokens()

        XCTAssertEqual(tokens.count, 5) // moduleStart, MODULE, Test, moduleStart (trailing), eof
        XCTAssertEqual(tokens[0].type, .moduleStart)
        XCTAssertEqual(tokens[1].type, .keyword(.module))
        if case .identifier(let name) = tokens[2].type {
            XCTAssertEqual(name, "Test")
        } else {
            XCTFail("Expected identifier")
        }
        XCTAssertEqual(tokens[3].type, .moduleStart) // Trailing ----
        XCTAssertEqual(tokens[4].type, .eof)
    }

    func testOperators() {
        let source = "/\\ \\/ => \\in \\A \\E"
        let lexer = TLALexer(source: source)
        let tokens = lexer.scanTokens()

        XCTAssertEqual(tokens[0].type, .operator(.conjunction))
        XCTAssertEqual(tokens[1].type, .operator(.disjunction))
        XCTAssertEqual(tokens[2].type, .operator(.implication))
        XCTAssertEqual(tokens[3].type, .operator(.elementOf))
        XCTAssertEqual(tokens[4].type, .operator(.forall))
        XCTAssertEqual(tokens[5].type, .operator(.exists))
    }

    func testNumbersAndIdentifiers() {
        let source = "x 42 foo_bar TRUE FALSE"
        let lexer = TLALexer(source: source)
        let tokens = lexer.scanTokens()

        if case .identifier(let name) = tokens[0].type {
            XCTAssertEqual(name, "x")
        } else {
            XCTFail("Expected identifier")
        }

        if case .number(let value) = tokens[1].type {
            XCTAssertEqual(value, 42)
        } else {
            XCTFail("Expected number")
        }
    }

    func testComments() {
        let source = """
        x == 1 \\* This is a comment
        y == 2
        """
        let lexer = TLALexer(source: source)
        let tokens = lexer.scanTokens()

        // Should contain comment token
        let hasComment = tokens.contains { token in
            if case .comment = token.type { return true }
            return false
        }
        XCTAssertTrue(hasComment)
    }

    func testBlockComments() {
        let source = """
        (* This is a
           block comment *)
        x == 1
        """
        let lexer = TLALexer(source: source)
        let tokens = lexer.scanTokens()

        let hasBlockComment = tokens.contains { token in
            if case .blockComment = token.type { return true }
            return false
        }
        XCTAssertTrue(hasBlockComment)
    }

    func testStringLiterals() {
        let source = "\"hello world\""
        let lexer = TLALexer(source: source)
        let tokens = lexer.scanTokens()

        if case .string(let value) = tokens[0].type {
            XCTAssertEqual(value, "hello world")
        } else {
            XCTFail("Expected string")
        }
    }

    func testTemporalOperators() {
        let source = "[] <> ~>"
        let lexer = TLALexer(source: source)
        let tokens = lexer.scanTokens()

        XCTAssertEqual(tokens[0].type, .operator(.always))
        XCTAssertEqual(tokens[1].type, .operator(.eventually))
        XCTAssertEqual(tokens[2].type, .operator(.leadsto))
    }

    func testSetOperators() {
        let source = "\\cup \\cap \\subseteq \\X"
        let lexer = TLALexer(source: source)
        let tokens = lexer.scanTokens()

        XCTAssertEqual(tokens[0].type, .operator(.cup))
        XCTAssertEqual(tokens[1].type, .operator(.cap))
        XCTAssertEqual(tokens[2].type, .operator(.subsetOf))
        XCTAssertEqual(tokens[3].type, .operator(.times))
    }

    func testLineAndColumnTracking() {
        let source = """
        x == 1
        y == 2
        """
        let lexer = TLALexer(source: source)
        let tokens = lexer.scanTokens()

        // First identifier should be on line 1
        XCTAssertEqual(tokens[0].line, 1)

        // Find 'y' identifier on line 2
        let yToken = tokens.first { token in
            if case .identifier(let name) = token.type {
                return name == "y"
            }
            return false
        }
        XCTAssertNotNil(yToken)
        XCTAssertEqual(yToken?.line, 2)
    }
}
