import XCTest
@testable import MacTLA

/// Tests for RECURSIVE forward declarations in TLAParser
final class TLAParserRecursiveTests: XCTestCase {

    // MARK: - Helper Methods

    private func parse(_ source: String) -> Result<TLAModule, TLAParser.ParseErrors> {
        TLAParser().parse(source)
    }

    // MARK: - Forward Declaration Tests

    func testRecursiveForwardDeclaration() throws {
        let source = """
        ---- MODULE Test ----
        RECURSIVE Fact(_)
        Fact(n) == IF n = 0 THEN 1 ELSE n * Fact(n - 1)
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            // Should have both RECURSIVE declaration and operator definition
            XCTAssertGreaterThanOrEqual(module.declarations.count, 2)
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }

    func testRecursiveForwardWithParameters() throws {
        let source = """
        ---- MODULE Test ----
        RECURSIVE Fib(_, _)
        Fib(a, b) == a + b
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            // Find the recursive declaration
            let recursiveDecls = module.declarations.compactMap { decl -> RecursiveDeclaration? in
                if case .recursiveDecl(let rd) = decl { return rd }
                return nil
            }
            XCTAssertFalse(recursiveDecls.isEmpty)
            if let first = recursiveDecls.first {
                XCTAssertEqual(first.name, "Fib")
                XCTAssertEqual(first.parameterCount, 2)
            }
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }

    func testRecursiveForwardWithUnderscores() throws {
        let source = """
        ---- MODULE Test ----
        RECURSIVE Op(_, _, _)
        Op(x, y, z) == x + y + z
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            let recursiveDecls = module.declarations.compactMap { decl -> RecursiveDeclaration? in
                if case .recursiveDecl(let rd) = decl { return rd }
                return nil
            }
            if let first = recursiveDecls.first {
                XCTAssertEqual(first.parameterCount, 3)
            }
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }

    // MARK: - Combined Declaration + Definition Tests

    func testRecursiveCombinedForm() throws {
        // Some TLA+ tools allow RECURSIVE and definition on same construct
        let source = """
        ---- MODULE Test ----
        RECURSIVE Sum(_)
        Sum(s) == IF s = {} THEN 0 ELSE LET x == CHOOSE e \\in s: TRUE IN x + Sum(s \\ {x})
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            XCTAssertGreaterThanOrEqual(module.declarations.count, 2)
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }

    // MARK: - Separate Declaration and Definition Tests

    func testRecursiveDeclarationThenDefinition() throws {
        let source = """
        ---- MODULE Test ----
        RECURSIVE Len(_)

        Len(s) == IF s = <<>> THEN 0 ELSE 1 + Len(Tail(s))
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            // Should parse successfully with blank line between
            XCTAssertGreaterThanOrEqual(module.declarations.count, 2)
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }

    func testRecursiveOperatorIsMarkedRecursive() throws {
        let source = """
        ---- MODULE Test ----
        RECURSIVE Fact(_)
        Fact(n) == IF n = 0 THEN 1 ELSE n * Fact(n - 1)
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            // Find the operator definition
            let opDefs = module.declarations.compactMap { decl -> OperatorDefinition? in
                if case .operatorDef(let op) = decl { return op }
                return nil
            }
            let factDef = opDefs.first { $0.name == "Fact" }
            XCTAssertNotNil(factDef)
            // The operator should be marked as recursive
            XCTAssertTrue(factDef?.isRecursive ?? false)
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }

    func testNonRecursiveOperatorNotMarked() throws {
        let source = """
        ---- MODULE Test ----
        Double(n) == n * 2
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            let opDefs = module.declarations.compactMap { decl -> OperatorDefinition? in
                if case .operatorDef(let op) = decl { return op }
                return nil
            }
            let doubleDef = opDefs.first { $0.name == "Double" }
            XCTAssertNotNil(doubleDef)
            XCTAssertFalse(doubleDef?.isRecursive ?? true)
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }

    // MARK: - Integration Tests

    func testRecursiveFactorialParsesCorrectly() throws {
        let source = """
        ---- MODULE Factorial ----
        EXTENDS Integers

        RECURSIVE Factorial(_)

        Factorial(n) == IF n <= 0
                        THEN 1
                        ELSE n * Factorial(n - 1)
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            XCTAssertEqual(module.name, "Factorial")

            // Should have RECURSIVE declaration and operator definition
            let recursiveDecls = module.declarations.compactMap { decl -> RecursiveDeclaration? in
                if case .recursiveDecl(let rd) = decl { return rd }
                return nil
            }
            XCTAssertEqual(recursiveDecls.count, 1)
            XCTAssertEqual(recursiveDecls.first?.name, "Factorial")
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }

    func testRecursiveFibonacciParsesCorrectly() throws {
        let source = """
        ---- MODULE Fibonacci ----
        EXTENDS Integers

        RECURSIVE Fib(_)

        Fib(n) == IF n <= 1
                  THEN n
                  ELSE Fib(n - 1) + Fib(n - 2)
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            XCTAssertEqual(module.name, "Fibonacci")

            let recursiveDecls = module.declarations.compactMap { decl -> RecursiveDeclaration? in
                if case .recursiveDecl(let rd) = decl { return rd }
                return nil
            }
            XCTAssertEqual(recursiveDecls.count, 1)
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }

    func testRecursiveMutualRecursion() throws {
        let source = """
        ---- MODULE MutualRecursion ----
        EXTENDS Integers

        RECURSIVE IsEven(_)
        RECURSIVE IsOdd(_)

        IsEven(n) == IF n = 0 THEN TRUE ELSE IsOdd(n - 1)
        IsOdd(n) == IF n = 0 THEN FALSE ELSE IsEven(n - 1)
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            let recursiveDecls = module.declarations.compactMap { decl -> RecursiveDeclaration? in
                if case .recursiveDecl(let rd) = decl { return rd }
                return nil
            }
            XCTAssertEqual(recursiveDecls.count, 2)

            let names = Set(recursiveDecls.map { $0.name })
            XCTAssertTrue(names.contains("IsEven"))
            XCTAssertTrue(names.contains("IsOdd"))
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }

    func testRecursiveWithLocalDef() throws {
        let source = """
        ---- MODULE Test ----
        RECURSIVE Sum(_)

        Sum(s) == IF s = {}
                  THEN 0
                  ELSE LET x == CHOOSE e \\in s: TRUE
                       IN x + Sum(s \\ {x})
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            // Should parse the LET IN expression inside recursive def
            let opDefs = module.declarations.compactMap { decl -> OperatorDefinition? in
                if case .operatorDef(let op) = decl { return op }
                return nil
            }
            let sumDef = opDefs.first { $0.name == "Sum" }
            XCTAssertNotNil(sumDef)
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }
}
