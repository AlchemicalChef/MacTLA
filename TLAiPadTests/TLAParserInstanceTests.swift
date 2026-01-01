import XCTest
@testable import MacTLA

/// Tests for INSTANCE WITH substitution syntax in TLAParser
final class TLAParserInstanceTests: XCTestCase {

    // MARK: - Helper Methods

    private func parse(_ source: String) -> Result<TLAModule, TLAParser.ParseErrors> {
        TLAParser().parse(source)
    }

    // MARK: - Simple Instance Tests

    func testInstanceSimple() throws {
        let source = """
        ---- MODULE Test ----
        INSTANCE Naturals
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            let instances = module.declarations.compactMap { decl -> InstanceDeclaration? in
                if case .instance(let inst) = decl { return inst }
                return nil
            }
            XCTAssertEqual(instances.count, 1)
            XCTAssertEqual(instances.first?.moduleName, "Naturals")
            XCTAssertNil(instances.first?.name)
            XCTAssertTrue(instances.first?.substitutions.isEmpty ?? false)
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }

    func testInstanceWithName() throws {
        let source = """
        ---- MODULE Test ----
        N == INSTANCE Naturals
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            let instances = module.declarations.compactMap { decl -> InstanceDeclaration? in
                if case .instance(let inst) = decl { return inst }
                return nil
            }
            XCTAssertEqual(instances.count, 1)
            XCTAssertEqual(instances.first?.moduleName, "Naturals")
            XCTAssertEqual(instances.first?.name, "N")
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }

    // MARK: - Substitution Tests

    func testInstanceWithSubstitution() throws {
        let source = """
        ---- MODULE Test ----
        CONSTANT MyConst
        INSTANCE Other WITH Const <- MyConst
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            let instances = module.declarations.compactMap { decl -> InstanceDeclaration? in
                if case .instance(let inst) = decl { return inst }
                return nil
            }
            XCTAssertEqual(instances.count, 1)
            if let inst = instances.first {
                XCTAssertEqual(inst.moduleName, "Other")
                XCTAssertEqual(inst.substitutions.count, 1)
                XCTAssertEqual(inst.substitutions.first?.parameter, "Const")
            }
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }

    func testInstanceWithMultipleSubstitutions() throws {
        let source = """
        ---- MODULE Test ----
        CONSTANT A, B, C
        INSTANCE Other WITH X <- A, Y <- B, Z <- C
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            let instances = module.declarations.compactMap { decl -> InstanceDeclaration? in
                if case .instance(let inst) = decl { return inst }
                return nil
            }
            XCTAssertEqual(instances.count, 1)
            if let inst = instances.first {
                XCTAssertEqual(inst.substitutions.count, 3)

                let params = Set(inst.substitutions.map { $0.parameter })
                XCTAssertTrue(params.contains("X"))
                XCTAssertTrue(params.contains("Y"))
                XCTAssertTrue(params.contains("Z"))
            }
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }

    func testInstanceSubstitutionUsesLeftArrow() throws {
        // Test that <- is correctly parsed (not = or other operators)
        let source = """
        ---- MODULE Test ----
        CONSTANT Val
        INSTANCE M WITH param <- Val
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            let instances = module.declarations.compactMap { decl -> InstanceDeclaration? in
                if case .instance(let inst) = decl { return inst }
                return nil
            }
            XCTAssertEqual(instances.first?.substitutions.count, 1)
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }

    // MARK: - Named Instance with Substitution

    func testNamedInstanceWithSubstitution() throws {
        let source = """
        ---- MODULE Test ----
        CONSTANT N
        I == INSTANCE Counter WITH max <- N
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            let instances = module.declarations.compactMap { decl -> InstanceDeclaration? in
                if case .instance(let inst) = decl { return inst }
                return nil
            }
            XCTAssertEqual(instances.count, 1)
            if let inst = instances.first {
                XCTAssertEqual(inst.name, "I")
                XCTAssertEqual(inst.moduleName, "Counter")
                XCTAssertEqual(inst.substitutions.count, 1)
            }
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }

    // MARK: - Complex Substitution Expression Tests

    func testInstanceSubstitutionWithExpression() throws {
        let source = """
        ---- MODULE Test ----
        CONSTANT N
        INSTANCE Other WITH max <- N + 1
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            let instances = module.declarations.compactMap { decl -> InstanceDeclaration? in
                if case .instance(let inst) = decl { return inst }
                return nil
            }
            XCTAssertEqual(instances.count, 1)
            if let inst = instances.first {
                XCTAssertEqual(inst.substitutions.count, 1)
                // The expression should be N + 1
                if case .binary(_, .plus, _, _) = inst.substitutions.first?.expression {
                    // Good - it's a binary plus expression
                } else {
                    XCTFail("Expected binary plus expression")
                }
            }
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }

    // MARK: - Multiple Instance Declarations

    func testMultipleInstances() throws {
        let source = """
        ---- MODULE Test ----
        INSTANCE Naturals
        INSTANCE Sequences
        INSTANCE FiniteSets
        ====
        """

        let result = parse(source)

        switch result {
        case .success(let module):
            let instances = module.declarations.compactMap { decl -> InstanceDeclaration? in
                if case .instance(let inst) = decl { return inst }
                return nil
            }
            XCTAssertEqual(instances.count, 3)

            let moduleNames = instances.map { $0.moduleName }
            XCTAssertTrue(moduleNames.contains("Naturals"))
            XCTAssertTrue(moduleNames.contains("Sequences"))
            XCTAssertTrue(moduleNames.contains("FiniteSets"))
        case .failure(let errors):
            XCTFail("Parse failed: \(errors)")
        }
    }
}
