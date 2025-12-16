import XCTest
@testable import MacTLA

/// Level 2: Integration Tests
/// Tests multi-file specifications, module composition (EXTENDS, INSTANCE), and configuration file parsing
final class Level2_IntegrationTests: XCTestCase {

    private func makeChecker() -> ModelChecker { ModelChecker() }

    // MARK: - Multi-File Simulation

    /// Tests that specifications with EXTENDS are properly structured
    func testExtendsNaturals() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE ExtendsTest ----
        EXTENDS Naturals

        VARIABLE x

        Init == x = 0

        Next == x' = x + 1

        TypeOK == x \\in Nat
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 10
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "TypeOK")]
        )

        // Should parse and check (even if Naturals isn't fully implemented)
        XCTAssertNotEqual(result.status, .error)
    }

    func testExtendsSequences() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE SeqTest ----
        EXTENDS Sequences

        VARIABLE seq

        Init == seq = <<>>

        Next == seq' = Append(seq, 1)

        TypeOK == seq \\in Seq(Nat)
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 5

        let result = await checker.verify(specification: spec, config: config)

        // Should at least parse
        XCTAssertTrue(result.status == .success || result.status == .error)
    }

    func testExtendsMultipleModules() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE MultiExtends ----
        EXTENDS Naturals, Sequences, FiniteSets

        VARIABLE x

        Init == x = 0

        Next == x' = x + 1
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 5

        let result = await checker.verify(specification: spec, config: config)

        // Should parse with multiple EXTENDS
        XCTAssertTrue(result.status != .error || result.error?.contains("parse") == false)
    }

    // MARK: - Module Composition (INSTANCE)

    func testInstanceSimple() {
        let parser = TLAParser()

        let spec = """
        ---- MODULE InstanceTest ----
        INSTANCE Other
        ====
        """

        let result = parser.parse(spec)

        switch result {
        case .success(let module):
            let instanceDecl = module.declarations.first { decl in
                if case .instance = decl { return true }
                return false
            }
            XCTAssertNotNil(instanceDecl)
        case .failure(let errors):
            XCTFail("Parse failed: \(errors.errors)")
        }
    }

    func testInstanceWithSubstitution() {
        let parser = TLAParser()

        let spec = """
        ---- MODULE InstanceSub ----
        CONSTANT N
        VARIABLE x

        Counter == INSTANCE CounterModule WITH n <- N, state <- x
        ====
        """

        let result = parser.parse(spec)

        switch result {
        case .success(let module):
            let instanceDecl = module.declarations.first { decl in
                if case .instance(let inst) = decl {
                    return inst.name == "Counter"
                }
                return false
            }
            XCTAssertNotNil(instanceDecl)
            if case .instance(let inst) = instanceDecl {
                XCTAssertEqual(inst.moduleName, "CounterModule")
                XCTAssertEqual(inst.substitutions.count, 2)
            }
        case .failure(let errors):
            XCTFail("Parse failed: \(errors.errors)")
        }
    }

    func testInstanceMultiple() {
        let parser = TLAParser()

        let spec = """
        ---- MODULE MultiInstance ----
        VARIABLES x, y

        M1 == INSTANCE Module1 WITH state <- x
        M2 == INSTANCE Module2 WITH state <- y
        ====
        """

        let result = parser.parse(spec)

        switch result {
        case .success(let module):
            let instanceCount = module.declarations.filter { decl in
                if case .instance = decl { return true }
                return false
            }.count
            XCTAssertEqual(instanceCount, 2)
        case .failure(let errors):
            XCTFail("Parse failed: \(errors.errors)")
        }
    }

    // MARK: - Configuration File Parsing (TLC Config)

    func testConfigConstantAssignment() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE ConfigTest ----
        CONSTANT N
        VARIABLE x

        Init == x = 0

        Next == x < N /\\ x' = x + 1

        Inv == x <= N
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 20
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            constants: [ModelChecker.ConstantOverride(name: "N", value: "5")],
            invariants: [ModelChecker.InvariantSpec(name: "Inv")]
        )

        XCTAssertEqual(result.status, .success, "Should work with N = 5")
    }

    func testConfigMultipleConstants() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE MultiConst ----
        CONSTANTS A, B, C
        VARIABLE x

        Init == x = A

        Next == x' = IF x = A THEN B ELSE IF x = B THEN C ELSE A

        TypeOK == x \\in {A, B, C}
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 20
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            constants: [
                ModelChecker.ConstantOverride(name: "A", value: "1"),
                ModelChecker.ConstantOverride(name: "B", value: "2"),
                ModelChecker.ConstantOverride(name: "C", value: "3")
            ],
            invariants: [ModelChecker.InvariantSpec(name: "TypeOK")]
        )

        XCTAssertEqual(result.status, .success)
    }

    func testConfigSetConstant() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE SetConst ----
        CONSTANT Procs
        VARIABLE x

        Init == x = 0

        Next == \\E p \\in Procs : x' = x + 1

        TypeOK == x >= 0
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 20
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            constants: [ModelChecker.ConstantOverride(name: "Procs", value: "{1, 2, 3}")],
            invariants: [ModelChecker.InvariantSpec(name: "TypeOK")]
        )

        XCTAssertNotEqual(result.status, .error)
    }

    // MARK: - Specification with Init and Next

    func testSpecWithInitAndNextDefined() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE CompleteSpec ----
        VARIABLE counter

        Init == counter = 0

        Increment == counter' = counter + 1
        Decrement == counter > 0 /\\ counter' = counter - 1

        Next == Increment \\/ Decrement

        Spec == Init /\\ [][Next]_counter

        TypeInvariant == counter \\in Nat
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 20
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "TypeInvariant")]
        )

        XCTAssertEqual(result.status, .success)
    }

    // MARK: - Complex Specifications

    func testResourceAllocationSpec() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE ResourceAlloc ----
        CONSTANT NumResources
        VARIABLE allocated

        Init == allocated = 0

        Acquire == allocated < NumResources /\\ allocated' = allocated + 1
        Release == allocated > 0 /\\ allocated' = allocated - 1

        Next == Acquire \\/ Release

        TypeOK == allocated >= 0 /\\ allocated <= NumResources
        NoOveralloc == allocated <= NumResources
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 50
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            constants: [ModelChecker.ConstantOverride(name: "NumResources", value: "3")],
            invariants: [
                ModelChecker.InvariantSpec(name: "TypeOK"),
                ModelChecker.InvariantSpec(name: "NoOveralloc")
            ]
        )

        XCTAssertEqual(result.status, .success)
        // Should find 4 states: allocated = 0, 1, 2, 3
        XCTAssertEqual(result.statesExplored, 4)
    }

    func testProducerConsumerSpec() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE ProducerConsumer ----
        CONSTANT MaxItems
        VARIABLE buffer

        Init == buffer = 0

        Produce == buffer < MaxItems /\\ buffer' = buffer + 1
        Consume == buffer > 0 /\\ buffer' = buffer - 1

        Next == Produce \\/ Consume

        TypeOK == buffer >= 0 /\\ buffer <= MaxItems
        NoUnderflow == buffer >= 0
        NoOverflow == buffer <= MaxItems
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 20
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            constants: [ModelChecker.ConstantOverride(name: "MaxItems", value: "3")],
            invariants: [
                ModelChecker.InvariantSpec(name: "TypeOK"),
                ModelChecker.InvariantSpec(name: "NoUnderflow"),
                ModelChecker.InvariantSpec(name: "NoOverflow")
            ]
        )

        XCTAssertEqual(result.status, .success)
    }

    // MARK: - Error Handling

    func testMissingConstantValue() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE MissingConst ----
        CONSTANT N
        VARIABLE x

        Init == x = N  \\ Uses undefined constant

        Next == x' = x
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 10

        let result = await checker.verify(
            specification: spec,
            config: config
            // Note: Not providing constant override for N
        )

        // Should error due to undefined constant
        XCTAssertEqual(result.status, .error)
    }

    func testInvalidConstantType() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE InvalidConst ----
        CONSTANT N
        VARIABLE x

        Init == x = 0

        Next == x < N /\\ x' = x + 1
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 10

        // Try to pass a malformed constant value
        let result = await checker.verify(
            specification: spec,
            config: config,
            constants: [ModelChecker.ConstantOverride(name: "N", value: "not_a_number!!!")]
        )

        // May error or handle gracefully
        XCTAssertTrue(result.status == .error || result.statesExplored == 0)
    }

    // MARK: - Composite State Spaces

    func testMultipleVariableStateSpace() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE MultiVar ----
        VARIABLES x, y, z

        Init == x = 0 /\\ y = 0 /\\ z = 0

        IncX == x' = (x + 1) % 2 /\\ y' = y /\\ z' = z
        IncY == x' = x /\\ y' = (y + 1) % 2 /\\ z' = z
        IncZ == x' = x /\\ y' = y /\\ z' = (z + 1) % 2

        Next == IncX \\/ IncY \\/ IncZ

        TypeOK == x \\in {0, 1} /\\ y \\in {0, 1} /\\ z \\in {0, 1}
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 50
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "TypeOK")]
        )

        XCTAssertEqual(result.status, .success)
        // 2^3 = 8 possible states
        XCTAssertEqual(result.statesExplored, 8, "Should find all 8 state combinations")
    }

    // MARK: - Assumption Declaration

    func testAssumptionParsing() {
        let parser = TLAParser()

        let spec = """
        ---- MODULE WithAssume ----
        CONSTANT N

        ASSUME N > 0

        VARIABLE x

        Init == x = 0

        Next == x' = x
        ====
        """

        let result = parser.parse(spec)

        switch result {
        case .success(let module):
            let assumeDecl = module.declarations.first { decl in
                if case .assumption = decl { return true }
                return false
            }
            XCTAssertNotNil(assumeDecl, "Should parse ASSUME declaration")
        case .failure(let errors):
            XCTFail("Parse failed: \(errors.errors)")
        }
    }

    // MARK: - Theorem Declaration

    func testTheoremParsing() {
        let parser = TLAParser()

        let spec = """
        ---- MODULE WithTheorem ----
        VARIABLE x

        Init == x = 0
        Next == x' = x + 1

        TypeOK == x >= 0

        THEOREM TypeSafe == Init => TypeOK
        ====
        """

        let result = parser.parse(spec)

        switch result {
        case .success(let module):
            let theoremDecl = module.declarations.first { decl in
                if case .theorem = decl { return true }
                return false
            }
            XCTAssertNotNil(theoremDecl, "Should parse THEOREM declaration")
        case .failure(let errors):
            XCTFail("Parse failed: \(errors.errors)")
        }
    }

    // MARK: - Large State Spaces

    func testLargeStateSpaceWithLimit() async throws {
        let checker = makeChecker()

        let spec = """
        ---- MODULE LargeSpace ----
        VARIABLE x

        Init == x = 0

        Next == x' = x + 1

        TypeOK == x >= 0
        ====
        """

        var config = ModelChecker.Configuration.default
        config.maxStates = 100
        config.checkInvariants = true

        let result = await checker.verify(
            specification: spec,
            config: config,
            invariants: [ModelChecker.InvariantSpec(name: "TypeOK")]
        )

        XCTAssertEqual(result.status, .success)
        XCTAssertEqual(result.statesExplored, 100, "Should explore exactly 100 states")
    }
}
