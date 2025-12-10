import Foundation

// MARK: - AST Nodes

protocol TLANode {
    var location: SourceLocation { get }
}

struct SourceLocation: Equatable {
    let line: Int
    let column: Int
    let length: Int

    static let unknown = SourceLocation(line: 0, column: 0, length: 0)
}

// Module
struct TLAModule: TLANode {
    let name: String
    let extends: [String]
    let declarations: [TLADeclaration]
    let location: SourceLocation
}

// Declarations
enum TLADeclaration: TLANode {
    case constant(ConstantDeclaration)
    case variable(VariableDeclaration)
    case operatorDef(OperatorDefinition)
    case theorem(TheoremDeclaration)
    case assumption(AssumptionDeclaration)
    case instance(InstanceDeclaration)
    case specification(SpecificationDeclaration)
    case invariant(InvariantDeclaration)
    case property(PropertyDeclaration)

    var location: SourceLocation {
        switch self {
        case .constant(let d): return d.location
        case .variable(let d): return d.location
        case .operatorDef(let d): return d.location
        case .theorem(let d): return d.location
        case .assumption(let d): return d.location
        case .instance(let d): return d.location
        case .specification(let d): return d.location
        case .invariant(let d): return d.location
        case .property(let d): return d.location
        }
    }
}

struct ConstantDeclaration: TLANode {
    let names: [String]
    let location: SourceLocation
}

struct VariableDeclaration: TLANode {
    let names: [String]
    let location: SourceLocation
}

/// Represents a parameter in an operator definition
struct OperatorParameter: Equatable {
    let name: String
    let arity: Int?  // nil for value parameter, Int for operator parameter with that arity

    /// Value parameter (e.g., x, y)
    static func value(_ name: String) -> OperatorParameter {
        OperatorParameter(name: name, arity: nil)
    }

    /// Operator parameter with arity (e.g., F(_) has arity 1, G(_, _) has arity 2)
    static func op(_ name: String, arity: Int) -> OperatorParameter {
        OperatorParameter(name: name, arity: arity)
    }

    var isOperator: Bool { arity != nil }
}

struct OperatorDefinition: TLANode {
    let name: String
    let parameters: [OperatorParameter]
    let body: TLAExpression
    let isRecursive: Bool
    let location: SourceLocation

    /// Convenience accessor for simple parameter names (backwards compatibility)
    var parameterNames: [String] {
        parameters.map { $0.name }
    }
}

struct TheoremDeclaration: TLANode {
    let name: String?
    let body: TLAExpression
    let proof: TLAProof?
    let location: SourceLocation
}

struct AssumptionDeclaration: TLANode {
    let name: String?
    let body: TLAExpression
    let location: SourceLocation
}

struct InstanceDeclaration: TLANode {
    let name: String?
    let moduleName: String
    let substitutions: [Substitution]
    let location: SourceLocation

    struct Substitution {
        let parameter: String
        let expression: TLAExpression
    }
}

/// SPECIFICATION declaration - declares the specification formula
struct SpecificationDeclaration: TLANode {
    let name: String  // Name of the specification operator (e.g., "Spec")
    let location: SourceLocation
}

/// INVARIANT declaration - declares an invariant to check
struct InvariantDeclaration: TLANode {
    let names: [String]  // Can list multiple invariants
    let location: SourceLocation
}

/// PROPERTY declaration - declares a temporal property to check
struct PropertyDeclaration: TLANode {
    let names: [String]  // Can list multiple properties
    let location: SourceLocation
}

// Expressions
indirect enum TLAExpression: TLANode {
    case identifier(String, SourceLocation)
    case number(Int, SourceLocation)
    case string(String, SourceLocation)
    case boolean(Bool, SourceLocation)

    // Operators
    case unary(TLAUnaryOp, TLAExpression, SourceLocation)
    case binary(TLAExpression, TLABinaryOp, TLAExpression, SourceLocation)
    case ternary(TLAExpression, TLAExpression, TLAExpression, SourceLocation) // IF-THEN-ELSE

    // Quantifiers
    case forall([BoundVariable], TLAExpression, SourceLocation)
    case exists([BoundVariable], TLAExpression, SourceLocation)
    case choose(BoundVariable, TLAExpression, SourceLocation)

    // Sets
    case setEnumeration([TLAExpression], SourceLocation)
    case setComprehension(BoundVariable, TLAExpression, SourceLocation)  // {x \in S : P(x)} - domain is in BoundVariable
    case setMap(TLAExpression, BoundVariable, SourceLocation)  // {f(x) : x \in S} - map form
    case setRange(TLAExpression, TLAExpression, SourceLocation)

    // Functions
    case functionApplication(TLAExpression, [TLAExpression], SourceLocation)
    case functionConstruction([BoundVariable], TLAExpression, SourceLocation)
    case except(TLAExpression, [ExceptClause], SourceLocation)

    // Records
    case recordConstruction([(String, TLAExpression)], SourceLocation)
    case recordAccess(TLAExpression, String, SourceLocation)

    // Tuples
    case tuple([TLAExpression], SourceLocation)

    // Let-In
    case letIn([OperatorDefinition], TLAExpression, SourceLocation)

    // Case
    case caseExpr([CaseArm], TLAExpression?, SourceLocation)

    // Prime (next state)
    case prime(TLAExpression, SourceLocation)

    // Temporal
    case always(TLAExpression, SourceLocation)
    case eventually(TLAExpression, SourceLocation)
    case leadsto(TLAExpression, TLAExpression, SourceLocation)
    case weakFairnessLeadsto(TLAExpression, TLAExpression, SourceLocation)  // -+->
    case enabled(TLAExpression, SourceLocation)
    case unchanged(TLAExpression, SourceLocation)
    case stuttering(TLAExpression, TLAExpression, SourceLocation) // [A]_v
    case action(TLAExpression, TLAExpression, SourceLocation) // <<A>>_v
    case weakFairness(TLAExpression, TLAExpression, SourceLocation) // WF_v(A)
    case strongFairness(TLAExpression, TLAExpression, SourceLocation) // SF_v(A)

    // Lambda
    case lambda([String], TLAExpression, SourceLocation)  // LAMBDA x, y : expr

    var location: SourceLocation {
        switch self {
        case .identifier(_, let loc),
             .number(_, let loc),
             .string(_, let loc),
             .boolean(_, let loc),
             .unary(_, _, let loc),
             .binary(_, _, _, let loc),
             .ternary(_, _, _, let loc),
             .forall(_, _, let loc),
             .exists(_, _, let loc),
             .choose(_, _, let loc),
             .setEnumeration(_, let loc),
             .setComprehension(_, _, let loc),
             .setMap(_, _, let loc),
             .setRange(_, _, let loc),
             .functionApplication(_, _, let loc),
             .functionConstruction(_, _, let loc),
             .except(_, _, let loc),
             .recordConstruction(_, let loc),
             .recordAccess(_, _, let loc),
             .tuple(_, let loc),
             .letIn(_, _, let loc),
             .caseExpr(_, _, let loc),
             .prime(_, let loc),
             .always(_, let loc),
             .eventually(_, let loc),
             .leadsto(_, _, let loc),
             .weakFairnessLeadsto(_, _, let loc),
             .enabled(_, let loc),
             .unchanged(_, let loc),
             .stuttering(_, _, let loc),
             .action(_, _, let loc),
             .weakFairness(_, _, let loc),
             .strongFairness(_, _, let loc),
             .lambda(_, _, let loc):
            return loc
        }
    }
}

struct BoundVariable {
    enum Pattern: Equatable {
        case single(String)
        case tuple([String])

        var description: String {
            switch self {
            case .single(let name):
                return name
            case .tuple(let names):
                return "<<\(names.joined(separator: ", "))>>"
            }
        }
    }

    let pattern: Pattern
    let domain: TLAExpression?

    // Convenience initializer for single variable (backwards compatibility)
    init(name: String, domain: TLAExpression?) {
        self.pattern = .single(name)
        self.domain = domain
    }

    // Full initializer
    init(pattern: Pattern, domain: TLAExpression?) {
        self.pattern = pattern
        self.domain = domain
    }

    // Convenience accessor for single variable names
    var name: String {
        switch pattern {
        case .single(let name):
            return name
        case .tuple(let names):
            return names.first ?? ""
        }
    }

    // Get all variable names bound by this pattern
    var boundNames: [String] {
        switch pattern {
        case .single(let name):
            return [name]
        case .tuple(let names):
            return names
        }
    }
}

struct ExceptClause {
    let path: [TLAExpression]
    let value: TLAExpression
}

struct CaseArm {
    let condition: TLAExpression
    let result: TLAExpression
}

enum TLAUnaryOp {
    case not
    case negative
    case domain
    case subset
    case union
}

enum TLABinaryOp {
    // Logical
    case and, or, implies, iff

    // Comparison
    case eq, neq, lt, le, gt, ge

    // Arithmetic
    case plus, minus, times, div, mod, exp

    // Set
    case elementOf, notElementOf, subsetOf, supersetOf, properSubset, properSuperset
    case setUnion, setIntersect, setMinus, cartesian

    // Sequence
    case concat, append

    // Function
    case compose
    case functionOverride  // @@ operator
    case colonGreater      // :> operator (x :> y = [z \in {x} |-> y])

    // Relations (ordering)
    case prec, preceq, succ, succeq

    // Relations (similarity)
    case sim, simeq, approx, cong, doteq, propto, asymp

    // Square operators (lattice operations)
    case sqcap, sqcup, sqsubseteq, sqsupseteq

    // Circle operators
    case oplus, ominus, otimes, oslash, odot

    // Other mathematical operators
    case cdot, bullet, star, bigcirc, wr
}

// Proof
indirect enum TLAProof: TLANode {
    case by(facts: [ProofFact], defs: [String], SourceLocation)
    case obvious(SourceLocation)
    case omitted(SourceLocation)
    case steps([TLAProofStep], SourceLocation)

    var location: SourceLocation {
        switch self {
        case .by(_, _, let loc), .obvious(let loc), .omitted(let loc), .steps(_, let loc):
            return loc
        }
    }
}

struct ProofFact: TLANode {
    enum Kind: Equatable {
        case identifier(String)
        case stepRef(level: Int, number: Int?)  // <1>2 or <1> (number optional)
    }
    let kind: Kind
    let location: SourceLocation
}

struct TLAProofStep: TLANode {
    let level: Int           // 1, 2, 3...
    let number: Int?         // Step number at level (nil for <1> QED style)
    let content: TLAProofStepContent
    let location: SourceLocation
}

enum TLAProofStepContent {
    case assertion(TLAExpression, TLAProof?)
    case suffices(assume: TLAExpression?, prove: TLAExpression, TLAProof?)
    case take([BoundVariable])
    case have(TLAExpression, TLAProof?)
    case witness([TLAExpression], TLAProof?)
    case pick([BoundVariable], TLAExpression, TLAProof?)
    case use(facts: [ProofFact])
    case hide(defs: [String], facts: [ProofFact])  // HIDE DEF x, y or HIDE fact1, fact2
    case define([OperatorDefinition])
    case caseStep(TLAExpression, TLAProof?)
    case qed(TLAProof?)
}

// MARK: - Parser

final class TLAParser {
    private var tokens: [TLAToken] = []
    private var current = 0
    private var errors: [ParseError] = []
    private var proofDepth = 0
    private let maxProofDepth = 100  // Prevent stack overflow on deeply nested proofs

    struct ParseError: Error, CustomStringConvertible {
        let message: String
        let location: SourceLocation

        var description: String {
            "Line \(location.line), column \(location.column): \(message)"
        }
    }

    struct ParseErrors: Error {
        let errors: [ParseError]
        let partialModule: TLAModule?  // Module parsed so far, even with errors

        init(errors: [ParseError], partialModule: TLAModule? = nil) {
            self.errors = errors
            self.partialModule = partialModule
        }
    }

    func parse(_ source: String) -> Result<TLAModule, ParseErrors> {
        let lexer = TLALexer(source: source)
        self.tokens = lexer.scanTokens()
        self.current = 0
        self.errors = []

        do {
            let module = try parseModule()
            if errors.isEmpty {
                return .success(module)
            } else {
                // Return errors but include partial module for IDE features
                return .failure(ParseErrors(errors: errors, partialModule: module))
            }
        } catch let error as ParseError {
            errors.append(error)
            // Try to create a minimal partial module if possible
            let partialModule = TLAModule(
                name: "Unknown",
                extends: [],
                declarations: [],
                location: .unknown
            )
            return .failure(ParseErrors(errors: errors, partialModule: partialModule))
        } catch {
            errors.append(ParseError(message: error.localizedDescription, location: .unknown))
            return .failure(ParseErrors(errors: errors, partialModule: nil))
        }
    }

    /// Parse a single expression from a string
    func parseExpression(_ source: String) -> Result<TLAExpression, ParseErrors> {
        let lexer = TLALexer(source: source)
        self.tokens = lexer.scanTokens()
        self.current = 0
        self.errors = []

        do {
            let expr = try parseExpression()
            if errors.isEmpty {
                return .success(expr)
            } else {
                return .failure(ParseErrors(errors: errors))
            }
        } catch let error as ParseError {
            errors.append(error)
            return .failure(ParseErrors(errors: errors))
        } catch {
            errors.append(ParseError(message: error.localizedDescription, location: .unknown))
            return .failure(ParseErrors(errors: errors))
        }
    }

    // MARK: - Module Parsing

    private func parseModule() throws -> TLAModule {
        // Skip to module start
        while !isAtEnd && !check(.moduleStart) {
            advance()
        }

        guard match(.moduleStart) else {
            throw error("Expected module start '----'")
        }

        guard case .keyword(.module) = peek().type else {
            throw error("Expected 'MODULE' keyword")
        }
        advance()

        guard case .identifier(let name) = peek().type else {
            throw error("Expected module name")
        }
        let moduleName = name
        let startLocation = currentLocation
        advance()

        // Skip remaining dashes
        while !isAtEnd && check(.moduleStart) {
            advance()
        }

        // Parse EXTENDS
        var extends: [String] = []
        if case .keyword(.extends) = peek().type {
            advance()
            extends = try parseIdentifierList()
        }

        // Parse declarations with error recovery
        var declarations: [TLADeclaration] = []
        while !isAtEnd && !check(.moduleEnd) {
            // Use recovery-enabled parsing to collect multiple errors
            if let decl = parseDeclarationWithRecovery() {
                declarations.append(decl)
            }
        }

        _ = match(.moduleEnd)

        return TLAModule(
            name: moduleName,
            extends: extends,
            declarations: declarations,
            location: startLocation
        )
    }

    private func parseIdentifierList() throws -> [String] {
        var identifiers: [String] = []

        guard case .identifier(let first) = peek().type else {
            throw error("Expected identifier")
        }
        identifiers.append(first)
        advance()

        while match(.comma) {
            guard case .identifier(let name) = peek().type else {
                throw error("Expected identifier after comma")
            }
            identifiers.append(name)
            advance()
        }

        return identifiers
    }

    /// Parse operator parameters - supports both value parameters (x) and operator parameters (F(_), G(_, _))
    private func parseOperatorParameters() throws -> [OperatorParameter] {
        var parameters: [OperatorParameter] = []

        // Parse first parameter
        guard case .identifier(let firstName) = peek().type else {
            throw error("Expected parameter name")
        }
        advance()

        // Check if this is a higher-order operator parameter: F(_) or F(_, _)
        if match(.leftParen) {
            let arity = try parseOperatorArity()
            guard match(.rightParen) else {
                throw error("Expected ')' after operator parameter arity")
            }
            parameters.append(.op(firstName, arity: arity))
        } else {
            parameters.append(.value(firstName))
        }

        // Parse remaining parameters
        while match(.comma) {
            guard case .identifier(let name) = peek().type else {
                throw error("Expected parameter name after comma")
            }
            advance()

            // Check if this is a higher-order operator parameter
            if match(.leftParen) {
                let arity = try parseOperatorArity()
                guard match(.rightParen) else {
                    throw error("Expected ')' after operator parameter arity")
                }
                parameters.append(.op(name, arity: arity))
            } else {
                parameters.append(.value(name))
            }
        }

        return parameters
    }

    /// Parse the arity pattern for an operator parameter: _, _, _ etc.
    private func parseOperatorArity() throws -> Int {
        var arity = 0

        // First underscore (subscriptSeparator)
        if case .subscriptSeparator = peek().type {
            advance()
            arity = 1
        } else if case .identifier(let name) = peek().type, name == "_" {
            // Handle underscore as identifier (fallback)
            advance()
            arity = 1
        } else {
            throw error("Expected '_' in operator parameter arity")
        }

        // Count additional underscores separated by commas
        while match(.comma) {
            if case .subscriptSeparator = peek().type {
                advance()
                arity += 1
            } else if case .identifier(let name) = peek().type, name == "_" {
                advance()
                arity += 1
            } else {
                throw error("Expected '_' after comma in operator parameter arity")
            }
        }

        return arity
    }

    private func parseDeclaration() throws -> TLADeclaration? {
        let token = peek()

        switch token.type {
        case .keyword(.constant), .keyword(.constants):
            return try parseConstantDeclaration()
        case .keyword(.variable), .keyword(.variables):
            return try parseVariableDeclaration()
        case .keyword(.theorem), .keyword(.lemma), .keyword(.corollary), .keyword(.proposition):
            return try parseTheoremDeclaration()
        case .keyword(.axiom):
            return try parseAxiomDeclaration()
        case .keyword(.assume), .keyword(.assumption):
            return try parseAssumptionDeclaration()
        case .keyword(.instance):
            return try parseInstanceDeclaration()
        case .keyword(.recursive):
            return try parseRecursiveOperatorDefinition()
        case .keyword(.local):
            return try parseLocalDeclaration()
        case .keyword(.specification):
            return try parseSpecificationDeclaration()
        case .keyword(.invariant):
            return try parseInvariantDeclaration()
        case .keyword(.property):
            return try parsePropertyDeclaration()
        case .identifier:
            return try parseOperatorDefinition()
        case .comment, .blockComment:
            advance()
            return nil
        default:
            advance() // Skip unknown tokens
            return nil
        }
    }

    private func parseConstantDeclaration() throws -> TLADeclaration {
        let loc = currentLocation
        advance() // Skip CONSTANT/CONSTANTS

        let names = try parseIdentifierList()
        return .constant(ConstantDeclaration(names: names, location: loc))
    }

    private func parseVariableDeclaration() throws -> TLADeclaration {
        let loc = currentLocation
        advance() // Skip VARIABLE/VARIABLES

        let names = try parseIdentifierList()
        return .variable(VariableDeclaration(names: names, location: loc))
    }

    private func parseOperatorDefinition() throws -> TLADeclaration {
        let loc = currentLocation

        guard case .identifier(let name) = peek().type else {
            throw error("Expected operator name")
        }
        advance()

        var parameters: [OperatorParameter] = []

        // Check for parameters
        if match(.leftParen) {
            parameters = try parseOperatorParameters()
            guard match(.rightParen) else {
                throw error("Expected ')' after parameters")
            }
        }

        guard case .operator(.define) = peek().type else {
            throw error("Expected '==' in operator definition")
        }
        advance()

        let body = try parseExpression()

        return .operatorDef(OperatorDefinition(
            name: name,
            parameters: parameters,
            body: body,
            isRecursive: false,
            location: loc
        ))
    }

    private func parseRecursiveOperatorDefinition() throws -> TLADeclaration {
        let loc = currentLocation
        advance() // Skip RECURSIVE

        guard case .identifier(let name) = peek().type else {
            throw error("Expected operator name after RECURSIVE")
        }
        advance()

        var parameters: [OperatorParameter] = []

        // Check for parameters
        if match(.leftParen) {
            parameters = try parseOperatorParameters()
            guard match(.rightParen) else {
                throw error("Expected ')' after parameters")
            }
        }

        guard case .operator(.define) = peek().type else {
            throw error("Expected '==' in recursive operator definition")
        }
        advance()

        let body = try parseExpression()

        return .operatorDef(OperatorDefinition(
            name: name,
            parameters: parameters,
            body: body,
            isRecursive: true,
            location: loc
        ))
    }

    private func parseLocalDeclaration() throws -> TLADeclaration? {
        advance() // Skip LOCAL

        // LOCAL can precede operator definitions or instances
        let token = peek()
        switch token.type {
        case .identifier:
            // Parse as a local operator definition
            let decl = try parseOperatorDefinition()
            // Mark it as local (could add a flag to the declaration types)
            return decl
        case .keyword(.instance):
            return try parseInstanceDeclaration()
        default:
            throw error("Expected operator definition or INSTANCE after LOCAL")
        }
    }

    private func parseTheoremDeclaration() throws -> TLADeclaration {
        let loc = currentLocation
        advance() // Skip THEOREM/LEMMA/COROLLARY/PROPOSITION

        var name: String? = nil
        if case .identifier(let n) = peek().type {
            let next = peekNext()
            if case .operator(.define) = next.type {
                name = n
                advance()
                advance() // Skip ==
            }
        }

        let body = try parseExpression()

        // Parse optional proof
        let proof = try parseProof()

        return .theorem(TheoremDeclaration(
            name: name,
            body: body,
            proof: proof,
            location: loc
        ))
    }

    private func parseAxiomDeclaration() throws -> TLADeclaration {
        let loc = currentLocation
        advance() // Skip AXIOM

        var name: String? = nil
        if case .identifier(let n) = peek().type {
            let next = peekNext()
            if case .operator(.define) = next.type {
                name = n
                advance()
                advance() // Skip ==
            }
        }

        let body = try parseExpression()

        // AXIOM is treated as an ASSUMPTION (axiomatic truth)
        return .assumption(AssumptionDeclaration(
            name: name,
            body: body,
            location: loc
        ))
    }

    private func parseAssumptionDeclaration() throws -> TLADeclaration {
        let loc = currentLocation
        advance() // Skip ASSUME/ASSUMPTION

        var name: String? = nil
        if case .identifier(let n) = peek().type {
            let next = peekNext()
            if case .operator(.define) = next.type {
                name = n
                advance()
                advance()
            }
        }

        let body = try parseExpression()

        return .assumption(AssumptionDeclaration(
            name: name,
            body: body,
            location: loc
        ))
    }

    private func parseInstanceDeclaration() throws -> TLADeclaration {
        let loc = currentLocation
        advance() // Skip INSTANCE

        guard case .identifier(let moduleName) = peek().type else {
            throw error("Expected module name after INSTANCE")
        }
        advance()

        var substitutions: [InstanceDeclaration.Substitution] = []

        if case .keyword(.with) = peek().type {
            advance()
            substitutions = try parseSubstitutions()
        }

        return .instance(InstanceDeclaration(
            name: nil,
            moduleName: moduleName,
            substitutions: substitutions,
            location: loc
        ))
    }

    private func parseSubstitutions() throws -> [InstanceDeclaration.Substitution] {
        var subs: [InstanceDeclaration.Substitution] = []

        repeat {
            guard case .identifier(let param) = peek().type else {
                throw error("Expected parameter name in substitution")
            }
            advance()

            guard case .operator(.rightArrow) = peek().type else {
                throw error("Expected '<-' in substitution")
            }
            advance()

            let expr = try parseExpression()
            subs.append(InstanceDeclaration.Substitution(parameter: param, expression: expr))
        } while match(.comma)

        return subs
    }

    private func parseSpecificationDeclaration() throws -> TLADeclaration {
        let loc = currentLocation
        advance() // Skip SPECIFICATION

        guard case .identifier(let name) = peek().type else {
            throw error("Expected specification name after SPECIFICATION")
        }
        advance()

        return .specification(SpecificationDeclaration(name: name, location: loc))
    }

    private func parseInvariantDeclaration() throws -> TLADeclaration {
        let loc = currentLocation
        advance() // Skip INVARIANT

        let names = try parseIdentifierList()
        return .invariant(InvariantDeclaration(names: names, location: loc))
    }

    private func parsePropertyDeclaration() throws -> TLADeclaration {
        let loc = currentLocation
        advance() // Skip PROPERTY

        let names = try parseIdentifierList()
        return .property(PropertyDeclaration(names: names, location: loc))
    }

    // MARK: - Expression Parsing
    // Operator precedence follows TLA+ spec (lowest to highest):
    // 1. ~> (leadsto) - Level 2-2
    // 2. <=> (equivalence) - Level 1-1
    // 3. => (implication) - Level 1-1
    // 4. \/ (disjunction) - Level 3-3
    // 5. /\ (conjunction) - Level 3-3
    // 6. ~ (negation) - Level 4-4
    // 7. Comparison operators - Level 5-5
    // 8. .. (range) - Level 9-9
    // 9. +, - (additive) - Level 10-10
    // 10. *, / (multiplicative) - Level 13-13
    // 11. ^ (exponentiation) - Level 14-14
    // 12. Unary prefix (-, DOMAIN, SUBSET, UNION) - Level 12-12
    // 13. ' (prime) - Level 15-15
    // 14. Function application [] - Level 16-16
    // 15. Record access . - Level 17-17

    private func parseExpression() throws -> TLAExpression {
        return try parseLeadsto()  // Leadsto is lowest precedence
    }

    private func parseLeadsto() throws -> TLAExpression {
        var left = try parseEquivalence()

        while true {
            let loc = currentLocation
            if case .operator(.leadsto) = peek().type {
                advance()
                let right = try parseEquivalence()
                left = .leadsto(left, right, loc)
            } else if case .operator(.weakFairnessLeadsto) = peek().type {
                advance()
                let right = try parseEquivalence()
                left = .weakFairnessLeadsto(left, right, loc)
            } else {
                break
            }
        }

        return left
    }

    private func parseEquivalence() throws -> TLAExpression {
        var left = try parseImplication()

        while case .operator(.equivalence) = peek().type {
            let loc = currentLocation
            advance()
            let right = try parseImplication()
            left = .binary(left, .iff, right, loc)
        }

        return left
    }

    private func parseImplication() throws -> TLAExpression {
        let left = try parseDisjunction()

        // Right-associative: a => b => c parses as a => (b => c)
        if case .operator(.implication) = peek().type {
            let loc = currentLocation
            advance()
            let right = try parseImplication()  // Recursive for right-associativity
            return .binary(left, .implies, right, loc)
        }

        return left
    }

    private func parseDisjunction() throws -> TLAExpression {
        var left = try parseConjunction()

        while case .operator(.disjunction) = peek().type {
            let loc = currentLocation
            advance()
            let right = try parseConjunction()
            left = .binary(left, .or, right, loc)
        }

        return left
    }

    private func parseConjunction() throws -> TLAExpression {
        var left = try parseNegation()

        while case .operator(.conjunction) = peek().type {
            let loc = currentLocation
            advance()
            let right = try parseNegation()
            left = .binary(left, .and, right, loc)
        }

        return left
    }

    // Negation at TLA+ Level 4-4 (between conjunction and comparison)
    private func parseNegation() throws -> TLAExpression {
        let loc = currentLocation

        if case .operator(.negation) = peek().type {
            advance()
            let expr = try parseNegation()  // Right-associative: ~~x = ~(~x)
            return .unary(.not, expr, loc)
        }

        return try parseComparison()
    }

    private func parseComparison() throws -> TLAExpression {
        var left = try parseFunctionOverride()  // @@ has higher precedence than comparison

        let comparisonOps: [TLAOperator: TLABinaryOp] = [
            // Equality
            .equal: .eq,
            .notEqual: .neq,
            .notEqualAlt: .neq,
            .notEqualUnicode: .neq,

            // Numeric comparison
            .lessThan: .lt,
            .lessThanOrEqual: .le,
            .lessThanOrEqualAlt: .le,
            .greaterThan: .gt,
            .greaterThanOrEqual: .ge,
            .greaterThanOrEqualAlt: .ge,

            // Set membership
            .elementOf: .elementOf,
            .notElementOf: .notElementOf,
            .subsetOf: .subsetOf,
            .supersetOf: .supersetOf,
            .properSubset: .properSubset,
            .properSuperset: .properSuperset,

            // Ordering relations
            .prec: .prec,
            .preceq: .preceq,
            .succ: .succ,
            .succeq: .succeq,

            // Similarity relations
            .sim: .sim,
            .simeq: .simeq,
            .approx: .approx,
            .cong: .cong,
            .doteq: .doteq,
            .propto: .propto,
            .asymp: .asymp,

            // Square relations
            .sqsubseteq: .sqsubseteq,
            .sqsupseteq: .sqsupseteq,
        ]

        while case .operator(let op) = peek().type, let binOp = comparisonOps[op] {
            let loc = currentLocation
            advance()
            let right = try parseRange()
            left = .binary(left, binOp, right, loc)
        }

        return left
    }

    // Function operators @@ and :>
    // f @@ g combines functions, with g's mappings overriding f's
    // x :> y creates a function mapping x to y: [z \in {x} |-> y]
    private func parseFunctionOverride() throws -> TLAExpression {
        var left = try parseRange()

        while true {
            let loc = currentLocation
            if case .operator(.functionOverride) = peek().type {
                advance()
                let right = try parseRange()
                left = .binary(left, .functionOverride, right, loc)
            } else if case .operator(.colonGreater) = peek().type {
                advance()
                let right = try parseRange()
                left = .binary(left, .colonGreater, right, loc)
            } else {
                break
            }
        }

        return left
    }

    private func parseRange() throws -> TLAExpression {
        var left = try parseAdditive()

        // Set range: 1..10 creates the set {1, 2, ..., 10}
        if case .operator(.dotDot) = peek().type {
            let loc = currentLocation
            advance()
            let right = try parseAdditive()
            left = .setRange(left, right, loc)
        }

        return left
    }

    private func parseAdditive() throws -> TLAExpression {
        var left = try parseMultiplicative()

        while true {
            let loc = currentLocation
            if case .operator(.plus) = peek().type {
                advance()
                let right = try parseMultiplicative()
                left = .binary(left, .plus, right, loc)
            } else if case .operator(.minus) = peek().type {
                advance()
                let right = try parseMultiplicative()
                left = .binary(left, .minus, right, loc)
            } else if case .operator(.cup) = peek().type {
                advance()
                let right = try parseMultiplicative()
                left = .binary(left, .setUnion, right, loc)
            } else if case .operator(.unionAlt) = peek().type {
                advance()
                let right = try parseMultiplicative()
                left = .binary(left, .setUnion, right, loc)
            } else if case .operator(.cap) = peek().type {
                advance()
                let right = try parseMultiplicative()
                left = .binary(left, .setIntersect, right, loc)
            } else if case .operator(.intersectAlt) = peek().type {
                advance()
                let right = try parseMultiplicative()
                left = .binary(left, .setIntersect, right, loc)
            } else if case .operator(.setMinus) = peek().type {
                advance()
                let right = try parseMultiplicative()
                left = .binary(left, .setMinus, right, loc)
            } else if case .operator(.concat) = peek().type {
                advance()
                let right = try parseMultiplicative()
                left = .binary(left, .concat, right, loc)
            } else if case .operator(.concatAlt) = peek().type {
                advance()
                let right = try parseMultiplicative()
                left = .binary(left, .concat, right, loc)
            } else if case .operator(.uplus) = peek().type {
                advance()
                let right = try parseMultiplicative()
                left = .binary(left, .setUnion, right, loc) // \uplus is disjoint union, treating as union
            } else if case .operator(.oplus) = peek().type {
                advance()
                let right = try parseMultiplicative()
                left = .binary(left, .oplus, right, loc)
            } else if case .operator(.ominus) = peek().type {
                advance()
                let right = try parseMultiplicative()
                left = .binary(left, .ominus, right, loc)
            } else if case .operator(.sqcup) = peek().type {
                advance()
                let right = try parseMultiplicative()
                left = .binary(left, .sqcup, right, loc)
            } else if case .operator(.sqcap) = peek().type {
                advance()
                let right = try parseMultiplicative()
                left = .binary(left, .sqcap, right, loc)
            } else {
                break
            }
        }

        return left
    }

    private func parseMultiplicative() throws -> TLAExpression {
        var left = try parseUnary()  // Changed: unary has lower precedence than exponentiation

        while true {
            let loc = currentLocation
            if case .operator(.multiply) = peek().type {
                advance()
                let right = try parseUnary()
                left = .binary(left, .times, right, loc)
            } else if case .operator(.divide) = peek().type {
                advance()
                let right = try parseUnary()
                left = .binary(left, .div, right, loc)
            } else if case .operator(.modulo) = peek().type {
                advance()
                let right = try parseUnary()
                left = .binary(left, .mod, right, loc)
            } else if case .operator(.times) = peek().type {
                advance()
                let right = try parseUnary()
                left = .binary(left, .cartesian, right, loc)
            } else if case .operator(.intDivide) = peek().type {
                advance()
                let right = try parseUnary()
                left = .binary(left, .div, right, loc)
            } else if case .operator(.otimes) = peek().type {
                advance()
                let right = try parseUnary()
                left = .binary(left, .otimes, right, loc)
            } else if case .operator(.oslash) = peek().type {
                advance()
                let right = try parseUnary()
                left = .binary(left, .oslash, right, loc)
            } else if case .operator(.odot) = peek().type {
                advance()
                let right = try parseUnary()
                left = .binary(left, .odot, right, loc)
            } else if case .operator(.cdot) = peek().type {
                advance()
                let right = try parseUnary()
                left = .binary(left, .cdot, right, loc)
            } else if case .operator(.bullet) = peek().type {
                advance()
                let right = try parseUnary()
                left = .binary(left, .bullet, right, loc)
            } else if case .operator(.star) = peek().type {
                advance()
                let right = try parseUnary()
                left = .binary(left, .star, right, loc)
            } else if case .operator(.bigcirc) = peek().type {
                advance()
                let right = try parseUnary()
                left = .binary(left, .bigcirc, right, loc)
            } else if case .operator(.wr) = peek().type {
                advance()
                let right = try parseUnary()
                left = .binary(left, .wr, right, loc)
            } else {
                break
            }
        }

        return left
    }

    // Unary prefix operators at TLA+ Level 12-12 (DOMAIN, SUBSET, UNION, unary minus)
    // Note: Negation (~) is handled at parseNegation() at Level 4-4
    // Unary has LOWER precedence than exponentiation, so -2^2 = -(2^2)
    private func parseUnary() throws -> TLAExpression {
        let loc = currentLocation

        if case .operator(.minus) = peek().type {
            advance()
            let expr = try parseUnary()
            return .unary(.negative, expr, loc)
        }

        if case .keyword(.domain) = peek().type {
            advance()
            let expr = try parseUnary()
            return .unary(.domain, expr, loc)
        }

        if case .keyword(.subset) = peek().type {
            advance()
            let expr = try parseUnary()
            return .unary(.subset, expr, loc)
        }

        if case .keyword(.union) = peek().type {
            advance()
            let expr = try parseUnary()
            return .unary(.union, expr, loc)
        }

        return try parseExponentiation()  // Changed: exponentiation has higher precedence
    }

    private func parseExponentiation() throws -> TLAExpression {
        var left = try parsePostfix()  // Changed: postfix has highest precedence

        // Exponentiation is right-associative: 2^3^4 = 2^(3^4)
        if case .operator(.power) = peek().type {
            let loc = currentLocation
            advance()
            let right = try parseExponentiation() // Right-associative
            left = .binary(left, .exp, right, loc)
        }

        return left
    }

    private func parsePostfix() throws -> TLAExpression {
        var expr = try parsePrimary()

        while true {
            let loc = currentLocation

            if case .operator(.prime) = peek().type {
                advance()
                expr = .prime(expr, loc)
            } else if match(.leftBracket) {
                let args = try parseExpressionList()
                guard match(.rightBracket) else {
                    throw error("Expected ']' after function arguments")
                }
                expr = .functionApplication(expr, args, loc)
            } else if match(.leftParen) {
                // Operator application: Op(x, y, z)
                var args: [TLAExpression] = []
                if !check(.rightParen) {
                    args = try parseExpressionList()
                }
                guard match(.rightParen) else {
                    throw error("Expected ')' after operator arguments")
                }
                expr = .functionApplication(expr, args, loc)
            } else if match(.dot) {
                // Record access: expr.field
                guard case .identifier(let fieldName) = peek().type else {
                    throw error("Expected field name after '.'")
                }
                advance()
                expr = .recordAccess(expr, fieldName, loc)
            } else {
                break
            }
        }

        return expr
    }

    private func parsePrimary() throws -> TLAExpression {
        let token = peek()
        let loc = currentLocation

        switch token.type {
        case .identifier(let name):
            advance()
            if name == "TRUE" {
                return .boolean(true, loc)
            } else if name == "FALSE" {
                return .boolean(false, loc)
            }
            return .identifier(name, loc)

        case .number(let value):
            advance()
            return .number(value, loc)

        case .string(let value):
            advance()
            return .string(value, loc)

        case .leftParen:
            advance()
            let expr = try parseExpression()
            guard match(.rightParen) else {
                throw error("Expected ')' after expression")
            }
            return expr

        case .leftBrace:
            return try parseSetExpression()

        case .leftBracket:
            return try parseStutteringOrFunctionOrRecord()

        case .leftAngle:
            return try parseActionOrTupleExpression()

        case .operator(.always):
            advance()
            let expr = try parseUnary()
            return .always(expr, loc)

        case .operator(.eventually):
            advance()
            let expr = try parseUnary()
            return .eventually(expr, loc)

        case .operator(.forall):
            return try parseQuantifier(isForall: true)

        case .operator(.exists):
            return try parseQuantifier(isForall: false)

        case .keyword(.if_):
            return try parseIfThenElse()

        case .keyword(.let_):
            return try parseLetIn()

        case .keyword(.case_):
            return try parseCaseExpression()

        case .keyword(.choose):
            return try parseChoose()

        case .keyword(.lambda):
            return try parseLambda()

        case .keyword(.enabled):
            advance()
            let expr = try parseUnary()
            return .enabled(expr, loc)

        case .keyword(.unchanged):
            advance()
            let expr = try parseUnary()
            return .unchanged(expr, loc)

        case .keyword(.wf):
            return try parseFairnessExpression(isWeak: true)

        case .keyword(.sf):
            return try parseFairnessExpression(isWeak: false)

        case .keyword(.true_):
            advance()
            return .boolean(true, loc)

        case .keyword(.false_):
            advance()
            return .boolean(false, loc)

        default:
            throw error("Unexpected token: \(token.lexeme)")
        }
    }

    private func parseFairnessExpression(isWeak: Bool) throws -> TLAExpression {
        let loc = currentLocation
        advance() // WF_ or SF_

        // Parse subscript - can be a variable, tuple <<x,y>>, or other primary expression
        let subscriptExpr = try parsePrimary()

        // Parse the action in parentheses
        guard match(.leftParen) else {
            throw error("Expected '(' after fairness subscript")
        }
        let action = try parseExpression()
        guard match(.rightParen) else {
            throw error("Expected ')' after fairness action")
        }

        if isWeak {
            return .weakFairness(subscriptExpr, action, loc)
        } else {
            return .strongFairness(subscriptExpr, action, loc)
        }
    }

    private func parseStutteringOrFunctionOrRecord() throws -> TLAExpression {
        let loc = currentLocation
        // Don't advance yet - parseFunctionOrRecordExpression will do it

        // Try to parse as a regular bracket expression first
        let result = try parseFunctionOrRecordExpression()

        // Check if this is a stuttering operator: [A]_v
        // Handle both standalone _ token (subscriptSeparator) and legacy _identifier pattern
        if case .subscriptSeparator = peek().type {
            advance()
            let subscriptExpr = try parsePrimary()  // Allow any primary expression as subscript
            return .stuttering(result, subscriptExpr, loc)
        } else if case .identifier(let name) = peek().type, name.hasPrefix("_") {
            // Legacy support for _vars style (when underscore is part of identifier)
            let subscriptLoc = currentLocation
            advance()
            let varName = String(name.dropFirst())
            if varName.isEmpty {
                throw error("Expected subscript variable after '_' in stuttering operator")
            }
            let subscriptExpr = TLAExpression.identifier(varName, subscriptLoc)
            return .stuttering(result, subscriptExpr, loc)
        }

        return result
    }

    private func parseActionOrTupleExpression() throws -> TLAExpression {
        let loc = currentLocation

        // Try to parse as a tuple first
        let result = try parseTupleExpression()

        // Check if this is an action operator: <<A>>_v
        // Handle both standalone _ token (subscriptSeparator) and legacy _identifier pattern
        if case .subscriptSeparator = peek().type {
            advance()
            let subscriptExpr = try parsePrimary()  // Allow any primary expression as subscript
            return .action(result, subscriptExpr, loc)
        } else if case .identifier(let name) = peek().type, name.hasPrefix("_") {
            // Legacy support for _vars style (when underscore is part of identifier)
            let subscriptLoc = currentLocation
            advance()
            let varName = String(name.dropFirst())
            if varName.isEmpty {
                throw error("Expected subscript variable after '_' in action operator")
            }
            let subscriptExpr = TLAExpression.identifier(varName, subscriptLoc)
            return .action(result, subscriptExpr, loc)
        }

        return result
    }

    private func parseSetExpression() throws -> TLAExpression {
        let loc = currentLocation
        advance() // {

        if match(.rightBrace) {
            return .setEnumeration([], loc)
        }

        // Try to parse as set comprehension: {x \in S : P(x)} or {<<x, y>> \in S : P(x, y)}
        // First, check if we have identifier or tuple followed by \in
        let savedCurrent = current
        var isBoundVarPattern = false
        var varPattern: TLAExpression?

        // Parse the pattern (identifier or tuple)
        if case .identifier(_) = peek().type {
            let identExpr = try parsePrimary()
            if case .operator(.elementOf) = peek().type {
                isBoundVarPattern = true
                varPattern = identExpr
            }
        } else if case .leftAngle = peek().type {
            let tupleExpr = try parsePrimary()  // Parse just the tuple
            if case .operator(.elementOf) = peek().type {
                isBoundVarPattern = true
                varPattern = tupleExpr
            }
        }

        if isBoundVarPattern, let pattern = varPattern {
            // This is a filter set comprehension
            advance() // consume \in
            let domain = try parseExpression()
            guard match(.colon) else {
                throw error("Expected ':' in set comprehension")
            }
            let predicate = try parseExpression()
            guard match(.rightBrace) else {
                throw error("Expected '}' after set comprehension")
            }

            // Handle both identifier and tuple pattern for bound variable
            let boundVar: BoundVariable
            switch pattern {
            case .identifier(let varName, _):
                boundVar = BoundVariable(name: varName, domain: domain)
            case .tuple(let elements, _):
                // Extract names from tuple elements
                var names: [String] = []
                for element in elements {
                    if case .identifier(let name, _) = element {
                        names.append(name)
                    } else {
                        throw error("Expected identifier in tuple pattern")
                    }
                }
                boundVar = BoundVariable(pattern: .tuple(names), domain: domain)
            default:
                throw error("Expected identifier or tuple pattern in set comprehension")
            }
            return .setComprehension(boundVar, predicate, loc)
        }

        // Not a bound var pattern, reset and parse as regular expression
        current = savedCurrent

        let first = try parseExpression()

        // Check for map set comprehension: {expr : x \in S}
        if match(.colon) {
            // Parse bound variables after the colon
            let boundVars = try parseBoundVariables()
            guard match(.rightBrace) else {
                throw error("Expected '}' after set comprehension")
            }
            // Map form: expression mapped over bound variables
            // Return as setComprehension with the expression as predicate
            if let boundVar = boundVars.first {
                return .setMap(first, boundVar, loc)
            } else {
                throw error("Expected bound variable in set comprehension")
            }
        }

        // Set enumeration
        var elements = [first]
        while match(.comma) {
            elements.append(try parseExpression())
        }
        guard match(.rightBrace) else {
            throw error("Expected '}' after set elements")
        }

        return .setEnumeration(elements, loc)
    }

    private func parseFunctionOrRecordExpression() throws -> TLAExpression {
        let loc = currentLocation
        advance() // [

        // Check for EXCEPT: [f EXCEPT ![x] = v]
        if case .identifier(_) = peek().type {
            let next = peekNext()
            if case .keyword(.except) = next.type {
                return try parseExceptExpression(location: loc)
            }
        }

        // Check for record construction: [field |-> value, ...]
        if case .identifier(_) = peek().type {
            let next = peekNext()
            if case .operator(.mapsto) = next.type {
                return try parseRecordConstruction(location: loc)
            }
        }

        // Check if this is a simple [expr] for stuttering operator [A]_v
        // We need to distinguish [expr] from [x \in S |-> expr]
        // Look ahead to see if we have the function construction pattern
        if case .identifier(_) = peek().type {
            let next = peekNext()
            // If next is ] or _ (subscript separator), this is [expr] for stuttering
            if case .rightBracket = next.type {
                let expr = try parseExpression()
                guard match(.rightBracket) else {
                    throw error("Expected ']' after expression")
                }
                return expr
            }
            // If next is not \in, this is [expr] for stuttering
            if case .operator(.elementOf) = next.type {
                // This is function construction: [x \in S |-> expr]
            } else {
                // This is [expr] for stuttering
                let expr = try parseExpression()
                guard match(.rightBracket) else {
                    throw error("Expected ']' after expression")
                }
                return expr
            }
        }

        // Function construction: [x \in S |-> expr]
        let boundVars = try parseBoundVariables()
        guard case .operator(.mapsto) = peek().type else {
            throw error("Expected '|->' in function construction")
        }
        advance()
        let body = try parseExpression()
        guard match(.rightBracket) else {
            throw error("Expected ']' after function construction")
        }

        return .functionConstruction(boundVars, body, loc)
    }

    private func parseExceptExpression(location: SourceLocation) throws -> TLAExpression {
        // Parse: [expr EXCEPT ![x] = v, ![y] = w, ...]
        // Base expression can be identifier, function application, record access, etc.
        let baseExpr = try parseExceptBaseExpression()

        guard case .keyword(.except) = peek().type else {
            throw error("Expected EXCEPT keyword")
        }
        advance()

        var clauses: [ExceptClause] = []

        repeat {
            // Parse ![path] = value or !.field = value
            guard case .exclamation = peek().type else {
                throw error("Expected '!' in EXCEPT clause")
            }
            advance()

            var path: [TLAExpression] = []

            // Handle multiple subscripts: ![a][b] = v or !.field.subfield = v
            while true {
                if match(.leftBracket) {
                    let index = try parseExpression()
                    path.append(index)
                    guard match(.rightBracket) else {
                        throw error("Expected ']' in EXCEPT path")
                    }
                } else if match(.dot) {
                    guard case .identifier(let fieldName) = peek().type else {
                        throw error("Expected field name after '.' in EXCEPT")
                    }
                    let fieldLoc = currentLocation
                    advance()
                    path.append(.string(fieldName, fieldLoc))
                } else {
                    break
                }
            }

            guard case .operator(.equal) = peek().type else {
                throw error("Expected '=' in EXCEPT clause")
            }
            advance()

            let value = try parseExpression()
            clauses.append(ExceptClause(path: path, value: value))
        } while match(.comma)

        guard match(.rightBracket) else {
            throw error("Expected ']' after EXCEPT expression")
        }

        return .except(baseExpr, clauses, location)
    }

    /// Parse base expression for EXCEPT - allows any postfix expression including f[x], r.field, etc.
    private func parseExceptBaseExpression() throws -> TLAExpression {
        // Parse the base as a primary expression first (identifier, parenthesized expr, etc.)
        let loc = currentLocation
        var expr: TLAExpression

        switch peek().type {
        case .identifier(let name):
            advance()
            expr = .identifier(name, loc)
        case .leftParen:
            // Support parenthesized expressions: [(expr) EXCEPT ...]
            advance()
            expr = try parseExpression()
            guard match(.rightParen) else {
                throw error("Expected ')' after parenthesized expression in EXCEPT base")
            }
        default:
            throw error("Expected identifier or parenthesized expression as base of EXCEPT")
        }

        // Handle subscripts and field accesses: f[x][y], r.field, f[x].field
        while true {
            let exprLoc = currentLocation
            if case .leftBracket = peek().type {
                advance()
                let index = try parseExpression()
                guard match(.rightBracket) else {
                    throw error("Expected ']' after subscript in EXCEPT base")
                }
                expr = .functionApplication(expr, [index], exprLoc)
            } else if case .dot = peek().type {
                advance()
                guard case .identifier(let fieldName) = peek().type else {
                    throw error("Expected field name after '.' in EXCEPT base")
                }
                advance()
                expr = .recordAccess(expr, fieldName, exprLoc)
            } else {
                break
            }
        }

        return expr
    }

    private func parseRecordConstruction(location: SourceLocation) throws -> TLAExpression {
        var fields: [(String, TLAExpression)] = []

        repeat {
            guard case .identifier(let fieldName) = peek().type else {
                throw error("Expected field name in record")
            }
            advance()

            guard case .operator(.mapsto) = peek().type else {
                throw error("Expected '|->' after field name")
            }
            advance()

            let value = try parseExpression()
            fields.append((fieldName, value))
        } while match(.comma)

        guard match(.rightBracket) else {
            throw error("Expected ']' after record")
        }

        return .recordConstruction(fields, location)
    }

    private func parseTupleExpression() throws -> TLAExpression {
        let loc = currentLocation
        advance() // <<

        var elements: [TLAExpression] = []

        if !check(.rightAngle) {
            elements.append(try parseExpression())
            while match(.comma) {
                elements.append(try parseExpression())
            }
        }

        guard match(.rightAngle) else {
            throw error("Expected '>>' after tuple elements")
        }

        return .tuple(elements, loc)
    }

    private func parseBoundVariables() throws -> [BoundVariable] {
        var vars: [BoundVariable] = []

        repeat {
            let pattern: BoundVariable.Pattern

            // Check for tuple pattern <<x, y, ...>>
            if check(.leftAngle) {
                advance() // <<
                var names: [String] = []

                // Parse first identifier
                guard case .identifier(let firstName) = peek().type else {
                    throw error("Expected variable name in tuple pattern")
                }
                names.append(firstName)
                advance()

                // Parse remaining identifiers
                while match(.comma) {
                    guard case .identifier(let name) = peek().type else {
                        throw error("Expected variable name in tuple pattern")
                    }
                    names.append(name)
                    advance()
                }

                guard match(.rightAngle) else {
                    throw error("Expected '>>' after tuple pattern")
                }

                pattern = .tuple(names)
            } else {
                // Single variable name
                guard case .identifier(let name) = peek().type else {
                    throw error("Expected variable name or tuple pattern")
                }
                advance()
                pattern = .single(name)
            }

            // Parse optional domain
            var domain: TLAExpression? = nil
            if case .operator(.elementOf) = peek().type {
                advance()
                domain = try parseExpression()
            }

            vars.append(BoundVariable(pattern: pattern, domain: domain))
        } while match(.comma)

        return vars
    }

    private func parseQuantifier(isForall: Bool) throws -> TLAExpression {
        let loc = currentLocation
        advance() // \A or \E

        let boundVars = try parseBoundVariables()

        guard match(.colon) else {
            throw error("Expected ':' after quantifier variables")
        }

        let body = try parseExpression()

        if isForall {
            return .forall(boundVars, body, loc)
        } else {
            return .exists(boundVars, body, loc)
        }
    }

    private func parseIfThenElse() throws -> TLAExpression {
        let loc = currentLocation
        advance() // IF

        let condition = try parseExpression()

        guard case .keyword(.then) = peek().type else {
            throw error("Expected 'THEN' after IF condition")
        }
        advance()

        let thenBranch = try parseExpression()

        guard case .keyword(.else_) = peek().type else {
            throw error("Expected 'ELSE' in IF expression")
        }
        advance()

        let elseBranch = try parseExpression()

        return .ternary(condition, thenBranch, elseBranch, loc)
    }

    private func parseLetIn() throws -> TLAExpression {
        let loc = currentLocation
        advance() // LET

        var definitions: [OperatorDefinition] = []

        // Parse at least one definition
        if case .identifier(_) = peek().type {
            guard case .operatorDef(let def) = try parseOperatorDefinition() else {
                throw error("Expected operator definition in LET")
            }
            definitions.append(def)
        } else {
            throw error("Expected at least one operator definition after LET")
        }

        // Parse remaining definitions
        while case .identifier(_) = peek().type {
            // Check that next token looks like a definition (has ==)
            if case .operator(.define) = peekNext().type {
                // Simple operator without parameters
            } else if case .leftParen = peekNext().type {
                // Operator with parameters
            } else {
                // Not a definition, probably part of IN body
                break
            }

            guard case .operatorDef(let def) = try parseOperatorDefinition() else {
                throw error("Expected operator definition in LET")
            }
            definitions.append(def)
        }

        guard case .keyword(.in_) = peek().type else {
            throw error("Expected 'IN' after LET definitions (found \(peek().lexeme))")
        }
        advance()

        let body = try parseExpression()

        return .letIn(definitions, body, loc)
    }

    private func parseCaseExpression() throws -> TLAExpression {
        let loc = currentLocation
        advance() // CASE

        var arms: [CaseArm] = []
        var other: TLAExpression? = nil

        repeat {
            if case .keyword(.other) = peek().type {
                advance()
                guard case .operator(.rightArrow) = peek().type else {
                    throw error("Expected '->' after OTHER")
                }
                advance()
                other = try parseExpression()
                break
            }

            let condition = try parseExpression()
            guard case .operator(.rightArrow) = peek().type else {
                throw error("Expected '->' in CASE arm")
            }
            advance()
            let result = try parseExpression()
            arms.append(CaseArm(condition: condition, result: result))
        } while match(.operator(.always)) // [] is the case separator (box operator)

        return .caseExpr(arms, other, loc)
    }

    private func parseChoose() throws -> TLAExpression {
        let loc = currentLocation
        advance() // CHOOSE

        guard case .identifier(let name) = peek().type else {
            throw error("Expected variable name after CHOOSE")
        }
        advance()

        var domain: TLAExpression? = nil
        if case .operator(.elementOf) = peek().type {
            advance()
            domain = try parseExpression()
        }

        guard match(.colon) else {
            throw error("Expected ':' after CHOOSE variable")
        }

        let predicate = try parseExpression()

        return .choose(BoundVariable(name: name, domain: domain), predicate, loc)
    }

    /// Parse LAMBDA expression: LAMBDA x, y, z : expr
    private func parseLambda() throws -> TLAExpression {
        let loc = currentLocation
        advance() // LAMBDA

        var parameters: [String] = []

        // Parse first parameter
        guard case .identifier(let firstName) = peek().type else {
            throw error("Expected parameter name after LAMBDA")
        }
        parameters.append(firstName)
        advance()

        // Parse remaining parameters
        while match(.comma) {
            guard case .identifier(let name) = peek().type else {
                throw error("Expected parameter name after ','")
            }
            parameters.append(name)
            advance()
        }

        guard match(.colon) else {
            throw error("Expected ':' after LAMBDA parameters")
        }

        let body = try parseExpression()

        return .lambda(parameters, body, loc)
    }

    private func parseExpressionList() throws -> [TLAExpression] {
        var expressions: [TLAExpression] = []

        if !check(.rightBracket) && !check(.rightParen) && !check(.rightBrace) {
            expressions.append(try parseExpression())
            while match(.comma) {
                expressions.append(try parseExpression())
            }
        }

        return expressions
    }

    // MARK: - Proof Parsing

    /// Check if the current position looks like a step marker (<level> or <level>number) without consuming tokens
    /// Formats: <1>1 (level 1, step 1), <1>2 (level 1, step 2), <1> QED (level 1, no step number)
    private func looksLikeStepNumber() -> Bool {
        guard case .operator(.lessThan) = peek().type else { return false }
        guard current + 1 < tokens.count, case .number(_) = tokens[current + 1].type else { return false }
        guard current + 2 < tokens.count, case .operator(.greaterThan) = tokens[current + 2].type else { return false }
        // Step number after > is optional (e.g., <1> QED is valid)
        return true
    }

    private func parseProof() throws -> TLAProof? {
        // Check recursion depth to prevent stack overflow
        proofDepth += 1
        defer { proofDepth -= 1 }

        guard proofDepth <= maxProofDepth else {
            throw error("Proof nesting too deep (max \(maxProofDepth) levels)")
        }

        let loc = currentLocation

        // Check for PROOF keyword (optional for simple proofs)
        let hasProofKeyword: Bool
        if case .keyword(.proof) = peek().type {
            advance()
            hasProofKeyword = true
        } else {
            hasProofKeyword = false
        }

        // OBVIOUS
        if case .keyword(.obvious) = peek().type {
            advance()
            return .obvious(loc)
        }

        // OMITTED
        if case .keyword(.omitted) = peek().type {
            advance()
            return .omitted(loc)
        }

        // BY facts DEF defs
        if case .keyword(.by) = peek().type {
            return try parseByProof(location: loc)
        }

        // Step-based proof (starts with <level>number pattern)
        // Use lookahead to verify this is actually a step number
        if looksLikeStepNumber() {
            let firstStepLoc = currentLocation  // Capture location BEFORE parsing step number
            let stepResult = try parseStepNumber()
            return try parseStepProof(firstStep: stepResult, firstStepLocation: firstStepLoc, location: loc)
        }

        // No proof found
        return hasProofKeyword ? .omitted(loc) : nil
    }

    private func parseByProof(location: SourceLocation) throws -> TLAProof {
        advance() // Skip BY

        var facts: [ProofFact] = []
        var defs: [String] = []

        // Parse facts (identifiers or step refs)
        if !isAtProofFactEnd() {
            facts.append(try parseProofFact())
            while match(.comma) {
                // Check for trailing comma before DEF or end
                if isAtProofFactEnd() {
                    break
                }
                facts.append(try parseProofFact())
            }
        }

        // Parse optional DEF clause
        if case .keyword(.def) = peek().type {
            advance()
            guard case .identifier(let defName) = peek().type else {
                throw error("Expected definition name after DEF")
            }
            defs.append(defName)
            advance()
            while match(.comma) {
                guard case .identifier(let name) = peek().type else {
                    throw error("Expected definition name")
                }
                defs.append(name)
                advance()
            }
        }

        return .by(facts: facts, defs: defs, location)
    }

    private func parseProofFact() throws -> ProofFact {
        let loc = currentLocation

        // Check for step reference like <1>2 using lookahead
        if looksLikeStepNumber() {
            let (level, number) = try parseStepNumber()
            return ProofFact(kind: .stepRef(level: level, number: number), location: loc)
        }

        guard case .identifier(let name) = peek().type else {
            throw error("Expected proof fact (identifier or step reference)")
        }
        advance()
        return ProofFact(kind: .identifier(name), location: loc)
    }

    /// Parse step number pattern: <level>number (e.g., <1>2, <2>1) or <level> (e.g., <1> QED)
    private func parseStepNumber() throws -> (level: Int, number: Int?) {
        guard case .operator(.lessThan) = peek().type else {
            throw error("Expected '<' in step number")
        }
        advance()

        guard case .number(let level) = peek().type else {
            throw error("Expected level number after '<'")
        }
        advance()

        guard case .operator(.greaterThan) = peek().type else {
            throw error("Expected '>' after level number")
        }
        advance()

        // Step number is optional (e.g., <1> QED is valid)
        if case .number(let number) = peek().type {
            advance()
            return (level, number)
        }

        return (level, nil)  // No step number (e.g., <1> QED)
    }

    private func parseStepProof(firstStep: (level: Int, number: Int?)?, firstStepLocation: SourceLocation?, location: SourceLocation) throws -> TLAProof {
        var steps: [TLAProofStep] = []

        // If we already parsed the first step number, use it
        if let first = firstStep {
            let stepLoc = firstStepLocation ?? currentLocation
            _ = match(.dot) // Optional period after step number
            let content = try parseStepContent()
            steps.append(TLAProofStep(
                level: first.level,
                number: first.number,
                content: content,
                location: stepLoc
            ))
        }

        // Parse remaining steps using lookahead to verify step numbers
        while looksLikeStepNumber() {
            let stepLoc = currentLocation

            let (level, number) = try parseStepNumber()

            _ = match(.dot) // Optional period after step number

            let content = try parseStepContent()
            steps.append(TLAProofStep(
                level: level,
                number: number,
                content: content,
                location: stepLoc
            ))
        }

        // Validate: step proofs should have at least one step
        if steps.isEmpty {
            throw error("Expected at least one proof step")
        }

        return .steps(steps, location)
    }

    private func parseStepContent() throws -> TLAProofStepContent {
        switch peek().type {
        case .keyword(.qed):
            advance()
            let proof = try parseProof()
            return .qed(proof)

        case .keyword(.suffices):
            return try parseSufficesStep()

        case .keyword(.take):
            return try parseTakeStep()

        case .keyword(.have):
            return try parseHaveStep()

        case .keyword(.witness):
            return try parseWitnessStep()

        case .keyword(.pick):
            return try parsePickStep()

        case .keyword(.use):
            return try parseUseStep()

        case .keyword(.hide):
            return try parseHideStep()

        case .keyword(.define):
            return try parseDefineStep()

        case .keyword(.case_):
            return try parseCaseProofStep()

        default:
            // Check for clearly unexpected tokens that can't start an assertion
            switch peek().type {
            case .eof, .moduleEnd:
                throw error("Unexpected end of input in proof step")
            case .rightParen, .rightBracket, .rightBrace:
                throw error("Unexpected closing delimiter in proof step")
            default:
                break
            }
            // Assertion step: expression followed by optional proof
            let expr = try parseExpression()
            let proof = try parseProof()
            return .assertion(expr, proof)
        }
    }

    private func parseSufficesStep() throws -> TLAProofStepContent {
        advance() // SUFFICES

        // Check for ASSUME keyword - if present, PROVE must follow
        if case .keyword(.assume) = peek().type {
            advance()
            let assumeExpr = try parseExpression()

            // ASSUME requires PROVE to follow
            guard case .keyword(.prove) = peek().type else {
                throw error("Expected PROVE after SUFFICES ASSUME")
            }
            advance()
            let proveExpr = try parseExpression()
            let proof = try parseProof()
            return .suffices(assume: assumeExpr, prove: proveExpr, proof)
        }

        // SUFFICES expr (shorthand - no ASSUME, just the thing to prove)
        let prove = try parseExpression()
        let proof = try parseProof()
        return .suffices(assume: nil, prove: prove, proof)
    }

    private func parseTakeStep() throws -> TLAProofStepContent {
        advance() // TAKE
        do {
            let vars = try parseBoundVariables()
            return .take(vars)
        } catch {
            throw self.error("Error in TAKE step: expected variable names (e.g., TAKE x \\in S)")
        }
    }

    private func parseHaveStep() throws -> TLAProofStepContent {
        advance() // HAVE
        let expr = try parseExpression()
        let proof = try parseProof()
        return .have(expr, proof)
    }

    private func parseWitnessStep() throws -> TLAProofStepContent {
        advance() // WITNESS
        var exprs: [TLAExpression] = [try parseExpression()]
        while match(.comma) {
            exprs.append(try parseExpression())
        }
        let proof = try parseProof()
        return .witness(exprs, proof)
    }

    private func parsePickStep() throws -> TLAProofStepContent {
        advance() // PICK
        let vars = try parseBoundVariables()
        guard match(.colon) else {
            throw error("Expected ':' after PICK variables")
        }
        let condition = try parseExpression()
        let proof = try parseProof()
        return .pick(vars, condition, proof)
    }

    private func parseUseStep() throws -> TLAProofStepContent {
        advance() // USE
        var facts: [ProofFact] = [try parseProofFact()]
        while match(.comma) {
            facts.append(try parseProofFact())
        }
        return .use(facts: facts)
    }

    private func parseHideStep() throws -> TLAProofStepContent {
        advance() // HIDE

        var defs: [String] = []
        var facts: [ProofFact] = []

        // Check if we have DEF keyword (HIDE DEF x, y, z)
        if case .keyword(.def) = peek().type {
            advance()
            guard case .identifier(let name) = peek().type else {
                throw error("Expected definition name after HIDE DEF")
            }
            defs.append(name)
            advance()
            while match(.comma) {
                guard case .identifier(let n) = peek().type else {
                    throw error("Expected definition name")
                }
                defs.append(n)
                advance()
            }
        } else {
            // HIDE fact1, fact2, ... (no DEF keyword)
            facts.append(try parseProofFact())
            while match(.comma) {
                facts.append(try parseProofFact())
            }
        }

        return .hide(defs: defs, facts: facts)
    }

    private func parseDefineStep() throws -> TLAProofStepContent {
        advance() // DEFINE
        var ops: [OperatorDefinition] = []
        while case .identifier(_) = peek().type {
            let startPos = current  // Track position to prevent infinite loop
            let decl = try parseOperatorDefinition()
            guard case .operatorDef(let def) = decl else {
                throw error("Expected operator definition in DEFINE, got \(type(of: decl))")
            }
            ops.append(def)
            // Safety check: ensure we made progress
            if current == startPos {
                throw error("Parser stuck in DEFINE block - no progress made")
            }
        }
        return .define(ops)
    }

    private func parseCaseProofStep() throws -> TLAProofStepContent {
        advance() // CASE
        let assumption = try parseExpression()
        let proof = try parseProof()
        return .caseStep(assumption, proof)
    }

    private func isAtProofFactEnd() -> Bool {
        switch peek().type {
        case .keyword(.def), .keyword(.qed), .keyword(.obvious), .keyword(.omitted),
             .keyword(.theorem), .keyword(.lemma), .keyword(.corollary), .keyword(.proposition),
             .keyword(.axiom), .keyword(.assume), .keyword(.assumption),
             .moduleEnd, .eof:
            return true
        default:
            return false
        }
        // Note: Step references like <1>2 are valid proof facts, so we don't
        // treat .operator(.lessThan) as an end marker
    }

    // MARK: - Helpers

    private var currentLocation: SourceLocation {
        let token = peek()
        return SourceLocation(line: token.line, column: token.column, length: token.length)
    }

    private func peek() -> TLAToken {
        guard current < tokens.count else {
            return TLAToken(type: .eof, lexeme: "", line: 0, column: 0, length: 0)
        }
        return tokens[current]
    }

    private func peekNext() -> TLAToken {
        guard current + 1 < tokens.count else {
            return TLAToken(type: .eof, lexeme: "", line: 0, column: 0, length: 0)
        }
        return tokens[current + 1]
    }

    private func previous() -> TLAToken {
        guard current > 0 else {
            // Return a dummy token if at start (shouldn't happen in normal flow)
            return TLAToken(type: .eof, lexeme: "", line: 0, column: 0, length: 0)
        }
        return tokens[current - 1]
    }

    private var isAtEnd: Bool {
        peek().type == .eof
    }

    @discardableResult
    private func advance() -> TLAToken {
        if !isAtEnd {
            current += 1
        }
        return previous()
    }

    private func check(_ type: TLATokenType) -> Bool {
        return peek().type == type
    }

    private func match(_ type: TLATokenType) -> Bool {
        if check(type) {
            advance()
            return true
        }
        return false
    }

    private func error(_ message: String) -> ParseError {
        return ParseError(message: message, location: currentLocation)
    }

    // MARK: - Error Recovery

    /// Synchronize to the next declaration boundary after an error
    /// This allows parsing to continue and collect multiple errors
    private func synchronize() {
        advance()

        while !isAtEnd {
            // Module end is a clear boundary
            if check(.moduleEnd) { return }

            // Declaration keywords indicate a new declaration
            switch peek().type {
            case .keyword(.constant), .keyword(.constants),
                 .keyword(.variable), .keyword(.variables),
                 .keyword(.theorem), .keyword(.lemma),
                 .keyword(.corollary), .keyword(.proposition),
                 .keyword(.assume), .keyword(.assumption),
                 .keyword(.axiom), .keyword(.instance),
                 .keyword(.recursive), .keyword(.local),
                 .keyword(.specification), .keyword(.invariant), .keyword(.property):
                return

            case .identifier:
                // Check if this looks like an operator definition (identifier followed by == or ()
                let next = peekNext()
                if case .operator(.define) = next.type {
                    return
                }
                if case .leftParen = next.type {
                    return
                }

            default:
                break
            }

            advance()
        }
    }

    /// Parse a declaration with error recovery - returns nil on error but continues parsing
    private func parseDeclarationWithRecovery() -> TLADeclaration? {
        do {
            return try parseDeclaration()
        } catch let parseError as ParseError {
            errors.append(parseError)
            synchronize()
            return nil
        } catch {
            errors.append(ParseError(message: error.localizedDescription, location: currentLocation))
            synchronize()
            return nil
        }
    }
}
