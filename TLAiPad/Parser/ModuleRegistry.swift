import Foundation

/// Registry for TLA+ modules, enabling INSTANCE declarations
/// Manages both standard library modules and user-defined modules
final class ModuleRegistry {
    static let shared = ModuleRegistry()

    /// Registered modules by name
    private var modules: [String: TLAModule] = [:]

    /// Standard library module names
    private static let standardModules: Set<String> = [
        "Naturals", "Integers", "Reals", "Sequences",
        "FiniteSets", "Bags", "TLC", "TLAPS"
    ]

    private init() {
        // Register standard library modules with their operator signatures
        registerStandardLibraries()
    }

    // MARK: - Public API

    /// Registers a module in the registry
    func register(_ module: TLAModule) {
        modules[module.name] = module
    }

    /// Resolves a module by name
    func resolve(_ name: String) -> TLAModule? {
        return modules[name]
    }

    /// Checks if a module is a standard library module
    func isStandardModule(_ name: String) -> Bool {
        return Self.standardModules.contains(name)
    }

    /// Instantiates a module with substitutions into an environment
    /// - Parameters:
    ///   - instance: The INSTANCE declaration
    ///   - env: The environment to modify
    /// - Returns: Updated environment with imported operators
    func instantiate(
        _ instance: InstanceDeclaration,
        into env: inout TLAInterpreter.Environment,
        module: TLAModule
    ) throws {
        guard let targetModule = resolve(instance.moduleName) else {
            // For standard modules, operators are built-in - just mark as instantiated
            if isStandardModule(instance.moduleName) {
                return // Built-in functions are already available
            }
            throw ModuleRegistryError.undefinedModule(instance.moduleName)
        }

        // Apply substitutions and import operators
        let prefix = instance.name.map { "\($0)!" } ?? ""

        for decl in targetModule.declarations {
            switch decl {
            case .operatorDef(let def):
                // Apply substitutions to the operator body if needed
                var newDef = def
                if !instance.substitutions.isEmpty {
                    newDef = applySubstitutions(to: def, substitutions: instance.substitutions)
                }
                // Register with optional prefix
                env.operators[prefix + def.name] = newDef

            case .constant(let constDecl):
                // Apply constant substitutions
                for name in constDecl.names {
                    if let sub = instance.substitutions.first(where: { $0.parameter == name }) {
                        // Substitution provided - evaluate expression to get string representation
                        // For now, use the expression's description as a placeholder
                        env.constants[prefix + name] = .modelValue(expressionToString(sub.expression))
                    } else {
                        // No substitution - use model value
                        env.constants[prefix + name] = .modelValue(name)
                    }
                }

            default:
                break
            }
        }
    }

    /// Converts a TLAExpression to a string representation for model values
    private func expressionToString(_ expr: TLAExpression) -> String {
        switch expr {
        case .identifier(let name, _):
            return name
        case .number(let n, _):
            return String(n)
        case .string(let s, _):
            return s
        case .boolean(let b, _):
            return b ? "TRUE" : "FALSE"
        default:
            return "expr"
        }
    }

    // MARK: - Standard Library Registration

    private func registerStandardLibraries() {
        // Note: Most standard library functions are implemented as built-ins
        // in TLAInterpreter.evaluateBuiltinFunction()
        // This registration is primarily for documentation and INSTANCE support

        // Naturals module
        let naturals = createStandardModule("Naturals", operators: [
            "Nat", // The set of natural numbers (0, 1, 2, ...)
        ])
        register(naturals)

        // Integers module
        let integers = createStandardModule("Integers", operators: [
            "Int", // The set of integers
        ])
        register(integers)

        // Sequences module
        let sequences = createStandardModule("Sequences", operators: [
            "Seq",      // Seq(S) - all sequences over S
            "Len",      // Len(s) - length of sequence
            "Head",     // Head(s) - first element
            "Tail",     // Tail(s) - all but first
            "Append",   // Append(s, e) - append element
            "SubSeq",   // SubSeq(s, m, n) - subsequence
            "SelectSeq", // SelectSeq(s, Test) - filter
        ])
        register(sequences)

        // FiniteSets module
        let finiteSets = createStandardModule("FiniteSets", operators: [
            "Cardinality",  // Cardinality(S) - size of set
            "IsFiniteSet",  // IsFiniteSet(S) - true if finite
        ])
        register(finiteSets)

        // TLC module
        let tlc = createStandardModule("TLC", operators: [
            "Print",    // Print(v, msg) - print and return
            "PrintT",   // PrintT(msg) - print and return TRUE
            "Assert",   // Assert(cond, msg) - assertion
        ])
        register(tlc)

        // Bags module
        let bags = createStandardModule("Bags", operators: [
            "BagToSet",     // BagToSet(B) - underlying set
            "SetToBag",     // SetToBag(S) - bag from set
            "BagIn",        // BagIn(e, B) - membership
            "EmptyBag",     // EmptyBag - empty bag
            "CopiesIn",     // CopiesIn(e, B) - count
            "BagUnion",     // BagUnion(B1, B2) - union
            "SubBag",       // SubBag(B1, B2) - subset
            "BagCardinality", // BagCardinality(B) - total count
        ])
        register(bags)

        // TLAPS module (proof system hints)
        let tlaps = createStandardModule("TLAPS", operators: [
            "BY",       // Proof step hint
            "OBVIOUS",  // Trivial proof
            "OMITTED",  // Skipped proof
        ])
        register(tlaps)
    }

    /// Creates a stub module for standard library
    private func createStandardModule(_ name: String, operators: [String]) -> TLAModule {
        var declarations: [TLADeclaration] = []

        for opName in operators {
            // Create a stub operator definition
            // The actual implementation is in evaluateBuiltinFunction
            let def = OperatorDefinition(
                name: opName,
                parameters: [], // Parameters handled dynamically
                body: .boolean(true, .unknown), // Stub body
                isRecursive: false,
                location: .unknown
            )
            declarations.append(.operatorDef(def))
        }

        return TLAModule(
            name: name,
            extends: [],
            declarations: declarations,
            location: .unknown
        )
    }

    // MARK: - Substitution Helpers

    /// Applies parameter substitutions to an operator definition
    private func applySubstitutions(
        to def: OperatorDefinition,
        substitutions: [InstanceDeclaration.Substitution]
    ) -> OperatorDefinition {
        // Create a mapping from old names to replacement expressions
        var exprMapping: [String: TLAExpression] = [:]
        for sub in substitutions {
            exprMapping[sub.parameter] = sub.expression
        }

        // Apply substitutions to the operator body
        let newBody = substituteInExpression(def.body, mapping: exprMapping)

        return OperatorDefinition(
            name: def.name,
            parameters: def.parameters,
            body: newBody,
            isRecursive: def.isRecursive,
            location: def.location
        )
    }

    /// Recursively substitutes identifiers in an expression
    private func substituteInExpression(
        _ expr: TLAExpression,
        mapping: [String: TLAExpression]
    ) -> TLAExpression {
        switch expr {
        case .identifier(let name, _):
            // If this identifier is in the mapping, replace it with the mapped expression
            if let replacement = mapping[name] {
                return replacement
            }
            return expr

        case .unary(let op, let operand, let loc):
            return .unary(op, substituteInExpression(operand, mapping: mapping), loc)

        case .binary(let left, let op, let right, let loc):
            return .binary(
                substituteInExpression(left, mapping: mapping),
                op,
                substituteInExpression(right, mapping: mapping),
                loc
            )

        case .ternary(let cond, let then, let else_, let loc):
            return .ternary(
                substituteInExpression(cond, mapping: mapping),
                substituteInExpression(then, mapping: mapping),
                substituteInExpression(else_, mapping: mapping),
                loc
            )

        case .functionApplication(let func_, let args, let loc):
            return .functionApplication(
                substituteInExpression(func_, mapping: mapping),
                args.map { substituteInExpression($0, mapping: mapping) },
                loc
            )

        case .setEnumeration(let elements, let loc):
            return .setEnumeration(
                elements.map { substituteInExpression($0, mapping: mapping) },
                loc
            )

        case .forall(let vars, let body, let loc):
            // Don't substitute bound variables
            let boundNames = Set(vars.map { $0.name })
            let filteredMapping = mapping.filter { !boundNames.contains($0.key) }
            let newVars = vars.map { v in
                BoundVariable(
                    name: v.name,
                    domain: v.domain.map { substituteInExpression($0, mapping: mapping) }
                )
            }
            return .forall(newVars, substituteInExpression(body, mapping: filteredMapping), loc)

        case .exists(let vars, let body, let loc):
            // Don't substitute bound variables
            let boundNames = Set(vars.map { $0.name })
            let filteredMapping = mapping.filter { !boundNames.contains($0.key) }
            let newVars = vars.map { v in
                BoundVariable(
                    name: v.name,
                    domain: v.domain.map { substituteInExpression($0, mapping: mapping) }
                )
            }
            return .exists(newVars, substituteInExpression(body, mapping: filteredMapping), loc)

        case .letIn(let defs, let body, let loc):
            // Process LET definitions and substitute in body
            let newDefs = defs.map { def in
                OperatorDefinition(
                    name: def.name,
                    parameters: def.parameters,
                    body: substituteInExpression(def.body, mapping: mapping),
                    isRecursive: def.isRecursive,
                    location: def.location
                )
            }
            return .letIn(newDefs, substituteInExpression(body, mapping: mapping), loc)

        case .recordConstruction(let fields, let loc):
            return .recordConstruction(
                fields.map { (name, expr) in
                    (name, substituteInExpression(expr, mapping: mapping))
                },
                loc
            )

        case .tuple(let elements, let loc):
            return .tuple(elements.map { substituteInExpression($0, mapping: mapping) }, loc)

        case .setRange(let low, let high, let loc):
            return .setRange(
                substituteInExpression(low, mapping: mapping),
                substituteInExpression(high, mapping: mapping),
                loc
            )

        // Add more cases as needed for complete substitution support

        default:
            return expr
        }
    }
}

// MARK: - Errors

enum ModuleRegistryError: Error, CustomStringConvertible {
    case undefinedModule(String)
    case substitutionError(String)

    var description: String {
        switch self {
        case .undefinedModule(let name):
            return "Undefined module: \(name)"
        case .substitutionError(let msg):
            return "Substitution error: \(msg)"
        }
    }
}
