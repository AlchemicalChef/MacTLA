import Foundation

/// Interprets and evaluates TLA+ expressions
final class TLAInterpreter {
    /// Maximum recursion depth to prevent stack overflow
    private static let maxRecursionDepth = 1000

    /// Constant overrides from configuration
    private var constantOverrides: [String: TLAValue] = [:]

    /// Upper bound for Nat (0..natUpperBound). Valid range: 0-100000
    var natUpperBound: Int = 1000 {
        didSet {
            if natUpperBound < 0 { natUpperBound = 0 }
            if natUpperBound > 100000 { natUpperBound = 100000 }
        }
    }

    /// Bound for Int (-intBound..intBound). Valid range: 0-100000
    var intBound: Int = 1000 {
        didSet {
            if intBound < 0 { intBound = 0 }
            if intBound > 100000 { intBound = 100000 }
        }
    }

    /// Maximum length for Seq(S) sequences. Valid range: 0-10
    var seqMaxLength: Int = 3 {
        didSet {
            if seqMaxLength < 0 { seqMaxLength = 0 }
            if seqMaxLength > 10 { seqMaxLength = 10 }
        }
    }

    /// Extracted variable domains from TypeOK or similar type invariants
    /// Used by ENABLED for exhaustive search over declared domains
    private var variableDomains: [String: TLAValue] = [:]

    /// Sets a constant value from configuration
    /// - Parameters:
    ///   - name: The constant name
    ///   - valueString: The value as a string (e.g., "3", "{a, b, c}", "<<1, 2, 3>>")
    func setConstant(name: String, valueString: String) {
        // Parse the value string into a TLAValue
        if let value = parseConstantValue(valueString) {
            constantOverrides[name] = value
        }
    }

    /// Loads a module's definitions into an environment
    /// This populates the environment with the module's operators, constants, and built-ins
    /// - Parameters:
    ///   - module: The TLA+ module to load
    ///   - env: The environment to populate (passed by reference)
    func loadModule(_ module: TLAModule, into env: inout Environment) throws {
        for decl in module.declarations {
            switch decl {
            case .operatorDef(let def):
                env.operators[def.name] = def
            case .constant(let constDecl):
                // Initialize constants - use override if available, otherwise model value
                for name in constDecl.names {
                    if let overrideValue = constantOverrides[name] {
                        env.constants[name] = overrideValue
                    } else {
                        env.constants[name] = .modelValue(name)
                    }
                }
            case .instance(let instanceDecl):
                // Handle INSTANCE declarations using ModuleRegistry
                do {
                    try ModuleRegistry.shared.instantiate(instanceDecl, into: &env, module: module)
                } catch {
                    // Log error but continue - standard modules are handled as built-ins
                    print("Warning: Could not instantiate module \(instanceDecl.moduleName): \(error)")
                }
            default:
                break
            }
        }

        // Add built-in operators
        addBuiltins(to: &env)

        // Extract variable domains from TypeOK for ENABLED exhaustive search
        extractVariableDomainsFromModule(module, env: env)
    }

    /// Parses a constant value string into a TLAValue
    private func parseConstantValue(_ str: String) -> TLAValue? {
        let trimmed = str.trimmingCharacters(in: .whitespaces)

        // Integer
        if let n = Int(trimmed) {
            return .integer(n)
        }

        // Boolean
        if trimmed == "TRUE" || trimmed == "true" {
            return .boolean(true)
        }
        if trimmed == "FALSE" || trimmed == "false" {
            return .boolean(false)
        }

        // String (quoted)
        if trimmed.hasPrefix("\"") && trimmed.hasSuffix("\"") && trimmed.count >= 2 {
            return .string(String(trimmed.dropFirst().dropLast()))
        }

        // Set enumeration: {a, b, c}
        if trimmed.hasPrefix("{") && trimmed.hasSuffix("}") && trimmed.count >= 2 {
            let inner = String(trimmed.dropFirst().dropLast())
            if inner.isEmpty {
                return .set([])
            }
            let elements = inner.components(separatedBy: ",").compactMap { elem -> TLAValue? in
                return parseConstantValue(elem.trimmingCharacters(in: .whitespaces))
            }
            return .set(Set(elements))
        }

        // Sequence: <<a, b, c>>
        if trimmed.hasPrefix("<<") && trimmed.hasSuffix(">>") && trimmed.count >= 4 {
            let inner = String(trimmed.dropFirst(2).dropLast(2))
            if inner.isEmpty {
                return .sequence([])
            }
            let elements = inner.components(separatedBy: ",").compactMap { elem -> TLAValue? in
                return parseConstantValue(elem.trimmingCharacters(in: .whitespaces))
            }
            return .sequence(elements)
        }

        // Range: m..n
        if trimmed.contains("..") {
            let parts = trimmed.components(separatedBy: "..")
            if parts.count == 2,
               let low = Int(parts[0].trimmingCharacters(in: .whitespaces)),
               let high = Int(parts[1].trimmingCharacters(in: .whitespaces)) {
                if low <= high {
                    return .set(Set((low...high).map { TLAValue.integer($0) }))
                } else {
                    return .set([])
                }
            }
        }

        // Model value (unquoted identifier)
        if trimmed.first?.isLetter == true {
            return .modelValue(trimmed)
        }

        return nil
    }

    /// Represents a successor state with the action that produced it
    struct SuccessorWithAction {
        let state: TLAState
        let actionName: String?
    }

    /// Evaluation environment for TLA+ expressions
    ///
    /// The `Environment` struct holds all the bindings needed to evaluate TLA+ expressions,
    /// including variable values, constant definitions, operator definitions, and primed
    /// variable values for action evaluation.
    ///
    /// ## Components
    /// - **Variables**: Current state variable bindings (e.g., `x = 5`)
    /// - **Constants**: Constant values from the specification or configuration
    /// - **Operators**: User-defined operator definitions from the module
    /// - **Primed Variables**: Next-state variable values for action constraint evaluation
    ///
    /// ## Usage
    /// ```swift
    /// // Create from a module
    /// let env = TLAInterpreter.Environment.from(module: myModule)
    ///
    /// // Add variable bindings
    /// var envWithVars = env
    /// envWithVars.variables["x"] = .integer(5)
    ///
    /// // Create with bound variable
    /// let newEnv = env.binding("y", to: .boolean(true))
    /// ```
    ///
    /// ## Thread Safety
    /// Environment is a value type (struct) and is safe to copy and modify independently.
    struct Environment {
        /// Current state variable bindings
        var variables: [String: TLAValue]

        /// Constant values (from CONSTANT declarations or configuration)
        var constants: [String: TLAValue]

        /// Operator definitions from the module
        var operators: [String: OperatorDefinition]

        /// Current recursion depth for detecting infinite recursion
        var recursionDepth: Int

        /// Primed variable values for action constraint evaluation
        ///
        /// When evaluating action constraints or the Next relation, primed variables
        /// (e.g., `x'`) represent the values in the successor state.
        var primedVariables: [String: TLAValue]

        /// Creates a new environment with the specified bindings
        ///
        /// - Parameters:
        ///   - variables: Initial variable bindings (default: empty)
        ///   - constants: Constant value bindings (default: empty)
        ///   - operators: Operator definitions (default: empty)
        ///   - recursionDepth: Current recursion depth (default: 0)
        ///   - primedVariables: Primed variable bindings (default: empty)
        init(
            variables: [String: TLAValue] = [:],
            constants: [String: TLAValue] = [:],
            operators: [String: OperatorDefinition] = [:],
            recursionDepth: Int = 0,
            primedVariables: [String: TLAValue] = [:]
        ) {
            self.variables = variables
            self.constants = constants
            self.operators = operators
            self.recursionDepth = recursionDepth
            self.primedVariables = primedVariables
        }

        /// Creates a new environment with an additional variable binding
        ///
        /// - Parameters:
        ///   - name: The variable name to bind
        ///   - value: The value to bind to the variable
        /// - Returns: A new environment with the variable bound
        func binding(_ name: String, to value: TLAValue) -> Environment {
            var env = self
            env.variables[name] = value
            return env
        }

        /// Returns new environment with incremented recursion depth
        ///
        /// - Throws: `InterpreterError.evaluationError` if maximum recursion depth is exceeded
        /// - Returns: A new environment with recursion depth incremented by 1
        func incrementingRecursion() throws -> Environment {
            guard recursionDepth < TLAInterpreter.maxRecursionDepth else {
                throw InterpreterError.evaluationError("Maximum recursion depth (\(TLAInterpreter.maxRecursionDepth)) exceeded")
            }
            var env = self
            env.recursionDepth = recursionDepth + 1
            return env
        }
    }

    enum InterpreterError: Error, CustomStringConvertible {
        case undefinedVariable(String)
        case undefinedOperator(String)
        case typeMismatch(expected: String, got: String)
        case evaluationError(String)
        case notImplemented(String)

        var description: String {
            switch self {
            case .undefinedVariable(let name): return "Undefined variable: \(name)"
            case .undefinedOperator(let name): return "Undefined operator: \(name)"
            case .typeMismatch(let expected, let got): return "Type mismatch: expected \(expected), got \(got)"
            case .evaluationError(let msg): return "Evaluation error: \(msg)"
            case .notImplemented(let feature): return "Not implemented: \(feature)"
            }
        }
    }

    private var module: TLAModule?

    func evaluateInit(_ initDef: OperatorDefinition, module: TLAModule) throws -> [TLAState] {
        self.module = module
        let env = buildEnvironment(from: module)

        // For Init, we need to find all satisfying assignments
        // This is a simplified implementation that handles basic cases
        let variables = extractVariables(from: module)

        // Start with empty state and try to find satisfying assignments
        var states: [TLAState] = []

        // Simple case: Init is a conjunction of equalities
        if let assignments = tryExtractAssignments(from: initDef.body, env: env) {
            var state = TLAState(variables: [:])
            for (name, value) in assignments {
                state.variables[name] = value
            }
            states.append(state)
        } else {
            // Fall back to exhaustive search over small domains
            let possibleStates = generatePossibleStates(for: variables, env: env)
            for state in possibleStates {
                let stateEnv = env.binding(variables: state.variables)
                if let result = try? evaluate(initDef.body, in: stateEnv),
                   case .boolean(true) = result {
                    states.append(state)
                }
            }
        }

        return states
    }

    func evaluateNext(_ nextDef: OperatorDefinition, state: TLAState, module: TLAModule) throws -> [TLAState] {
        // Delegate to the version that tracks actions, discarding action info
        return try evaluateNextWithActions(nextDef, state: state, module: module).map { $0.state }
    }

    /// Evaluates Next and returns successor states with their action names (for fairness checking)
    func evaluateNextWithActions(_ nextDef: OperatorDefinition, state: TLAState, module: TLAModule) throws -> [SuccessorWithAction] {
        self.module = module
        var env = buildEnvironment(from: module)
        env.variables = state.variables

        // Find all possible next states with their action names
        var successors: [SuccessorWithAction] = []

        // Extract action names from Next (look for disjuncts that are operator references)
        let actionNames = extractActionNames(from: nextDef.body, module: module)

        // Extract primed variable assignments from Next
        let variables = Array(state.variables.keys)
        let possibleAssignments = generatePossibleAssignments(for: variables, env: env)

        for assignment in possibleAssignments {
            // Create environment with both current and primed variables
            var nextEnv = env
            nextEnv.primedVariables = [:]
            for (name, value) in assignment {
                nextEnv.variables[name + "'"] = value
                nextEnv.primedVariables[name] = value
            }

            // Check if Next predicate is satisfied
            if let result = try? evaluate(nextDef.body, in: nextEnv),
               case .boolean(true) = result {
                // Start with current state to preserve unmodified variables
                var nextState = TLAState(variables: state.variables)
                // Then apply the assignments (which may override some values)
                for (name, value) in assignment {
                    nextState.variables[name] = value
                }

                // Find which action(s) are satisfied for this transition
                let satisfiedAction = findSatisfiedAction(actionNames, env: nextEnv, module: module)

                successors.append(SuccessorWithAction(state: nextState, actionName: satisfiedAction))
            }
        }

        return successors
    }

    /// Extracts action names from a Next formula (typically a disjunction of actions)
    private func extractActionNames(from expr: TLAExpression, module: TLAModule) -> [String] {
        var names: [String] = []

        switch expr {
        case .binary(let left, .or, let right, _):
            // Next == Action1 \/ Action2 \/ ...
            names.append(contentsOf: extractActionNames(from: left, module: module))
            names.append(contentsOf: extractActionNames(from: right, module: module))

        case .identifier(let name, _):
            // Reference to an action operator
            if module.declarations.contains(where: {
                if case .operatorDef(let def) = $0 {
                    return def.name == name && def.parameters.isEmpty
                }
                return false
            }) {
                names.append(name)
            }

        case .stuttering(let formula, _, _):
            // [Next]_vars - extract from inner formula
            names.append(contentsOf: extractActionNames(from: formula, module: module))

        case .action(let formula, _, _):
            // <<Next>>_vars - extract from inner formula
            names.append(contentsOf: extractActionNames(from: formula, module: module))

        default:
            break
        }

        return names
    }

    /// Finds which action is satisfied in the given environment
    private func findSatisfiedAction(_ actionNames: [String], env: Environment, module: TLAModule) -> String? {
        for name in actionNames {
            if let def = env.operators[name] ?? findOperator(name, in: module) {
                if let result = try? evaluate(def.body, in: env),
                   case .boolean(true) = result {
                    return name
                }
            }
        }
        return nil
    }

    /// Finds an operator definition in the module
    private func findOperator(_ name: String, in module: TLAModule) -> OperatorDefinition? {
        for decl in module.declarations {
            if case .operatorDef(let def) = decl, def.name == name {
                return def
            }
        }
        return nil
    }

    func evaluateInvariant(_ invariant: OperatorDefinition, state: TLAState, module: TLAModule) throws -> Bool {
        self.module = module
        var env = buildEnvironment(from: module)
        env.variables = state.variables

        let result = try evaluate(invariant.body, in: env)

        guard case .boolean(let holds) = result else {
            throw InterpreterError.typeMismatch(expected: "Boolean", got: "\(result)")
        }

        return holds
    }

    // MARK: - Expression Evaluation

    /// Evaluates a TLA+ expression in the given environment.
    ///
    /// This is the core evaluation function that recursively processes TLA+ AST nodes
    /// and returns concrete `TLAValue` results. It supports all TLA+ expression forms
    /// including arithmetic, logical, set, sequence, record, and function operations.
    ///
    /// - Parameters:
    ///   - expr: The TLA+ expression AST node to evaluate
    ///   - env: The evaluation environment containing variable bindings, constants,
    ///          operator definitions, and primed variable values
    ///
    /// - Returns: The computed `TLAValue` result of the expression
    ///
    /// - Throws: `InterpreterError` if evaluation fails due to:
    ///   - Undefined variable or operator references
    ///   - Type mismatches (e.g., arithmetic on non-integers)
    ///   - Division by zero
    ///   - Recursion depth exceeded
    ///
    /// ## Supported Expression Types
    /// - Literals: integers, booleans, strings
    /// - Variables: identifier lookup, primed variables (`x'`)
    /// - Operators: unary, binary, user-defined
    /// - Quantifiers: `\A`, `\E`, `CHOOSE`
    /// - Sets: enumeration, comprehension, range, operations
    /// - Sequences: tuple construction, indexing
    /// - Records: construction, field access, EXCEPT
    /// - Functions: construction, application
    /// - Control flow: IF-THEN-ELSE, CASE, LET-IN
    func evaluate(_ expr: TLAExpression, in env: Environment) throws -> TLAValue {
        switch expr {
        case .identifier(let name, _):
            // Check for primed variable - name is already "x'" so look it up in primedVariables first
            if name.hasSuffix("'") {
                let baseName = String(name.dropLast())
                // First check primedVariables (for action constraint evaluation)
                if let value = env.primedVariables[baseName] {
                    return value
                }
                // Fall back to looking up the full name in variables (legacy behavior)
                if let value = env.variables[name] {
                    return value
                }
            } else {
                // Regular variable lookup
                if let value = env.variables[name] {
                    return value
                }
            }
            if let value = env.constants[name] {
                return value
            }
            if let op = env.operators[name], op.parameters.isEmpty {
                let recursiveEnv = try env.incrementingRecursion()
                return try evaluate(op.body, in: recursiveEnv)
            }
            throw InterpreterError.undefinedVariable(name)

        case .number(let n, _):
            return .integer(n)

        case .string(let s, _):
            return .string(s)

        case .boolean(let b, _):
            return .boolean(b)

        case .unary(let op, let operand, _):
            return try evaluateUnary(op, operand, env)

        case .binary(let left, let op, let right, _):
            return try evaluateBinary(left, op, right, env)

        case .ternary(let cond, let then, let else_, _):
            let condValue = try evaluate(cond, in: env)
            guard case .boolean(let b) = condValue else {
                throw InterpreterError.typeMismatch(expected: "Boolean", got: "\(condValue)")
            }
            return try evaluate(b ? then : else_, in: env)

        case .forall(let vars, let body, _):
            return try evaluateForall(vars, body, env)

        case .exists(let vars, let body, _):
            return try evaluateExists(vars, body, env)

        case .setEnumeration(let elements, _):
            var values: Set<TLAValue> = []
            for elem in elements {
                values.insert(try evaluate(elem, in: env))
            }
            return .set(values)

        case .setRange(let low, let high, _):
            let lowVal = try evaluate(low, in: env)
            let highVal = try evaluate(high, in: env)
            guard case .integer(let l) = lowVal,
                  case .integer(let h) = highVal else {
                throw InterpreterError.typeMismatch(expected: "Integer", got: "non-integer")
            }
            // TLA+ semantics: l..h is empty set when l > h
            if l > h {
                return .set([])
            }
            // Limit range size to prevent memory exhaustion
            let rangeSize = h - l + 1
            let maxRangeSize = 100_000
            guard rangeSize <= maxRangeSize else {
                throw InterpreterError.evaluationError("Set range \(l)..\(h) would create \(rangeSize) elements - limit is \(maxRangeSize)")
            }
            return .set(Set((l...h).map { TLAValue.integer($0) }))

        case .functionApplication(let func_, let args, _):
            // Check if this is a lambda application: (LAMBDA x : body)[arg]
            if case .lambda(let params, let body, _) = func_ {
                let argVals = try args.map { try evaluate($0, in: env) }
                guard argVals.count == params.count else {
                    throw InterpreterError.evaluationError("LAMBDA expects \(params.count) arguments, got \(argVals.count)")
                }
                var lambdaEnv = try env.incrementingRecursion()
                for (param, val) in zip(params, argVals) {
                    lambdaEnv.variables[param] = val
                }
                return try evaluate(body, in: lambdaEnv)
            }

            // Check if this is a built-in function from standard modules
            if case .identifier(let funcName, _) = func_ {
                if let builtinResult = try evaluateBuiltinFunction(funcName, args: args, in: env) {
                    return builtinResult
                }
            }

            // Check if this is an operator invocation
            if case .identifier(let opName, _) = func_,
               let opDef = env.operators[opName],
               !opDef.parameters.isEmpty {
                // Invoke the operator with arguments
                let argVals = try args.map { try evaluate($0, in: env) }
                guard argVals.count == opDef.parameters.count else {
                    throw InterpreterError.evaluationError("Operator \(opName) expects \(opDef.parameters.count) arguments, got \(argVals.count)")
                }
                var opEnv = try env.incrementingRecursion()
                for (param, val) in zip(opDef.parameterNames, argVals) {
                    opEnv.variables[param] = val
                }
                return try evaluate(opDef.body, in: opEnv)
            }

            let funcVal = try evaluate(func_, in: env)
            let argVals = try args.map { try evaluate($0, in: env) }

            // Create the key: single value for one arg, tuple for multiple args
            let key: TLAValue = argVals.count == 1 ? argVals[0] : .sequence(argVals)

            switch funcVal {
            case .function(let f):
                // Try exact key match first
                if let value = f[key] {
                    return value
                }
                // For single arg, also try tuple wrapper
                if argVals.count == 1, let value = f[.sequence(argVals)] {
                    return value
                }
                throw InterpreterError.evaluationError("Function application failed: key \(key) not found")
            case .sequence(let seq):
                if case .integer(let idx) = argVals.first, idx >= 1, idx <= seq.count {
                    return seq[idx - 1] // TLA+ sequences are 1-indexed
                }
                throw InterpreterError.evaluationError("Sequence index out of bounds")
            case .record(let r):
                if case .string(let field) = argVals.first, let value = r[field] {
                    return value
                }
                throw InterpreterError.evaluationError("Record field not found")
            default:
                throw InterpreterError.typeMismatch(expected: "Function/Sequence/Record", got: "\(funcVal)")
            }

        case .recordConstruction(let fields, _):
            var record: [String: TLAValue] = [:]
            for (name, expr) in fields {
                record[name] = try evaluate(expr, in: env)
            }
            return .record(record)

        case .tuple(let elements, _):
            return .sequence(try elements.map { try evaluate($0, in: env) })

        case .prime(let expr, _):
            // Handle primed expressions by looking up primed variables
            if case .identifier(let name, let loc) = expr {
                return try evaluate(.identifier(name + "'", loc), in: env)
            }
            throw InterpreterError.notImplemented("Complex primed expressions")

        case .unchanged(let expr, _):
            // UNCHANGED x means x' = x
            // UNCHANGED <<x, y, z>> means x' = x /\ y' = y /\ z' = z
            switch expr {
            case .identifier(let name, _):
                let currentValue = try evaluate(expr, in: env)
                // Look in primedVariables for next-state values, not variables with "'" suffix
                guard let primedValue = env.primedVariables[name] else {
                    throw InterpreterError.evaluationError("UNCHANGED: primed variable '\(name)'' not defined in current context")
                }
                return .boolean(currentValue == primedValue)

            case .tuple(let elements, _):
                // UNCHANGED <<x, y, z>> checks all elements
                for element in elements {
                    if case .identifier(let name, _) = element {
                        let currentValue = try evaluate(element, in: env)
                        // Look in primedVariables for next-state values
                        guard let primedValue = env.primedVariables[name] else {
                            throw InterpreterError.evaluationError("UNCHANGED: primed variable '\(name)'' not defined in current context")
                        }
                        if currentValue != primedValue {
                            return .boolean(false)
                        }
                    } else {
                        throw InterpreterError.notImplemented("UNCHANGED with non-identifier tuple elements")
                    }
                }
                return .boolean(true)

            default:
                throw InterpreterError.notImplemented("Complex UNCHANGED expressions")
            }

        case .letIn(let defs, let body, _):
            var newEnv = env
            for def in defs {
                if def.parameters.isEmpty {
                    // Parameterless definition - evaluate and store as variable for efficiency
                    let value = try evaluate(def.body, in: newEnv)
                    newEnv.variables[def.name] = value
                } else {
                    // Parameterized operator - store definition for later invocation
                    newEnv.operators[def.name] = def
                }
            }
            return try evaluate(body, in: newEnv)

        case .setComprehension(let boundVar, let predicate, _):
            // {x \in S : P(x)} - set of all x in domain where P(x) is true
            guard let domain = boundVar.domain else {
                throw InterpreterError.evaluationError("Set comprehension requires a domain")
            }
            let domainVal = try evaluate(domain, in: env)
            guard case .set(let domainSet) = domainVal else {
                throw InterpreterError.typeMismatch(expected: "Set", got: "\(domainVal)")
            }

            var result: Set<TLAValue> = []
            for val in domainSet {
                var localEnv = env
                localEnv.variables[boundVar.name] = val
                let predVal = try evaluate(predicate, in: localEnv)
                if case .boolean(true) = predVal {
                    result.insert(val)
                }
            }
            return .set(result)

        case .setMap(let mapExpr, let boundVar, _):
            // {f(x) : x \in S} - set of all f(x) for x in domain
            guard let domain = boundVar.domain else {
                throw InterpreterError.evaluationError("Set map requires a domain")
            }
            let domainVal = try evaluate(domain, in: env)
            guard case .set(let domainSet) = domainVal else {
                throw InterpreterError.typeMismatch(expected: "Set", got: "\(domainVal)")
            }

            var result: Set<TLAValue> = []
            for val in domainSet {
                var localEnv = env
                localEnv.variables[boundVar.name] = val
                let mappedVal = try evaluate(mapExpr, in: localEnv)
                result.insert(mappedVal)
            }
            return .set(result)

        case .choose(let boundVar, let body, _):
            // CHOOSE x \in S : P(x) - pick an arbitrary x satisfying P
            // Per TLA+ semantics, CHOOSE is a total function: if no value satisfies
            // the predicate, it returns an unspecified but deterministic value from the domain.
            guard let domain = boundVar.domain else {
                throw InterpreterError.evaluationError("CHOOSE requires a domain")
            }
            let domainVal = try evaluate(domain, in: env)
            guard case .set(let domainSet) = domainVal else {
                throw InterpreterError.typeMismatch(expected: "Set", got: "\(domainVal)")
            }

            // Sort domain for deterministic CHOOSE behavior
            // TLA+ CHOOSE must return the same value for the same input
            let sortedDomain = domainSet.sorted { $0.sortKey < $1.sortKey }

            // Empty domain is an error - CHOOSE requires at least one element
            guard let firstElement = sortedDomain.first else {
                throw InterpreterError.evaluationError("CHOOSE: domain is empty")
            }

            // Return first element (in sorted order) that satisfies the predicate
            for val in sortedDomain {
                let localEnv = try bindPattern(boundVar, value: val, in: env)
                let predVal = try evaluate(body, in: localEnv)
                if case .boolean(true) = predVal {
                    return val
                }
            }

            // Per TLA+ semantics: if no value satisfies P(x), return an unspecified
            // but deterministic value. We use the first element of the sorted domain.
            print("Warning: CHOOSE found no element satisfying predicate, returning first element of domain: \(firstElement)")
            return firstElement

        case .functionConstruction(let boundVars, let body, _):
            // [x \in S |-> expr] or [x \in S, y \in T |-> expr] - create a function
            guard !boundVars.isEmpty else {
                throw InterpreterError.evaluationError("Function construction requires at least one bound variable")
            }

            // Evaluate all domains
            var domains: [[TLAValue]] = []
            for bv in boundVars {
                guard let domainExpr = bv.domain else {
                    throw InterpreterError.evaluationError("Function construction requires a domain for each variable")
                }
                let domainVal = try evaluate(domainExpr, in: env)
                guard case .set(let domainSet) = domainVal else {
                    throw InterpreterError.typeMismatch(expected: "Set", got: "\(domainVal)")
                }
                domains.append(Array(domainSet))
            }

            // Single variable case - simple function
            if boundVars.count == 1 {
                var function: [TLAValue: TLAValue] = [:]
                for val in domains[0] {
                    let localEnv = try bindPattern(boundVars[0], value: val, in: env)
                    let resultVal = try evaluate(body, in: localEnv)
                    function[val] = resultVal
                }
                return .function(function)
            }

            // Multiple variables - function from tuples
            // Compute Cartesian product of domains
            var function: [TLAValue: TLAValue] = [:]
            let tuples = cartesianProduct(domains)
            for tuple in tuples {
                var localEnv = env
                for (bv, val) in zip(boundVars, tuple) {
                    localEnv = try bindPattern(bv, value: val, in: localEnv)
                }
                let key = TLAValue.sequence(tuple)  // Use tuple as key
                let resultVal = try evaluate(body, in: localEnv)
                function[key] = resultVal
            }
            return .function(function)

        case .functionSet(let domain, let codomain, _):
            // [S -> T] - the set of all functions from S to T
            let domainVal = try evaluate(domain, in: env)
            let codomainVal = try evaluate(codomain, in: env)
            guard case .set(let domainSet) = domainVal else {
                throw InterpreterError.typeMismatch(expected: "Set for domain", got: "\(domainVal)")
            }
            guard case .set(let codomainSet) = codomainVal else {
                throw InterpreterError.typeMismatch(expected: "Set for codomain", got: "\(codomainVal)")
            }

            // Generate all possible functions from domain to codomain
            // Size is |codomain|^|domain|
            let domainArray = Array(domainSet)
            let codomainArray = Array(codomainSet)

            if domainArray.isEmpty {
                // [{}-> T] = {<<>>} - the single empty function
                return .set([.function([:])])
            }

            // Limit size to prevent memory exhaustion
            let numFunctions = Int(pow(Double(codomainArray.count), Double(domainArray.count)))
            let maxFunctions = 10_000
            guard numFunctions <= maxFunctions else {
                throw InterpreterError.evaluationError("Function set [\(domainSet.count) -> \(codomainSet.count)] would create \(numFunctions) functions - limit is \(maxFunctions)")
            }

            // Generate all functions by iterating through all combinations
            var allFunctions: Set<TLAValue> = []

            func generateFunctions(index: Int, current: [TLAValue: TLAValue]) {
                if index == domainArray.count {
                    allFunctions.insert(.function(current))
                    return
                }
                for coVal in codomainArray {
                    var next = current
                    next[domainArray[index]] = coVal
                    generateFunctions(index: index + 1, current: next)
                }
            }

            generateFunctions(index: 0, current: [:])
            return .set(allFunctions)

        case .except(let base, let clauses, _):
            // [f EXCEPT ![x] = v] or [f EXCEPT ![x][y] = v] - functional update with nested paths
            var result = try evaluate(base, in: env)

            for clause in clauses {
                guard !clause.path.isEmpty else { continue }
                let value = try evaluate(clause.value, in: env)
                result = try applyExceptClause(to: result, path: clause.path, value: value, env: env)
            }

            return result

        case .recordAccess(let record, let field, _):
            let recordVal = try evaluate(record, in: env)
            guard case .record(let r) = recordVal else {
                throw InterpreterError.typeMismatch(expected: "Record", got: "\(recordVal)")
            }
            guard let value = r[field] else {
                throw InterpreterError.evaluationError("Record field '\(field)' not found")
            }
            return value

        case .caseExpr(let arms, let other, _):
            // CASE cond1 -> result1 [] cond2 -> result2 [] OTHER -> default
            for arm in arms {
                let condVal = try evaluate(arm.condition, in: env)
                if case .boolean(true) = condVal {
                    return try evaluate(arm.result, in: env)
                }
            }
            if let otherExpr = other {
                return try evaluate(otherExpr, in: env)
            }
            throw InterpreterError.evaluationError("CASE: no condition matched and no OTHER clause")

        // ENABLED operator - checks if action can be taken from current state
        case .enabled(let actionExpr, _):
            return try evaluateEnabled(actionExpr, in: env)

        // Other temporal operators - these require model checking context
        case .always, .eventually, .leadsto, .stuttering, .action, .weakFairness, .strongFairness:
            throw InterpreterError.notImplemented("Temporal operators require model checking context")

        default:
            throw InterpreterError.notImplemented("Expression type: \(expr)")
        }
    }

    private func evaluateUnary(_ op: TLAUnaryOp, _ operand: TLAExpression, _ env: Environment) throws -> TLAValue {
        let value = try evaluate(operand, in: env)

        switch op {
        case .not:
            guard case .boolean(let b) = value else {
                throw InterpreterError.typeMismatch(expected: "Boolean", got: "\(value)")
            }
            return .boolean(!b)

        case .negative:
            guard case .integer(let n) = value else {
                throw InterpreterError.typeMismatch(expected: "Integer", got: "\(value)")
            }
            return .integer(-n)

        case .domain:
            switch value {
            case .function(let f):
                return .set(Set(f.keys))
            case .sequence(let seq):
                return .set(Set((1...seq.count).map { TLAValue.integer($0) }))
            case .record(let r):
                return .set(Set(r.keys.map { TLAValue.string($0) }))
            default:
                throw InterpreterError.typeMismatch(expected: "Function/Sequence/Record", got: "\(value)")
            }

        case .subset:
            guard case .set(let s) = value else {
                throw InterpreterError.typeMismatch(expected: "Set", got: "\(value)")
            }
            // Limit PowerSet to sets of size 20 (2^20 = 1M subsets)
            guard s.count <= 20 else {
                throw InterpreterError.evaluationError("SUBSET of set with \(s.count) elements would generate \(1 << s.count) subsets - limit is 20 elements")
            }
            return .set(Set(powerSet(Array(s)).map { TLAValue.set(Set($0)) }))

        case .union:
            guard case .set(let s) = value else {
                throw InterpreterError.typeMismatch(expected: "Set", got: "\(value)")
            }
            var result: Set<TLAValue> = []
            for elem in s {
                guard case .set(let innerSet) = elem else {
                    throw InterpreterError.typeMismatch(expected: "Set of sets", got: "\(value)")
                }
                result.formUnion(innerSet)
            }
            return .set(result)
        }
    }

    private func evaluateBinary(_ left: TLAExpression, _ op: TLABinaryOp, _ right: TLAExpression, _ env: Environment) throws -> TLAValue {
        // Short-circuit evaluation for logical operators
        switch op {
        case .and:
            let leftVal = try evaluate(left, in: env)
            guard case .boolean(let l) = leftVal else {
                throw InterpreterError.typeMismatch(expected: "Boolean", got: "\(leftVal)")
            }
            if !l { return .boolean(false) }
            let rightVal = try evaluate(right, in: env)
            guard case .boolean(let r) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Boolean", got: "\(rightVal)")
            }
            return .boolean(r)

        case .or:
            let leftVal = try evaluate(left, in: env)
            guard case .boolean(let l) = leftVal else {
                throw InterpreterError.typeMismatch(expected: "Boolean", got: "\(leftVal)")
            }
            if l { return .boolean(true) }
            let rightVal = try evaluate(right, in: env)
            guard case .boolean(let r) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Boolean", got: "\(rightVal)")
            }
            return .boolean(r)

        case .implies:
            let leftVal = try evaluate(left, in: env)
            guard case .boolean(let l) = leftVal else {
                throw InterpreterError.typeMismatch(expected: "Boolean", got: "\(leftVal)")
            }
            if !l { return .boolean(true) }
            let rightVal = try evaluate(right, in: env)
            guard case .boolean(let r) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Boolean", got: "\(rightVal)")
            }
            return .boolean(r)

        default:
            break
        }

        let leftVal = try evaluate(left, in: env)
        let rightVal = try evaluate(right, in: env)

        switch op {
        case .eq:
            return .boolean(leftVal == rightVal)

        case .neq:
            return .boolean(leftVal != rightVal)

        case .lt, .le, .gt, .ge:
            guard case .integer(let l) = leftVal,
                  case .integer(let r) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Integer", got: "non-integer")
            }
            switch op {
            case .lt: return .boolean(l < r)
            case .le: return .boolean(l <= r)
            case .gt: return .boolean(l > r)
            case .ge: return .boolean(l >= r)
            default: throw InterpreterError.evaluationError("Unexpected comparison operator: \(op)")
            }

        case .plus, .minus, .times, .div, .mod, .exp:
            guard case .integer(let l) = leftVal,
                  case .integer(let r) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Integer", got: "non-integer")
            }
            switch op {
            case .plus: return .integer(l + r)
            case .minus: return .integer(l - r)
            case .times: return .integer(l * r)
            case .div:
                guard r != 0 else {
                    throw InterpreterError.evaluationError("Division by zero")
                }
                // TLA+ uses floor division (truncate toward negative infinity)
                // Swift's / truncates toward zero, so we need to adjust for negative results
                let quotient = l / r
                let remainder = l % r
                // Adjust when signs differ and there's a remainder
                if remainder != 0 && (l < 0) != (r < 0) {
                    return .integer(quotient - 1)
                }
                return .integer(quotient)
            case .mod:
                guard r != 0 else {
                    throw InterpreterError.evaluationError("Modulo by zero")
                }
                // TLA+ modulo always returns non-negative result in range [0, |r|)
                // Swift's % can return negative values, so we need to adjust
                let result = l % r
                return .integer(result >= 0 ? result : result + abs(r))
            case .exp:
                // Integer-only exponentiation to preserve precision (TLA+ spec compliance)
                if r < 0 {
                    throw InterpreterError.evaluationError("Negative exponent not supported for integers")
                }
                // Use binary exponentiation for efficiency and overflow checking
                let result = integerPower(base: l, exponent: r)
                guard let value = result else {
                    throw InterpreterError.evaluationError("Exponentiation overflow: \(l)^\(r)")
                }
                return .integer(value)
            default: throw InterpreterError.evaluationError("Unexpected arithmetic operator: \(op)")
            }

        case .elementOf:
            guard case .set(let s) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Set", got: "\(rightVal)")
            }
            return .boolean(s.contains(leftVal))

        case .notElementOf:
            guard case .set(let s) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Set", got: "\(rightVal)")
            }
            return .boolean(!s.contains(leftVal))

        case .subsetOf:
            guard case .set(let l) = leftVal,
                  case .set(let r) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Set", got: "non-set")
            }
            return .boolean(l.isSubset(of: r))

        case .supersetOf:
            guard case .set(let l) = leftVal,
                  case .set(let r) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Set", got: "non-set")
            }
            return .boolean(r.isSubset(of: l))  // A \supseteq B iff B \subseteq A

        case .properSubset:
            guard case .set(let l) = leftVal,
                  case .set(let r) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Set", got: "non-set")
            }
            return .boolean(l.isStrictSubset(of: r))

        case .properSuperset:
            guard case .set(let l) = leftVal,
                  case .set(let r) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Set", got: "non-set")
            }
            return .boolean(r.isStrictSubset(of: l))  // A \supset B iff B \subset A

        case .setUnion:
            guard case .set(let l) = leftVal,
                  case .set(let r) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Set", got: "non-set")
            }
            return .set(l.union(r))

        case .setIntersect:
            guard case .set(let l) = leftVal,
                  case .set(let r) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Set", got: "non-set")
            }
            return .set(l.intersection(r))

        case .setMinus:
            guard case .set(let l) = leftVal,
                  case .set(let r) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Set", got: "non-set")
            }
            return .set(l.subtracting(r))

        case .cartesian:
            guard case .set(let l) = leftVal,
                  case .set(let r) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Set", got: "non-set")
            }
            // Limit Cartesian product size to prevent memory exhaustion
            let productSize = l.count * r.count
            let maxProductSize = 1_000_000
            guard productSize <= maxProductSize else {
                throw InterpreterError.evaluationError("Cartesian product of sets with \(l.count) and \(r.count) elements would create \(productSize) tuples - limit is \(maxProductSize)")
            }
            var result: Set<TLAValue> = []
            result.reserveCapacity(productSize)
            for a in l {
                for b in r {
                    result.insert(.sequence([a, b]))
                }
            }
            return .set(result)

        case .iff:
            guard case .boolean(let l) = leftVal,
                  case .boolean(let r) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Boolean", got: "non-boolean")
            }
            return .boolean(l == r)

        case .concat:
            // Sequence concatenation: s1 \o s2
            guard case .sequence(let s1) = leftVal,
                  case .sequence(let s2) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Sequence", got: "non-sequence")
            }
            return .sequence(s1 + s2)

        case .append:
            // Append element to sequence: Append(s, e)
            guard case .sequence(let s) = leftVal else {
                throw InterpreterError.typeMismatch(expected: "Sequence", got: "\(leftVal)")
            }
            return .sequence(s + [rightVal])

        case .compose:
            // Function composition: f @@ g (function override)
            guard case .function(let f) = leftVal,
                  case .function(let g) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Function", got: "non-function")
            }
            // f @@ g means: g overrides f (g's values take precedence)
            var result = f
            for (key, value) in g {
                result[key] = value
            }
            return .function(result)

        case .colonGreater:
            // TLC module: x :> y creates function [z \in {x} |-> y]
            // This is equivalent to (x :> y) = [z \in {x} |-> y]
            return .function([leftVal: rightVal])

        // Relational operators - return boolean for comparison
        case .prec, .preceq, .succ, .succeq:
            guard case .integer(let l) = leftVal,
                  case .integer(let r) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Integer", got: "non-integer")
            }
            switch op {
            case .prec: return .boolean(l < r)
            case .preceq: return .boolean(l <= r)
            case .succ: return .boolean(l > r)
            case .succeq: return .boolean(l >= r)
            default: throw InterpreterError.evaluationError("Unexpected precedence operator: \(op)")
            }

        // Similarity relations - these are user-defined in TLA+
        // Default implementation: structural equality (user should define custom semantics)
        case .sim, .simeq, .approx, .cong, .doteq, .propto, .asymp:
            // Note: These operators have no fixed semantics in TLA+
            // Treating as structural equality as a reasonable default
            return .boolean(leftVal == rightVal)

        // Square operators (lattice operations - treating as set operations)
        case .sqcap:
            guard case .set(let l) = leftVal,
                  case .set(let r) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Set", got: "non-set")
            }
            return .set(l.intersection(r))

        case .sqcup:
            guard case .set(let l) = leftVal,
                  case .set(let r) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Set", got: "non-set")
            }
            return .set(l.union(r))

        case .sqsubseteq:
            guard case .set(let l) = leftVal,
                  case .set(let r) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Set", got: "non-set")
            }
            return .boolean(l.isSubset(of: r))

        case .sqsupseteq:
            guard case .set(let l) = leftVal,
                  case .set(let r) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Set", got: "non-set")
            }
            return .boolean(r.isSubset(of: l))

        // Circle operators - these are user-defined in TLA+
        // Common interpretations: XOR, symmetric difference, modular arithmetic
        case .oplus:
            // ⊕ most commonly means XOR (for booleans/integers)
            if case .boolean(let l) = leftVal, case .boolean(let r) = rightVal {
                return .boolean(l != r) // Boolean XOR
            }
            guard case .integer(let l) = leftVal,
                  case .integer(let r) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Integer or Boolean", got: "other")
            }
            return .integer(l ^ r) // Bitwise XOR for integers

        case .ominus:
            // ⊖ symmetric difference for sets, or modular subtraction
            if case .set(let l) = leftVal, case .set(let r) = rightVal {
                return .set(l.symmetricDifference(r))
            }
            guard case .integer(let l) = leftVal,
                  case .integer(let r) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Integer or Set", got: "other")
            }
            return .integer(l - r)

        case .otimes:
            // ⊗ tensor/outer product - treating as multiplication
            guard case .integer(let l) = leftVal,
                  case .integer(let r) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Integer", got: "non-integer")
            }
            return .integer(l * r)

        case .oslash:
            guard case .integer(let l) = leftVal,
                  case .integer(let r) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Integer", got: "non-integer")
            }
            guard r != 0 else {
                throw InterpreterError.evaluationError("Circle division by zero")
            }
            return .integer(l / r)

        case .odot:
            // ⊙ dot product - treating as multiplication
            guard case .integer(let l) = leftVal,
                  case .integer(let r) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Integer", got: "non-integer")
            }
            return .integer(l * r)

        // Other mathematical operators
        case .cdot, .bullet:
            guard case .integer(let l) = leftVal,
                  case .integer(let r) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Integer", got: "non-integer")
            }
            return .integer(l * r) // Multiplication

        case .star:
            guard case .integer(let l) = leftVal,
                  case .integer(let r) = rightVal else {
                throw InterpreterError.typeMismatch(expected: "Integer", got: "non-integer")
            }
            return .integer(l * r) // Convolution/multiplication

        case .bigcirc, .wr:
            // These are typically domain-specific
            throw InterpreterError.notImplemented("Operator \(op) requires domain-specific semantics")

        default:
            throw InterpreterError.notImplemented("Binary operator: \(op)")
        }
    }

    /// Binds a value to a bound variable pattern in the environment
    /// For single patterns: binds the value to the name
    /// For tuple patterns: destructures the value and binds each element to its name
    private func bindPattern(_ boundVar: BoundVariable, value: TLAValue, in env: Environment) throws -> Environment {
        switch boundVar.pattern {
        case .single(let name):
            return env.binding(name, to: value)
        case .tuple(let names):
            // Value must be a sequence/tuple for pattern matching
            guard case .sequence(let elements) = value else {
                throw InterpreterError.typeMismatch(expected: "Sequence/Tuple for pattern <<\(names.joined(separator: ", "))>>", got: "\(value)")
            }
            guard elements.count == names.count else {
                throw InterpreterError.evaluationError("Tuple pattern has \(names.count) elements but value has \(elements.count)")
            }
            var newEnv = env
            for (name, element) in zip(names, elements) {
                newEnv = newEnv.binding(name, to: element)
            }
            return newEnv
        }
    }

    private func evaluateForall(_ vars: [BoundVariable], _ body: TLAExpression, _ env: Environment) throws -> TLAValue {
        guard let firstVar = vars.first else {
            return try evaluate(body, in: env)
        }

        let domain = try getDomain(for: firstVar, in: env)
        let remainingVars = Array(vars.dropFirst())

        for value in domain {
            let newEnv = try bindPattern(firstVar, value: value, in: env)
            let result: TLAValue
            if remainingVars.isEmpty {
                result = try evaluate(body, in: newEnv)
            } else {
                result = try evaluateForall(remainingVars, body, newEnv)
            }
            guard case .boolean(let b) = result else {
                throw InterpreterError.typeMismatch(expected: "Boolean", got: "\(result)")
            }
            if !b { return .boolean(false) }
        }

        return .boolean(true)
    }

    private func evaluateExists(_ vars: [BoundVariable], _ body: TLAExpression, _ env: Environment) throws -> TLAValue {
        guard let firstVar = vars.first else {
            return try evaluate(body, in: env)
        }

        let domain = try getDomain(for: firstVar, in: env)
        let remainingVars = Array(vars.dropFirst())

        for value in domain {
            let newEnv = try bindPattern(firstVar, value: value, in: env)
            let result: TLAValue
            if remainingVars.isEmpty {
                result = try evaluate(body, in: newEnv)
            } else {
                result = try evaluateExists(remainingVars, body, newEnv)
            }
            guard case .boolean(let b) = result else {
                throw InterpreterError.typeMismatch(expected: "Boolean", got: "\(result)")
            }
            if b { return .boolean(true) }
        }

        return .boolean(false)
    }

    /// Evaluates ENABLED action - checks if action can be taken from current state
    /// An action is enabled if there exists some assignment to primed variables
    /// that makes the action predicate true.
    private func evaluateEnabled(_ actionExpr: TLAExpression, in env: Environment) throws -> TLAValue {
        // Get current variable names (non-primed)
        let currentVars = Array(env.variables.keys.filter { !$0.hasSuffix("'") })

        // Build per-variable domain maps for exhaustive search
        // Use extracted domains from TypeOK when available
        var varDomains: [String: [TLAValue]] = [:]
        var totalSearchSpace = 1
        let maxSearchSpace = 100_000  // Limit to prevent memory explosion

        for varName in currentVars {
            if let domain = variableDomains[varName], case .set(let domainSet) = domain {
                // Use extracted domain from TypeOK
                varDomains[varName] = Array(domainSet)
                totalSearchSpace *= max(1, domainSet.count)
            } else {
                // Fallback: use current value + neighbors + defaults
                var fallbackValues: Set<TLAValue> = [
                    .boolean(true), .boolean(false),
                    .integer(0), .integer(1)
                ]
                if let currentValue = env.variables[varName] {
                    fallbackValues.insert(currentValue)
                    if case .integer(let n) = currentValue {
                        fallbackValues.insert(.integer(n + 1))
                        fallbackValues.insert(.integer(n - 1))
                    }
                }
                varDomains[varName] = Array(fallbackValues)
                totalSearchSpace *= fallbackValues.count
            }

            // Check search space limit after each variable
            if totalSearchSpace > maxSearchSpace {
                throw InterpreterError.evaluationError(
                    "ENABLED search space too large (\(totalSearchSpace) states) - consider smaller TypeOK domains"
                )
            }
        }

        // Try all combinations of primed variable assignments
        func tryAssignments(varIndex: Int, currentEnv: Environment) -> Bool {
            guard varIndex < currentVars.count else {
                // All primed variables assigned, evaluate the action
                do {
                    let result = try evaluate(actionExpr, in: currentEnv)
                    if case .boolean(true) = result {
                        return true
                    }
                } catch {
                    // Action threw error with this assignment - not enabled
                }
                return false
            }

            let varName = currentVars[varIndex]
            let primedName = varName + "'"
            let domain = varDomains[varName] ?? []

            for value in domain {
                var newEnv = currentEnv
                newEnv.variables[primedName] = value
                newEnv.primedVariables[varName] = value  // Sync for UNCHANGED support
                if tryAssignments(varIndex: varIndex + 1, currentEnv: newEnv) {
                    return true
                }
            }
            return false
        }

        let isEnabled = tryAssignments(varIndex: 0, currentEnv: env)
        return .boolean(isEnabled)
    }

    // MARK: - Integer Arithmetic Helpers

    /// Integer-only exponentiation using binary exponentiation algorithm.
    /// Returns nil on overflow instead of using floating-point.
    private func integerPower(base: Int, exponent: Int) -> Int? {
        guard exponent >= 0 else { return nil }
        if exponent == 0 { return 1 }
        if base == 0 { return 0 }
        if base == 1 { return 1 }
        if base == -1 { return exponent % 2 == 0 ? 1 : -1 }

        var result = 1
        var base = base
        var exp = exponent

        // Binary exponentiation with overflow checking
        while exp > 0 {
            if exp % 2 == 1 {
                // Check for overflow before multiplication
                let (product, overflow) = result.multipliedReportingOverflow(by: base)
                if overflow { return nil }
                result = product
            }
            exp /= 2
            if exp > 0 {
                // Check for overflow before squaring
                let (squared, overflow) = base.multipliedReportingOverflow(by: base)
                if overflow { return nil }
                base = squared
            }
        }

        return result
    }

    // MARK: - Built-in Functions from Standard Modules

    /// Evaluates built-in functions from standard TLA+ modules (Sequences, FiniteSets, etc.)
    /// Returns nil if the function is not a built-in, allowing normal evaluation to continue.
    private func evaluateBuiltinFunction(_ name: String, args: [TLAExpression], in env: Environment) throws -> TLAValue? {
        switch name {
        // Sequences module
        case "Head":
            guard args.count == 1 else {
                throw InterpreterError.evaluationError("Head expects 1 argument, got \(args.count)")
            }
            let seqVal = try evaluate(args[0], in: env)
            guard case .sequence(let seq) = seqVal else {
                throw InterpreterError.typeMismatch(expected: "Sequence", got: "\(seqVal)")
            }
            guard !seq.isEmpty else {
                throw InterpreterError.evaluationError("Head of empty sequence is undefined")
            }
            return seq[0]

        case "Tail":
            guard args.count == 1 else {
                throw InterpreterError.evaluationError("Tail expects 1 argument, got \(args.count)")
            }
            let seqVal = try evaluate(args[0], in: env)
            guard case .sequence(let seq) = seqVal else {
                throw InterpreterError.typeMismatch(expected: "Sequence", got: "\(seqVal)")
            }
            guard !seq.isEmpty else {
                throw InterpreterError.evaluationError("Tail of empty sequence is undefined")
            }
            return .sequence(Array(seq.dropFirst()))

        case "Len":
            guard args.count == 1 else {
                throw InterpreterError.evaluationError("Len expects 1 argument, got \(args.count)")
            }
            let seqVal = try evaluate(args[0], in: env)
            guard case .sequence(let seq) = seqVal else {
                throw InterpreterError.typeMismatch(expected: "Sequence", got: "\(seqVal)")
            }
            return .integer(seq.count)

        case "Append":
            guard args.count == 2 else {
                throw InterpreterError.evaluationError("Append expects 2 arguments, got \(args.count)")
            }
            let seqVal = try evaluate(args[0], in: env)
            let elemVal = try evaluate(args[1], in: env)
            guard case .sequence(let seq) = seqVal else {
                throw InterpreterError.typeMismatch(expected: "Sequence", got: "\(seqVal)")
            }
            return .sequence(seq + [elemVal])

        case "SubSeq":
            guard args.count == 3 else {
                throw InterpreterError.evaluationError("SubSeq expects 3 arguments, got \(args.count)")
            }
            let seqVal = try evaluate(args[0], in: env)
            let mVal = try evaluate(args[1], in: env)
            let nVal = try evaluate(args[2], in: env)
            guard case .sequence(let seq) = seqVal else {
                throw InterpreterError.typeMismatch(expected: "Sequence", got: "\(seqVal)")
            }
            guard case .integer(let m) = mVal, case .integer(let n) = nVal else {
                throw InterpreterError.typeMismatch(expected: "Integer", got: "non-integer")
            }
            // TLA+ SubSeq(s, m, n) returns s[m..n] (1-indexed, inclusive)
            // Per TLA+ semantics:
            // - If m < 1, undefined (we throw an error)
            // - If m > n, returns <<>>
            // - If n > Len(s), clamp to Len(s)
            // - If m > Len(s), returns <<>>
            if m < 1 {
                throw InterpreterError.evaluationError("SubSeq: starting index m must be >= 1, got \(m)")
            }
            if m > n {
                return .sequence([])
            }
            let clampedN = min(n, seq.count)
            if m > seq.count {
                return .sequence([])
            }
            // Convert to 0-indexed: [m-1, clampedN-1] inclusive = [m-1, clampedN) in Swift
            return .sequence(Array(seq[(m-1)..<clampedN]))

        case "SelectSeq":
            guard args.count == 2 else {
                throw InterpreterError.evaluationError("SelectSeq expects 2 arguments, got \(args.count)")
            }
            let seqVal = try evaluate(args[0], in: env)
            guard case .sequence(let seq) = seqVal else {
                throw InterpreterError.typeMismatch(expected: "Sequence", got: "\(seqVal)")
            }
            // SelectSeq(s, Test) filters elements where Test(e) is TRUE
            // Test can be either:
            // 1. An operator name (identifier)
            // 2. A LAMBDA expression
            var result: [TLAValue] = []

            if case .lambda(let params, let body, _) = args[1] {
                // LAMBDA expression
                guard params.count == 1 else {
                    throw InterpreterError.evaluationError("SelectSeq lambda must take exactly 1 parameter")
                }
                for elem in seq {
                    var testEnv = try env.incrementingRecursion()
                    testEnv.variables[params[0]] = elem
                    let testResult = try evaluate(body, in: testEnv)
                    if case .boolean(true) = testResult {
                        result.append(elem)
                    }
                }
            } else if case .identifier(let testName, _) = args[1],
                      let testOp = env.operators[testName],
                      testOp.parameters.count == 1 {
                // Operator reference
                for elem in seq {
                    var testEnv = try env.incrementingRecursion()
                    testEnv.variables[testOp.parameterNames[0]] = elem
                    let testResult = try evaluate(testOp.body, in: testEnv)
                    if case .boolean(true) = testResult {
                        result.append(elem)
                    }
                }
            } else {
                throw InterpreterError.evaluationError("SelectSeq second argument must be a unary operator or LAMBDA")
            }
            return .sequence(result)

        case "Seq":
            // Seq(S) - the set of all finite sequences with elements from S
            // NOTE: This is infinite in TLA+, but we bound it for model checking
            guard args.count == 1 else {
                throw InterpreterError.evaluationError("Seq expects 1 argument, got \(args.count)")
            }
            let setVal = try evaluate(args[0], in: env)
            guard case .set(let baseSet) = setVal else {
                throw InterpreterError.typeMismatch(expected: "Set", got: "\(setVal)")
            }

            // Generate sequences up to a bounded length (default: 3)
            // This is a common model checking approximation
            let maxSeqLen = seqMaxLength
            let elements = Array(baseSet)
            var seqSet: Set<TLAValue> = [.sequence([])]  // Empty sequence

            // Generate all sequences of length 1 to maxSeqLen
            for length in 1...maxSeqLen {
                let seqs = generateSequences(from: elements, length: length)
                for seq in seqs {
                    seqSet.insert(.sequence(seq))
                }
            }
            return .set(seqSet)

        case "First":
            // First(s) == Head(s) - first element of sequence (alias)
            guard args.count == 1 else {
                throw InterpreterError.evaluationError("First expects 1 argument, got \(args.count)")
            }
            let seqVal = try evaluate(args[0], in: env)
            guard case .sequence(let seq) = seqVal else {
                throw InterpreterError.typeMismatch(expected: "Sequence", got: "\(seqVal)")
            }
            guard !seq.isEmpty else {
                throw InterpreterError.evaluationError("First of empty sequence is undefined")
            }
            return seq[0]

        case "Last":
            // Last(s) - last element of sequence
            guard args.count == 1 else {
                throw InterpreterError.evaluationError("Last expects 1 argument, got \(args.count)")
            }
            let seqVal = try evaluate(args[0], in: env)
            guard case .sequence(let seq) = seqVal else {
                throw InterpreterError.typeMismatch(expected: "Sequence", got: "\(seqVal)")
            }
            guard !seq.isEmpty else {
                throw InterpreterError.evaluationError("Last of empty sequence is undefined")
            }
            return seq[seq.count - 1]

        case "Front":
            // Front(s) - all but last element
            guard args.count == 1 else {
                throw InterpreterError.evaluationError("Front expects 1 argument, got \(args.count)")
            }
            let seqVal = try evaluate(args[0], in: env)
            guard case .sequence(let seq) = seqVal else {
                throw InterpreterError.typeMismatch(expected: "Sequence", got: "\(seqVal)")
            }
            guard !seq.isEmpty else {
                throw InterpreterError.evaluationError("Front of empty sequence is undefined")
            }
            return .sequence(Array(seq.dropLast()))

        case "Reverse":
            // Reverse(s) - reverse sequence order
            guard args.count == 1 else {
                throw InterpreterError.evaluationError("Reverse expects 1 argument, got \(args.count)")
            }
            let seqVal = try evaluate(args[0], in: env)
            guard case .sequence(let seq) = seqVal else {
                throw InterpreterError.typeMismatch(expected: "Sequence", got: "\(seqVal)")
            }
            return .sequence(seq.reversed())

        case "Range":
            // Range(f) - the range (image) of a function
            guard args.count == 1 else {
                throw InterpreterError.evaluationError("Range expects 1 argument, got \(args.count)")
            }
            let funcVal = try evaluate(args[0], in: env)
            guard case .function(let f) = funcVal else {
                throw InterpreterError.typeMismatch(expected: "Function", got: "\(funcVal)")
            }
            return .set(Set(f.values))

        case "Min":
            // Min(S) - minimum element of a set of integers
            guard args.count == 1 else {
                throw InterpreterError.evaluationError("Min expects 1 argument, got \(args.count)")
            }
            let setVal = try evaluate(args[0], in: env)
            guard case .set(let s) = setVal else {
                throw InterpreterError.typeMismatch(expected: "Set", got: "\(setVal)")
            }
            guard !s.isEmpty else {
                throw InterpreterError.evaluationError("Min of empty set is undefined")
            }
            var minVal: Int = Int.max
            for elem in s {
                guard case .integer(let i) = elem else {
                    throw InterpreterError.typeMismatch(expected: "Integer", got: "\(elem)")
                }
                minVal = min(minVal, i)
            }
            return .integer(minVal)

        case "Max":
            // Max(S) - maximum element of a set of integers
            guard args.count == 1 else {
                throw InterpreterError.evaluationError("Max expects 1 argument, got \(args.count)")
            }
            let setVal = try evaluate(args[0], in: env)
            guard case .set(let s) = setVal else {
                throw InterpreterError.typeMismatch(expected: "Set", got: "\(setVal)")
            }
            guard !s.isEmpty else {
                throw InterpreterError.evaluationError("Max of empty set is undefined")
            }
            var maxVal: Int = Int.min
            for elem in s {
                guard case .integer(let i) = elem else {
                    throw InterpreterError.typeMismatch(expected: "Integer", got: "\(elem)")
                }
                maxVal = max(maxVal, i)
            }
            return .integer(maxVal)

        case "ToString":
            // ToString(v) - convert value to string representation
            guard args.count == 1 else {
                throw InterpreterError.evaluationError("ToString expects 1 argument, got \(args.count)")
            }
            let val = try evaluate(args[0], in: env)
            return .string("\(val)")

        // FiniteSets module
        case "Cardinality":
            guard args.count == 1 else {
                throw InterpreterError.evaluationError("Cardinality expects 1 argument, got \(args.count)")
            }
            let setVal = try evaluate(args[0], in: env)
            guard case .set(let s) = setVal else {
                throw InterpreterError.typeMismatch(expected: "Set", got: "\(setVal)")
            }
            return .integer(s.count)

        case "IsFiniteSet":
            guard args.count == 1 else {
                throw InterpreterError.evaluationError("IsFiniteSet expects 1 argument, got \(args.count)")
            }
            let setVal = try evaluate(args[0], in: env)
            guard case .set(_) = setVal else {
                throw InterpreterError.typeMismatch(expected: "Set", got: "\(setVal)")
            }
            // In our implementation all sets are finite
            return .boolean(true)

        // TLC module
        case "Print":
            guard args.count == 2 else {
                throw InterpreterError.evaluationError("Print expects 2 arguments, got \(args.count)")
            }
            let outVal = try evaluate(args[0], in: env)
            let retVal = try evaluate(args[1], in: env)
            // Print outputs first arg and returns second arg
            print("TLC Print: \(outVal)")
            return retVal

        case "PrintT":
            guard args.count == 1 else {
                throw InterpreterError.evaluationError("PrintT expects 1 argument, got \(args.count)")
            }
            let outVal = try evaluate(args[0], in: env)
            print("TLC PrintT: \(outVal)")
            return .boolean(true)

        case "Assert":
            guard args.count == 2 else {
                throw InterpreterError.evaluationError("Assert expects 2 arguments, got \(args.count)")
            }
            let condVal = try evaluate(args[0], in: env)
            guard case .boolean(let cond) = condVal else {
                throw InterpreterError.typeMismatch(expected: "Boolean", got: "\(condVal)")
            }
            if !cond {
                let msgVal = try evaluate(args[1], in: env)
                throw InterpreterError.evaluationError("Assertion failed: \(msgVal)")
            }
            return .boolean(true)

        default:
            // Not a built-in function
            return nil
        }
    }

    private func getDomain(for boundVar: BoundVariable, in env: Environment) throws -> [TLAValue] {
        guard let domainExpr = boundVar.domain else {
            throw InterpreterError.evaluationError("Bound variable \(boundVar.name) has no domain")
        }

        let domainVal = try evaluate(domainExpr, in: env)
        guard case .set(let s) = domainVal else {
            throw InterpreterError.typeMismatch(expected: "Set", got: "\(domainVal)")
        }

        // Sort for deterministic iteration order (Set iteration is undefined in Swift)
        return Array(s).sorted { $0.sortKey < $1.sortKey }
    }

    /// Computes the Cartesian product of multiple arrays
    /// cartesianProduct([[1,2], [3,4]]) = [[1,3], [1,4], [2,3], [2,4]]
    private func cartesianProduct(_ arrays: [[TLAValue]]) -> [[TLAValue]] {
        guard !arrays.isEmpty else { return [[]] }
        guard arrays.count > 1 else { return arrays[0].map { [$0] } }

        var result: [[TLAValue]] = [[]]
        for array in arrays {
            var newResult: [[TLAValue]] = []
            for existing in result {
                for element in array {
                    newResult.append(existing + [element])
                }
            }
            result = newResult
        }
        return result
    }

    /// Generates all sequences of a given length from a set of elements
    private func generateSequences(from elements: [TLAValue], length: Int) -> [[TLAValue]] {
        guard length > 0 else { return [[]] }
        guard !elements.isEmpty else { return [] }

        if length == 1 {
            return elements.map { [$0] }
        }

        var result: [[TLAValue]] = []
        let shorterSeqs = generateSequences(from: elements, length: length - 1)
        for seq in shorterSeqs {
            for elem in elements {
                result.append(seq + [elem])
            }
        }
        return result
    }

    // MARK: - Helpers

    /// Recursively applies an EXCEPT update through nested paths
    /// Supports [f EXCEPT ![x][y] = v] syntax for nested function/record/sequence updates
    private func applyExceptClause(
        to base: TLAValue,
        path: [TLAExpression],
        value: TLAValue,
        env: Environment,
        depth: Int = 0
    ) throws -> TLAValue {
        // Recursion depth protection
        guard depth < Self.maxRecursionDepth else {
            throw InterpreterError.evaluationError("EXCEPT: maximum nesting depth exceeded (\(Self.maxRecursionDepth))")
        }

        guard let firstKeyExpr = path.first else {
            // End of path - return the new value
            return value
        }

        let key = try evaluate(firstKeyExpr, in: env)
        let remainingPath = Array(path.dropFirst())

        switch base {
        case .function(var f):
            if remainingPath.isEmpty {
                // Last path element - update directly
                f[key] = value
            } else {
                // Recurse into nested structure
                guard let nested = f[key] else {
                    throw InterpreterError.evaluationError("EXCEPT: path not found for key \(key)")
                }
                f[key] = try applyExceptClause(to: nested, path: remainingPath, value: value, env: env, depth: depth + 1)
            }
            return .function(f)

        case .record(var r):
            guard case .string(let field) = key else {
                throw InterpreterError.typeMismatch(expected: "String key for record", got: "\(key)")
            }
            if remainingPath.isEmpty {
                r[field] = value
            } else {
                guard let nested = r[field] else {
                    throw InterpreterError.evaluationError("EXCEPT: field '\(field)' not found")
                }
                r[field] = try applyExceptClause(to: nested, path: remainingPath, value: value, env: env, depth: depth + 1)
            }
            return .record(r)

        case .sequence(var seq):
            guard case .integer(let idx) = key, idx >= 1, idx <= seq.count else {
                throw InterpreterError.evaluationError("EXCEPT: sequence index out of bounds")
            }
            if remainingPath.isEmpty {
                seq[idx - 1] = value
            } else {
                let nested = seq[idx - 1]
                seq[idx - 1] = try applyExceptClause(to: nested, path: remainingPath, value: value, env: env, depth: depth + 1)
            }
            return .sequence(seq)

        default:
            throw InterpreterError.typeMismatch(expected: "Function/Record/Sequence", got: "\(base)")
        }
    }

    private func buildEnvironment(from module: TLAModule) -> Environment {
        var env = Environment()
        // Use loadModule to populate the environment (reuses the same logic)
        try? loadModule(module, into: &env)
        return env
    }

    private func addBuiltins(to env: inout Environment) {
        // Naturals - limited to prevent memory exhaustion, configurable via natUpperBound
        env.constants["Nat"] = .set(Set((0...natUpperBound).map { TLAValue.integer($0) }))
        // Integers - configurable via intBound
        env.constants["Int"] = .set(Set((-intBound...intBound).map { TLAValue.integer($0) }))

        // Booleans
        env.constants["BOOLEAN"] = .set([.boolean(true), .boolean(false)])
    }

    /// Extracts variable domains from a type invariant like TypeOK
    /// TypeOK == x \in {0,1,2} /\ y \in BOOLEAN /\ z \in Nat
    /// Returns a dictionary mapping variable names to their domain sets
    private func extractDomainsFromTypeInvariant(_ expr: TLAExpression, env: Environment) -> [String: TLAValue] {
        var domains: [String: TLAValue] = [:]

        switch expr {
        case .binary(let left, .and, let right, _):
            // Conjunction: recurse on both sides
            let leftDomains = extractDomainsFromTypeInvariant(left, env: env)
            let rightDomains = extractDomainsFromTypeInvariant(right, env: env)
            domains.merge(leftDomains) { _, new in new }
            domains.merge(rightDomains) { _, new in new }

        case .binary(let left, .elementOf, let right, _):
            // x \in S - extract variable name and domain
            if case .identifier(let varName, _) = left {
                // Skip complex expressions that could cause combinatorial explosion
                // E.g., [S -> [S -> 0..500]] creates billions of entries
                if couldCauseExplosion(right) {
                    print("Info: Skipping domain extraction for '\(varName)' - complex expression could cause memory explosion")
                    break
                }

                // Try to evaluate the set expression
                do {
                    let domainValue = try evaluate(right, in: env)
                    if case .set(let s) = domainValue {
                        // Only store reasonably-sized domains
                        if s.count <= 100_000 {
                            domains[varName] = domainValue
                        } else {
                            print("Info: Skipping domain for '\(varName)' - set too large (\(s.count) elements)")
                        }
                    } else {
                        print("Warning: TypeOK domain for '\(varName)' is not a set: \(domainValue)")
                    }
                } catch {
                    print("Warning: Failed to extract TypeOK domain for '\(varName)': \(error)")
                }
            }

        default:
            // Other expressions (OR, implies, etc.) don't contribute to domain extraction
            // Log if we encounter complex patterns that might be TypeOK constraints
            break
        }

        return domains
    }

    /// Checks if an expression could cause combinatorial explosion when evaluated.
    /// This detects patterns like nested function constructions, large set ranges, etc.
    private func couldCauseExplosion(_ expr: TLAExpression) -> Bool {
        switch expr {
        case .functionConstruction(let boundVars, let body, _):
            // Nested function constructions are dangerous
            if containsFunctionConstruction(body) {
                return true
            }
            // Check if any domain is itself a function construction
            for bv in boundVars {
                if let domain = bv.domain, couldCauseExplosion(domain) {
                    return true
                }
            }
            // Large ranges in function domains are dangerous
            for bv in boundVars {
                if let domain = bv.domain, hasLargeRange(domain) {
                    return true
                }
            }
            return false

        case .binary(let left, .cartesian, let right, _):
            // Cartesian products can explode
            return couldCauseExplosion(left) || couldCauseExplosion(right)

        case .setRange(let start, let end, _):
            // Check if range is large
            if case .number(let s, _) = start, case .number(let e, _) = end {
                return abs(e - s) > 100
            }
            return false

        case .binary(let left, _, let right, _):
            // Check both sides of binary expressions
            return couldCauseExplosion(left) || couldCauseExplosion(right)

        case .unary(_, let operand, _):
            return couldCauseExplosion(operand)

        default:
            return false
        }
    }

    /// Checks if an expression contains a function construction (helper for explosion detection)
    private func containsFunctionConstruction(_ expr: TLAExpression) -> Bool {
        switch expr {
        case .functionConstruction:
            return true
        case .binary(let left, _, let right, _):
            return containsFunctionConstruction(left) || containsFunctionConstruction(right)
        case .unary(_, let operand, _):
            return containsFunctionConstruction(operand)
        case .ternary(let cond, let thenBr, let elseBr, _):
            return containsFunctionConstruction(cond) ||
                   containsFunctionConstruction(thenBr) ||
                   containsFunctionConstruction(elseBr)
        default:
            return false
        }
    }

    /// Checks if an expression contains a large set range (> 100 elements)
    private func hasLargeRange(_ expr: TLAExpression) -> Bool {
        switch expr {
        case .setRange(let start, let end, _):
            if case .number(let s, _) = start, case .number(let e, _) = end {
                return abs(e - s) > 100
            }
            return true // Conservatively assume large for non-literal ranges
        case .binary(let left, _, let right, _):
            return hasLargeRange(left) || hasLargeRange(right)
        case .identifier(let name, _):
            // Known large sets
            let largeBuiltins = ["Nat", "Int", "Real", "STRING"]
            return largeBuiltins.contains(name)
        default:
            return false
        }
    }

    /// Finds and extracts variable domains from TypeOK or TypeInvariant operator
    private func extractVariableDomainsFromModule(_ module: TLAModule, env: Environment) {
        // Look for TypeOK or TypeInvariant operator
        for decl in module.declarations {
            if case .operatorDef(let def) = decl {
                let name = def.name.lowercased()
                if name == "typeok" || name == "typeinvariant" || name == "typeinv" {
                    // Found a type invariant - extract domains from its body
                    let domains = extractDomainsFromTypeInvariant(def.body, env: env)
                    variableDomains.merge(domains) { _, new in new }
                }
            }
        }
    }

    private func extractVariables(from module: TLAModule) -> [String] {
        var vars: [String] = []
        for decl in module.declarations {
            if case .variable(let varDecl) = decl {
                vars.append(contentsOf: varDecl.names)
            }
        }
        return vars
    }

    private func tryExtractAssignments(from expr: TLAExpression, env: Environment) -> [(String, TLAValue)]? {
        // Simple case: conjunction of equalities
        switch expr {
        case .binary(let left, .and, let right, _):
            guard let leftAssigns = tryExtractAssignments(from: left, env: env),
                  let rightAssigns = tryExtractAssignments(from: right, env: env) else {
                return nil
            }
            return leftAssigns + rightAssigns

        case .binary(let left, .eq, let right, _):
            if case .identifier(let name, _) = left {
                if let value = try? evaluate(right, in: env) {
                    return [(name, value)]
                }
            }
            if case .identifier(let name, _) = right {
                if let value = try? evaluate(left, in: env) {
                    return [(name, value)]
                }
            }
            return nil

        default:
            return nil
        }
    }

    private func generatePossibleStates(for variables: [String], env: Environment) -> [TLAState] {
        // Generate a small set of possible states for exhaustive search
        // This is a simplified implementation
        let defaultValues: [TLAValue] = [
            .integer(0),
            .integer(1),
            .boolean(true),
            .boolean(false),
            .set([])
        ]

        var states: [TLAState] = [TLAState(variables: [:])]

        for variable in variables {
            var newStates: [TLAState] = []
            for state in states {
                for value in defaultValues {
                    var newState = state
                    newState.variables[variable] = value
                    newStates.append(newState)
                }
            }
            states = newStates
        }

        return states
    }

    private func generatePossibleAssignments(for variables: [String], env: Environment) -> [[String: TLAValue]] {
        // Similar to generatePossibleStates but for next-state generation
        let currentValues = variables.compactMap { env.variables[$0] }
        var possibleValues = Set(currentValues)

        // Add some neighboring values
        for value in currentValues {
            switch value {
            case .integer(let n):
                possibleValues.insert(.integer(n + 1))
                possibleValues.insert(.integer(n - 1))
            default:
                break
            }
        }

        var assignments: [[String: TLAValue]] = [[:]]

        for variable in variables {
            var newAssignments: [[String: TLAValue]] = []
            for assignment in assignments {
                for value in possibleValues {
                    var newAssignment = assignment
                    newAssignment[variable] = value
                    newAssignments.append(newAssignment)
                }
            }
            assignments = newAssignments
        }

        return assignments
    }

    private func powerSet<T>(_ array: [T]) -> [[T]] {
        guard !array.isEmpty else { return [[]] }
        let first = array[0]
        let rest = Array(array.dropFirst())
        let subsets = powerSet(rest)
        return subsets + subsets.map { [first] + $0 }
    }
}

// Extension for Environment
extension TLAInterpreter.Environment {
    func binding(variables: [String: TLAValue]) -> TLAInterpreter.Environment {
        var env = self
        for (name, value) in variables {
            env.variables[name] = value
        }
        return env
    }
}
