import Foundation

/// Interprets and evaluates TLA+ expressions
final class TLAInterpreter {
    /// Maximum recursion depth to prevent stack overflow
    private static let maxRecursionDepth = 1000

    /// Constant overrides from configuration
    private var constantOverrides: [String: TLAValue] = [:]

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
        if trimmed.hasPrefix("\"") && trimmed.hasSuffix("\"") {
            return .string(String(trimmed.dropFirst().dropLast()))
        }

        // Set enumeration: {a, b, c}
        if trimmed.hasPrefix("{") && trimmed.hasSuffix("}") {
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
        if trimmed.hasPrefix("<<") && trimmed.hasSuffix(">>") {
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

    struct Environment {
        var variables: [String: TLAValue]
        var constants: [String: TLAValue]
        var operators: [String: OperatorDefinition]
        var recursionDepth: Int

        init(
            variables: [String: TLAValue] = [:],
            constants: [String: TLAValue] = [:],
            operators: [String: OperatorDefinition] = [:],
            recursionDepth: Int = 0
        ) {
            self.variables = variables
            self.constants = constants
            self.operators = operators
            self.recursionDepth = recursionDepth
        }

        func binding(_ name: String, to value: TLAValue) -> Environment {
            var env = self
            env.variables[name] = value
            return env
        }

        /// Returns new environment with incremented recursion depth
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
        self.module = module
        var env = buildEnvironment(from: module)
        env.variables = state.variables

        // Find all possible next states
        var nextStates: [TLAState] = []

        // Extract primed variable assignments from Next
        let variables = Array(state.variables.keys)
        let possibleAssignments = generatePossibleAssignments(for: variables, env: env)

        for assignment in possibleAssignments {
            // Create environment with both current and primed variables
            var nextEnv = env
            for (name, value) in assignment {
                nextEnv.variables[name + "'"] = value
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
                nextStates.append(nextState)
            }
        }

        return nextStates
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

    func evaluate(_ expr: TLAExpression, in env: Environment) throws -> TLAValue {
        switch expr {
        case .identifier(let name, _):
            // Check for primed variable - name is already "x'" so just look it up
            if let value = env.variables[name] {
                return value
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
            return .set(Set((l...h).map { TLAValue.integer($0) }))

        case .functionApplication(let func_, let args, _):
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
                guard let primedValue = env.variables[name + "'"] else {
                    throw InterpreterError.evaluationError("UNCHANGED: primed variable '\(name)'' not defined in current context")
                }
                return .boolean(currentValue == primedValue)

            case .tuple(let elements, _):
                // UNCHANGED <<x, y, z>> checks all elements
                for element in elements {
                    if case .identifier(let name, _) = element {
                        let currentValue = try evaluate(element, in: env)
                        guard let primedValue = env.variables[name + "'"] else {
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
            guard let domain = boundVar.domain else {
                throw InterpreterError.evaluationError("CHOOSE requires a domain")
            }
            let domainVal = try evaluate(domain, in: env)
            guard case .set(let domainSet) = domainVal else {
                throw InterpreterError.typeMismatch(expected: "Set", got: "\(domainVal)")
            }

            for val in domainSet {
                var localEnv = env
                localEnv.variables[boundVar.name] = val
                let predVal = try evaluate(body, in: localEnv)
                if case .boolean(true) = predVal {
                    return val
                }
            }
            throw InterpreterError.evaluationError("CHOOSE: no value satisfies the predicate")

        case .functionConstruction(let boundVars, let body, _):
            // [x \in S |-> expr] - create a function
            guard let firstVar = boundVars.first,
                  let domain = firstVar.domain else {
                throw InterpreterError.evaluationError("Function construction requires a domain")
            }
            let domainVal = try evaluate(domain, in: env)
            guard case .set(let domainSet) = domainVal else {
                throw InterpreterError.typeMismatch(expected: "Set", got: "\(domainVal)")
            }

            var function: [TLAValue: TLAValue] = [:]
            for val in domainSet {
                var localEnv = env
                localEnv.variables[firstVar.name] = val
                let resultVal = try evaluate(body, in: localEnv)
                function[val] = resultVal
            }
            return .function(function)

        case .except(let base, let clauses, _):
            // [f EXCEPT ![x] = v] - functional update
            let baseVal = try evaluate(base, in: env)

            switch baseVal {
            case .function(var f):
                for clause in clauses {
                    guard let firstPath = clause.path.first else { continue }
                    let key = try evaluate(firstPath, in: env)
                    let value = try evaluate(clause.value, in: env)
                    f[key] = value
                }
                return .function(f)

            case .record(var r):
                for clause in clauses {
                    guard let firstPath = clause.path.first,
                          case .string(let field) = try evaluate(firstPath, in: env) else { continue }
                    let value = try evaluate(clause.value, in: env)
                    r[field] = value
                }
                return .record(r)

            case .sequence(var seq):
                for clause in clauses {
                    guard let firstPath = clause.path.first,
                          case .integer(let idx) = try evaluate(firstPath, in: env),
                          idx >= 1, idx <= seq.count else { continue }
                    let value = try evaluate(clause.value, in: env)
                    seq[idx - 1] = value
                }
                return .sequence(seq)

            default:
                throw InterpreterError.typeMismatch(expected: "Function/Record/Sequence", got: "\(baseVal)")
            }

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
                return .integer(l / r)
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
            var result: Set<TLAValue> = []
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

    private func evaluateForall(_ vars: [BoundVariable], _ body: TLAExpression, _ env: Environment) throws -> TLAValue {
        guard let firstVar = vars.first else {
            return try evaluate(body, in: env)
        }

        let domain = try getDomain(for: firstVar, in: env)
        let remainingVars = Array(vars.dropFirst())

        for value in domain {
            let newEnv = env.binding(firstVar.name, to: value)
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
            let newEnv = env.binding(firstVar.name, to: value)
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
        let currentVars = env.variables.keys.filter { !$0.hasSuffix("'") }

        // Generate possible assignments to primed variables
        // We use the same values as current state plus neighbors
        var possibleValues: Set<TLAValue> = []
        for (_, value) in env.variables {
            possibleValues.insert(value)
            // Add neighboring values for integers
            if case .integer(let n) = value {
                possibleValues.insert(.integer(n + 1))
                possibleValues.insert(.integer(n - 1))
            }
        }
        // Add common defaults
        possibleValues.insert(.boolean(true))
        possibleValues.insert(.boolean(false))
        possibleValues.insert(.integer(0))
        possibleValues.insert(.integer(1))

        let possibleValuesArray = Array(possibleValues)

        // Try all combinations of primed variable assignments
        func tryAssignments(vars: [String], currentEnv: Environment) -> Bool {
            guard let varName = vars.first else {
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

            let remaining = Array(vars.dropFirst())
            let primedName = varName + "'"

            for value in possibleValuesArray {
                var newEnv = currentEnv
                newEnv.variables[primedName] = value
                if tryAssignments(vars: remaining, currentEnv: newEnv) {
                    return true
                }
            }
            return false
        }

        let isEnabled = tryAssignments(vars: Array(currentVars), currentEnv: env)
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
            // Empty if m > n or out of bounds
            if m > n || m < 1 || n > seq.count {
                return .sequence([])
            }
            // Convert to 0-indexed: [m-1, n-1] inclusive = [m-1, n) in Swift
            return .sequence(Array(seq[(m-1)..<n]))

        case "SelectSeq":
            guard args.count == 2 else {
                throw InterpreterError.evaluationError("SelectSeq expects 2 arguments, got \(args.count)")
            }
            let seqVal = try evaluate(args[0], in: env)
            guard case .sequence(let seq) = seqVal else {
                throw InterpreterError.typeMismatch(expected: "Sequence", got: "\(seqVal)")
            }
            // SelectSeq(s, Test) filters elements where Test(e) is TRUE
            // The second arg must be an operator reference
            guard case .identifier(let testName, _) = args[1],
                  let testOp = env.operators[testName],
                  testOp.parameters.count == 1 else {
                throw InterpreterError.evaluationError("SelectSeq second argument must be a unary operator")
            }
            var result: [TLAValue] = []
            for elem in seq {
                var testEnv = try env.incrementingRecursion()
                testEnv.variables[testOp.parameterNames[0]] = elem
                let testResult = try evaluate(testOp.body, in: testEnv)
                if case .boolean(true) = testResult {
                    result.append(elem)
                }
            }
            return .sequence(result)

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
            var minVal: Int?
            for elem in s {
                guard case .integer(let i) = elem else {
                    throw InterpreterError.typeMismatch(expected: "Integer", got: "\(elem)")
                }
                if minVal == nil || i < minVal! {
                    minVal = i
                }
            }
            return .integer(minVal!)

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
            var maxVal: Int?
            for elem in s {
                guard case .integer(let i) = elem else {
                    throw InterpreterError.typeMismatch(expected: "Integer", got: "\(elem)")
                }
                if maxVal == nil || i > maxVal! {
                    maxVal = i
                }
            }
            return .integer(maxVal!)

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

    // MARK: - Helpers

    private func buildEnvironment(from module: TLAModule) -> Environment {
        var env = Environment()

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

        return env
    }

    private func addBuiltins(to env: inout Environment) {
        // Naturals - limited to prevent memory exhaustion, but large enough for most specs
        env.constants["Nat"] = .set(Set((0...1000).map { TLAValue.integer($0) }))
        env.constants["Int"] = .set(Set((-1000...1000).map { TLAValue.integer($0) }))

        // Booleans
        env.constants["BOOLEAN"] = .set([.boolean(true), .boolean(false)])
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
