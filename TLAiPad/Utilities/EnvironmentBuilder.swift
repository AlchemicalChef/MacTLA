import Foundation

// MARK: - TLAInterpreter.Environment Extensions

extension TLAInterpreter.Environment {
    /// Loads all operator definitions from a TLA+ module into the environment
    /// - Parameter module: The TLA+ module to load operators from
    mutating func loadOperators(from module: TLAModule) {
        for decl in module.declarations {
            if case .operatorDef(let def) = decl {
                operators[def.name] = def
            }
        }
    }

    /// Loads constants from a TLA+ module into the environment
    /// - Parameters:
    ///   - module: The TLA+ module to load constants from
    ///   - overrides: Optional constant value overrides
    mutating func loadConstants(from module: TLAModule, overrides: [String: TLAValue] = [:]) {
        for decl in module.declarations {
            if case .constant(let constDecl) = decl {
                for name in constDecl.names {
                    if let overrideValue = overrides[name] {
                        constants[name] = overrideValue
                    } else {
                        constants[name] = .modelValue(name)
                    }
                }
            }
        }
    }

    /// Creates an environment initialized from a TLA+ module
    /// - Parameters:
    ///   - module: The TLA+ module to initialize from
    ///   - constantOverrides: Optional constant value overrides
    /// - Returns: A new environment with operators and constants loaded
    static func from(module: TLAModule, constantOverrides: [String: TLAValue] = [:]) -> TLAInterpreter.Environment {
        var env = TLAInterpreter.Environment()
        env.loadOperators(from: module)
        env.loadConstants(from: module, overrides: constantOverrides)
        return env
    }

    /// Creates a copy of this environment with variables bound from a state
    /// - Parameter state: The TLA+ state to bind variables from
    /// - Returns: A new environment with variables bound
    func withVariables(from state: TLAState) -> TLAInterpreter.Environment {
        var env = self
        env.variables = state.variables
        return env
    }

    /// Creates a copy with primed variables set for action constraint evaluation
    /// - Parameter state: The state containing the primed (next) variable values
    /// - Returns: A new environment with primed variables set
    func withPrimedVariables(from state: TLAState) -> TLAInterpreter.Environment {
        var env = self
        env.primedVariables = state.variables
        return env
    }

    /// Convenience method to bind multiple variables at once
    /// - Parameter variables: Dictionary of variable names to values
    /// - Returns: A new environment with the variables bound
    func binding(variables: [String: TLAValue]) -> TLAInterpreter.Environment {
        var env = self
        for (name, value) in variables {
            env.variables[name] = value
        }
        return env
    }
}
