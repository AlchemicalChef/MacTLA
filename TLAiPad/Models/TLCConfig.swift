import Foundation

// MARK: - TLC Configuration Models

/// TLC model checker configuration
struct TLCConfig: Codable, Equatable {
    var initOperator: String = "Init"
    var nextOperator: String = "Next"
    var specificationOperator: String = ""
    var constants: [TLCConstant] = []
    var invariants: [TLCInvariant] = []
    var properties: [TLCProperty] = []
    var symmetrySets: [TLCSymmetrySet] = []
    var constraints: [TLCConstraint] = []           // State constraints (CONSTRAINT)
    var actionConstraints: [TLCActionConstraint] = [] // Action constraints (ACTION_CONSTRAINT)
    var view: String = ""                           // VIEW directive for state projection
    var checkDeadlock: Bool = true
    var workers: Int = 1
    var maxStates: Int = AppConstants.ModelChecker.defaultMaxStates
    var maxDepth: Int = AppConstants.ModelChecker.defaultMaxDepth

    // Simulation mode options
    var simulationMode: Bool = false
    var simulationTraceCount: Int = AppConstants.ModelChecker.defaultSimulationTraceCount
    var simulationTraceDepth: Int = AppConstants.ModelChecker.defaultSimulationTraceDepth

    // Diagnostics options
    var coverageEnabled: Bool = false
    var profilerEnabled: Bool = false

    /// Parses a .cfg file content into a TLCConfig
    static func parse(from content: String) -> TLCConfig {
        var config = TLCConfig()
        let lines = content.components(separatedBy: .newlines)

        var currentSection: String?

        for line in lines {
            let trimmed = line.trimmingCharacters(in: .whitespaces)

            // Skip comments and empty lines
            if trimmed.isEmpty || trimmed.hasPrefix("\\*") { continue }

            // Check for section headers using TLAConfigKeyword enum
            if trimmed.startsWithKeyword(TLAConfigKeyword.initState.rawValue) {
                currentSection = "INIT"
                let value = TLAConfigKeyword.initState.extractValue(from: trimmed)
                if !value.isEmpty {
                    config.initOperator = value
                }
                continue
            }

            if trimmed.startsWithKeyword(TLAConfigKeyword.next.rawValue) {
                currentSection = "NEXT"
                let value = TLAConfigKeyword.next.extractValue(from: trimmed)
                if !value.isEmpty {
                    config.nextOperator = value
                }
                continue
            }

            if trimmed.startsWithKeyword(TLAConfigKeyword.specification.rawValue) {
                currentSection = "SPECIFICATION"
                let value = TLAConfigKeyword.specification.extractValue(from: trimmed)
                if !value.isEmpty {
                    config.specificationOperator = value
                }
                continue
            }

            if trimmed == "CONSTANTS" || trimmed.hasPrefix("CONSTANT ") || trimmed.hasPrefix("CONSTANTS ") {
                currentSection = "CONSTANTS"
                // Handle inline constant definition
                var remainder = trimmed
                if remainder.hasPrefix("CONSTANTS ") {
                    remainder = String(remainder.dropFirst("CONSTANTS ".count))
                } else if remainder.hasPrefix("CONSTANT ") {
                    remainder = String(remainder.dropFirst("CONSTANT ".count))
                } else {
                    continue
                }
                remainder = remainder.trimmingCharacters(in: .whitespaces)
                if !remainder.isEmpty, remainder.contains("=") || remainder.contains("<-") {
                    let separator = remainder.contains("<-") ? "<-" : "="
                    let parts = remainder.components(separatedBy: separator)
                    if parts.count == 2 {
                        let name = parts[0].trimmingCharacters(in: .whitespaces)
                        let value = parts[1].trimmingCharacters(in: .whitespaces)
                        if !name.isEmpty && !value.isEmpty {
                            config.constants.append(TLCConstant(name: name, value: value))
                        }
                    }
                }
                continue
            }

            if trimmed == "INVARIANTS" || trimmed.hasPrefix("INVARIANT ") {
                currentSection = "INVARIANTS"
                if trimmed.hasPrefix("INVARIANT ") {
                    let value = extractAfterKeyword(trimmed, "INVARIANT ")
                    if !value.isEmpty {
                        config.invariants.append(TLCInvariant(name: value))
                    }
                }
                continue
            }

            if trimmed == "PROPERTIES" || trimmed.hasPrefix("PROPERTY ") {
                currentSection = "PROPERTIES"
                if trimmed.hasPrefix("PROPERTY ") {
                    let value = extractAfterKeyword(trimmed, "PROPERTY ")
                    if !value.isEmpty {
                        config.properties.append(TLCProperty(name: value))
                    }
                }
                continue
            }

            if trimmed.startsWithKeyword(TLAConfigKeyword.symmetry.rawValue) {
                currentSection = "SYMMETRY"
                let value = TLAConfigKeyword.symmetry.extractValue(from: trimmed)
                if !value.isEmpty {
                    config.symmetrySets.append(TLCSymmetrySet(name: value))
                }
                continue
            }

            // State constraints
            if trimmed.hasPrefix("CONSTRAINT") && !trimmed.hasPrefix("CONSTRAINTS") {
                currentSection = "CONSTRAINT"
                let value = TLAConfigKeyword.constraint.extractValue(from: trimmed)
                if !value.isEmpty {
                    config.constraints.append(TLCConstraint(expression: value))
                }
                continue
            }

            if trimmed == "CONSTRAINTS" {
                currentSection = "CONSTRAINTS"
                continue
            }

            // Action constraints
            if trimmed.hasPrefix("ACTION_CONSTRAINT") && !trimmed.hasPrefix("ACTION_CONSTRAINTS") {
                currentSection = "ACTION_CONSTRAINT"
                let value = TLAConfigKeyword.actionConstraint.extractValue(from: trimmed)
                if !value.isEmpty {
                    config.actionConstraints.append(TLCActionConstraint(expression: value))
                }
                continue
            }

            if trimmed == "ACTION_CONSTRAINTS" {
                currentSection = "ACTION_CONSTRAINTS"
                continue
            }

            // View directive
            if trimmed.startsWithKeyword(TLAConfigKeyword.view.rawValue) {
                let value = TLAConfigKeyword.view.extractValue(from: trimmed)
                if !value.isEmpty {
                    config.view = value
                }
                continue
            }

            if trimmed.startsWithKeyword(TLAConfigKeyword.checkDeadlock.rawValue) {
                let value = TLAConfigKeyword.checkDeadlock.extractValue(from: trimmed)
                config.checkDeadlock = value.uppercased() != "FALSE"
                continue
            }

            // Parse values in sections
            switch currentSection {
            case "CONSTANTS":
                if trimmed.contains("=") || trimmed.contains("<-") {
                    let separator = trimmed.contains("<-") ? "<-" : "="
                    let parts = trimmed.components(separatedBy: separator)
                    if parts.count == 2 {
                        let name = parts[0].trimmingCharacters(in: .whitespaces)
                        let value = parts[1].trimmingCharacters(in: .whitespaces)
                        if !name.isEmpty && !value.isEmpty {
                            config.constants.append(TLCConstant(name: name, value: value))
                        }
                    }
                }

            case "INVARIANTS":
                if !trimmed.isEmpty {
                    config.invariants.append(TLCInvariant(name: trimmed))
                }

            case "PROPERTIES":
                if !trimmed.isEmpty {
                    config.properties.append(TLCProperty(name: trimmed))
                }

            case "CONSTRAINTS":
                if !trimmed.isEmpty {
                    config.constraints.append(TLCConstraint(expression: trimmed))
                }

            case "ACTION_CONSTRAINTS":
                if !trimmed.isEmpty {
                    config.actionConstraints.append(TLCActionConstraint(expression: trimmed))
                }

            default:
                break
            }
        }

        return config
    }

    /// Generates a .cfg file content from the configuration
    func generateConfigFile() -> String {
        var lines: [String] = []

        // Specification
        if !specificationOperator.isEmpty {
            lines.append("SPECIFICATION \(specificationOperator)")
        } else {
            if !initOperator.isEmpty {
                lines.append("INIT \(initOperator)")
            }
            if !nextOperator.isEmpty {
                lines.append("NEXT \(nextOperator)")
            }
        }

        // Constants
        let validConstants = constants.filter { !$0.name.isEmpty && !$0.value.isEmpty }
        if !validConstants.isEmpty {
            lines.append("")
            lines.append("CONSTANTS")
            for constant in validConstants {
                lines.append("    \(constant.name) = \(constant.value)")
            }
        }

        // Invariants
        let validInvariants = invariants.filter { !$0.name.isEmpty }
        if !validInvariants.isEmpty {
            lines.append("")
            for invariant in validInvariants {
                lines.append("INVARIANT \(invariant.name)")
            }
        }

        // Properties
        let validProperties = properties.filter { !$0.name.isEmpty }
        if !validProperties.isEmpty {
            lines.append("")
            for property in validProperties {
                lines.append("PROPERTY \(property.name)")
            }
        }

        // Symmetry
        let validSymmetry = symmetrySets.filter { !$0.name.isEmpty }
        if !validSymmetry.isEmpty {
            lines.append("")
            for symmetry in validSymmetry {
                lines.append("SYMMETRY \(symmetry.name)")
            }
        }

        // State Constraints
        let validConstraints = constraints.filter { !$0.expression.isEmpty }
        if !validConstraints.isEmpty {
            lines.append("")
            for constraint in validConstraints {
                lines.append("CONSTRAINT \(constraint.expression)")
            }
        }

        // Action Constraints
        let validActionConstraints = actionConstraints.filter { !$0.expression.isEmpty }
        if !validActionConstraints.isEmpty {
            lines.append("")
            for actionConstraint in validActionConstraints {
                lines.append("ACTION_CONSTRAINT \(actionConstraint.expression)")
            }
        }

        // View
        if !view.isEmpty {
            lines.append("")
            lines.append("VIEW \(view)")
        }

        // Options
        if !checkDeadlock {
            lines.append("")
            lines.append("CHECK_DEADLOCK FALSE")
        }

        return lines.joined(separator: "\n")
    }
}

// MARK: - Supporting Types

/// Constant definition for TLC configuration
struct TLCConstant: Identifiable, Codable, Equatable {
    let id: UUID
    var name: String
    var value: String

    init(id: UUID = UUID(), name: String, value: String) {
        self.id = id
        self.name = name
        self.value = value
    }
}

/// Invariant specification for TLC configuration
struct TLCInvariant: Identifiable, Codable, Equatable {
    let id: UUID
    var name: String

    init(id: UUID = UUID(), name: String) {
        self.id = id
        self.name = name
    }
}

/// Temporal property specification for TLC configuration
struct TLCProperty: Identifiable, Codable, Equatable {
    let id: UUID
    var name: String

    init(id: UUID = UUID(), name: String) {
        self.id = id
        self.name = name
    }
}

/// Symmetry set specification for TLC configuration
struct TLCSymmetrySet: Identifiable, Codable, Equatable {
    let id: UUID
    var name: String

    init(id: UUID = UUID(), name: String) {
        self.id = id
        self.name = name
    }
}

/// State constraint for TLC configuration
struct TLCConstraint: Identifiable, Codable, Equatable {
    let id: UUID
    var expression: String  // State predicate expression

    init(id: UUID = UUID(), expression: String) {
        self.id = id
        self.expression = expression
    }
}

/// Action constraint for TLC configuration
struct TLCActionConstraint: Identifiable, Codable, Equatable {
    let id: UUID
    var expression: String  // Action predicate expression (can use primed variables)

    init(id: UUID = UUID(), expression: String) {
        self.id = id
        self.expression = expression
    }
}
