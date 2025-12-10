import SwiftUI

/// Editor view for TLC configuration files (.cfg)
struct ConfigEditorView: View {
    @Binding var config: TLCConfig
    @State private var showAddConstant = false
    @State private var showAddInvariant = false
    @State private var showAddProperty = false

    var body: some View {
        Form {
            // Specification Section
            Section("Specification") {
                TextField("INIT operator", text: $config.initOperator)
                    .tlaCodeTextField()

                TextField("NEXT operator", text: $config.nextOperator)
                    .tlaCodeTextField()

                TextField("SPECIFICATION (optional)", text: $config.specificationOperator)
                    .tlaCodeTextField()
            }

            // Constants Section
            Section {
                ForEach($config.constants) { $constant in
                    HStack {
                        TextField("Name", text: $constant.name)
                            .tlaCodeTextField()
                            .frame(maxWidth: .infinity)

                        Text("=")
                            .foregroundStyle(.secondary)

                        TextField("Value", text: $constant.value)
                            .tlaCodeTextField()
                            .frame(maxWidth: .infinity)
                    }
                }
                .onDelete { indexSet in
                    config.constants.remove(atOffsets: indexSet)
                }

                Button(action: { config.constants.append(TLCConstant(name: "", value: "")) }) {
                    Label("Add Constant", systemImage: "plus.circle")
                }
            } header: {
                Text("Constants")
            } footer: {
                Text("Define constant values for model checking (e.g., N = 3, Nodes = {n1, n2})")
            }

            // Invariants Section
            Section {
                ForEach($config.invariants) { $invariant in
                    TextField("Invariant", text: $invariant.name)
                        .tlaCodeTextField()
                }
                .onDelete { indexSet in
                    config.invariants.remove(atOffsets: indexSet)
                }

                Button(action: { config.invariants.append(TLCInvariant(name: "")) }) {
                    Label("Add Invariant", systemImage: "plus.circle")
                }
            } header: {
                Text("Invariants")
            } footer: {
                Text("Safety properties to check (must hold in every reachable state)")
            }

            // Properties Section (Temporal)
            Section {
                ForEach($config.properties) { $property in
                    TextField("Property", text: $property.name)
                        .tlaCodeTextField()
                }
                .onDelete { indexSet in
                    config.properties.remove(atOffsets: indexSet)
                }

                Button(action: { config.properties.append(TLCProperty(name: "")) }) {
                    Label("Add Property", systemImage: "plus.circle")
                }
            } header: {
                Text("Properties (Temporal)")
            } footer: {
                Text("Liveness and temporal properties to verify")
            }

            // Model Checking Options
            Section("Model Checking Options") {
                Toggle("Check Deadlock", isOn: $config.checkDeadlock)

                Stepper("Workers: \(config.workers)", value: $config.workers, in: 1...16)

                Stepper("Max States: \(formatNumber(config.maxStates))",
                        value: $config.maxStates,
                        in: 1000...100_000_000,
                        step: 100_000)

                Stepper("Max Depth: \(config.maxDepth)",
                        value: $config.maxDepth,
                        in: 1...10000,
                        step: 10)
            }

            // Symmetry Section
            Section {
                ForEach($config.symmetrySets) { $symmetrySet in
                    TextField("Symmetry Set", text: $symmetrySet.name)
                        .tlaCodeTextField()
                }
                .onDelete { indexSet in
                    config.symmetrySets.remove(atOffsets: indexSet)
                }

                Button(action: { config.symmetrySets.append(TLCSymmetrySet(name: "")) }) {
                    Label("Add Symmetry Set", systemImage: "plus.circle")
                }
            } header: {
                Text("Symmetry (Advanced)")
            } footer: {
                Text("Declare sets with symmetric values to reduce state space")
            }

            // Raw Config Preview
            Section("Generated Configuration") {
                Text(config.generateConfigFile())
                    .font(.system(.caption, design: .monospaced))
                    .foregroundStyle(.secondary)
                    .textSelection(.enabled)
            }
        }
        .navigationTitle("Configuration Editor")
    }

    private func formatNumber(_ n: Int) -> String {
        if n >= 1_000_000 {
            return "\(n / 1_000_000)M"
        } else if n >= 1_000 {
            return "\(n / 1_000)K"
        }
        return "\(n)"
    }
}

// MARK: - Configuration Model

struct TLCConfig: Codable, Equatable {
    var initOperator: String = "Init"
    var nextOperator: String = "Next"
    var specificationOperator: String = ""
    var constants: [TLCConstant] = []
    var invariants: [TLCInvariant] = []
    var properties: [TLCProperty] = []
    var symmetrySets: [TLCSymmetrySet] = []
    var checkDeadlock: Bool = true
    var workers: Int = 1
    var maxStates: Int = 1_000_000
    var maxDepth: Int = 100

    /// Parses a .cfg file content into a TLCConfig
    static func parse(from content: String) -> TLCConfig {
        var config = TLCConfig()
        let lines = content.components(separatedBy: .newlines)

        var currentSection: String?

        for line in lines {
            let trimmed = line.trimmingCharacters(in: .whitespaces)

            // Skip comments and empty lines
            if trimmed.isEmpty || trimmed.hasPrefix("\\*") { continue }

            // Check for section headers
            if trimmed.hasPrefix("INIT") {
                currentSection = "INIT"
                let value = trimmed.replacingOccurrences(of: "INIT", with: "").trimmingCharacters(in: .whitespaces)
                if !value.isEmpty {
                    config.initOperator = value
                }
                continue
            }

            if trimmed.hasPrefix("NEXT") {
                currentSection = "NEXT"
                let value = trimmed.replacingOccurrences(of: "NEXT", with: "").trimmingCharacters(in: .whitespaces)
                if !value.isEmpty {
                    config.nextOperator = value
                }
                continue
            }

            if trimmed.hasPrefix("SPECIFICATION") {
                currentSection = "SPECIFICATION"
                let value = trimmed.replacingOccurrences(of: "SPECIFICATION", with: "").trimmingCharacters(in: .whitespaces)
                if !value.isEmpty {
                    config.specificationOperator = value
                }
                continue
            }

            if trimmed == "CONSTANTS" || trimmed.hasPrefix("CONSTANT ") || trimmed.hasPrefix("CONSTANTS ") {
                currentSection = "CONSTANTS"
                // Handle inline constant definition: "CONSTANTS N = 3" or "CONSTANT N = 3"
                var remainder = trimmed
                if remainder.hasPrefix("CONSTANTS ") {
                    remainder = String(remainder.dropFirst("CONSTANTS ".count))
                } else if remainder.hasPrefix("CONSTANT ") {
                    remainder = String(remainder.dropFirst("CONSTANT ".count))
                } else {
                    continue // Just "CONSTANTS" header, no inline value
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
                    let value = trimmed.replacingOccurrences(of: "INVARIANT ", with: "").trimmingCharacters(in: .whitespaces)
                    if !value.isEmpty {
                        config.invariants.append(TLCInvariant(name: value))
                    }
                }
                continue
            }

            if trimmed == "PROPERTIES" || trimmed.hasPrefix("PROPERTY ") {
                currentSection = "PROPERTIES"
                if trimmed.hasPrefix("PROPERTY ") {
                    let value = trimmed.replacingOccurrences(of: "PROPERTY ", with: "").trimmingCharacters(in: .whitespaces)
                    if !value.isEmpty {
                        config.properties.append(TLCProperty(name: value))
                    }
                }
                continue
            }

            if trimmed.hasPrefix("SYMMETRY") {
                currentSection = "SYMMETRY"
                let value = trimmed.replacingOccurrences(of: "SYMMETRY", with: "").trimmingCharacters(in: .whitespaces)
                if !value.isEmpty {
                    config.symmetrySets.append(TLCSymmetrySet(name: value))
                }
                continue
            }

            if trimmed.hasPrefix("CHECK_DEADLOCK") {
                let value = trimmed.replacingOccurrences(of: "CHECK_DEADLOCK", with: "").trimmingCharacters(in: .whitespaces)
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
                        // Only add if both name and value are non-empty
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

        // Options
        if !checkDeadlock {
            lines.append("")
            lines.append("CHECK_DEADLOCK FALSE")
        }

        return lines.joined(separator: "\n")
    }
}

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

struct TLCInvariant: Identifiable, Codable, Equatable {
    let id: UUID
    var name: String

    init(id: UUID = UUID(), name: String) {
        self.id = id
        self.name = name
    }
}

struct TLCProperty: Identifiable, Codable, Equatable {
    let id: UUID
    var name: String

    init(id: UUID = UUID(), name: String) {
        self.id = id
        self.name = name
    }
}

struct TLCSymmetrySet: Identifiable, Codable, Equatable {
    let id: UUID
    var name: String

    init(id: UUID = UUID(), name: String) {
        self.id = id
        self.name = name
    }
}

#Preview {
    NavigationStack {
        ConfigEditorView(config: .constant(TLCConfig(
            initOperator: "Init",
            nextOperator: "Next",
            constants: [
                TLCConstant(name: "N", value: "3"),
                TLCConstant(name: "Nodes", value: "{n1, n2, n3}")
            ],
            invariants: [
                TLCInvariant(name: "TypeOK"),
                TLCInvariant(name: "SafetyInvariant")
            ],
            properties: [
                TLCProperty(name: "Liveness")
            ]
        )))
    }
}
