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
                Text("Declare sets with symmetric values to reduce state space (e.g., Permutations(Nodes))")
            }

            // State Constraints Section
            Section {
                ForEach($config.constraints) { $constraint in
                    TextField("Constraint", text: $constraint.expression)
                        .tlaCodeTextField()
                }
                .onDelete { indexSet in
                    config.constraints.remove(atOffsets: indexSet)
                }

                Button(action: { config.constraints.append(TLCConstraint(expression: "")) }) {
                    Label("Add Constraint", systemImage: "plus.circle")
                }
            } header: {
                Text("State Constraints")
            } footer: {
                Text("Limit exploration to states satisfying these predicates (e.g., x < 5)")
            }

            // Action Constraints Section
            Section {
                ForEach($config.actionConstraints) { $actionConstraint in
                    TextField("Action Constraint", text: $actionConstraint.expression)
                        .tlaCodeTextField()
                }
                .onDelete { indexSet in
                    config.actionConstraints.remove(atOffsets: indexSet)
                }

                Button(action: { config.actionConstraints.append(TLCActionConstraint(expression: "")) }) {
                    Label("Add Action Constraint", systemImage: "plus.circle")
                }
            } header: {
                Text("Action Constraints")
            } footer: {
                Text("Filter transitions satisfying these predicates (can use primed variables)")
            }

            // View Section
            Section {
                TextField("View Expression", text: $config.view)
                    .tlaCodeTextField()
            } header: {
                Text("View")
            } footer: {
                Text("Project states to these variables for comparison (e.g., <<x, y>>)")
            }

            // Simulation Mode Section
            Section {
                Toggle("Simulation Mode", isOn: $config.simulationMode)

                if config.simulationMode {
                    Stepper("Traces: \(config.simulationTraceCount)",
                            value: $config.simulationTraceCount,
                            in: 1...10000,
                            step: 10)

                    Stepper("Max Depth: \(config.simulationTraceDepth)",
                            value: $config.simulationTraceDepth,
                            in: 10...10000,
                            step: 10)
                }
            } header: {
                Text("Simulation")
            } footer: {
                Text("Random exploration instead of exhaustive checking (useful for large state spaces)")
            }

            // Diagnostics Section
            Section {
                Toggle("Coverage Tracking", isOn: $config.coverageEnabled)
                Toggle("Profiler", isOn: $config.profilerEnabled)
            } header: {
                Text("Diagnostics")
            } footer: {
                Text("Track action coverage and expression costs (may slow down checking)")
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

// TLCConfig and related types are now in Models/TLCConfig.swift

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
