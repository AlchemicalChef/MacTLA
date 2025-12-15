import SwiftUI

/// Viewer for counterexample traces from model checking
struct TraceViewerView: View {
    let trace: [TraceState]
    let onStateSelected: ((TraceState) -> Void)?

    @State private var selectedStateId: UUID?
    @State private var expandedStateIds: Set<UUID> = []

    init(trace: [TraceState], onStateSelected: ((TraceState) -> Void)? = nil) {
        self.trace = trace
        self.onStateSelected = onStateSelected
    }

    var body: some View {
        VStack(spacing: 0) {
            // Header
            HStack {
                Label("Error Trace", systemImage: "exclamationmark.triangle.fill")
                    .foregroundStyle(.red)
                    .font(.headline)

                Spacer()

                Text("\(trace.count) states")
                    .font(.caption)
                    .foregroundStyle(.secondary)
            }
            .padding()
            .background(.bar)

            Divider()

            // Trace list
            ScrollView {
                LazyVStack(spacing: 0) {
                    ForEach(trace) { state in
                        TraceStateRow(
                            state: state,
                            isSelected: selectedStateId == state.id,
                            isExpanded: expandedStateIds.contains(state.id),
                            onSelect: {
                                selectedStateId = state.id
                                onStateSelected?(state)
                            },
                            onToggleExpand: {
                                if expandedStateIds.contains(state.id) {
                                    expandedStateIds.remove(state.id)
                                } else {
                                    expandedStateIds.insert(state.id)
                                }
                            }
                        )

                        if state.id != trace.last?.id {
                            // Arrow between states
                            HStack {
                                Spacer()
                                Image(systemName: "arrow.down")
                                    .font(.caption)
                                    .foregroundStyle(.secondary)
                                Spacer()
                            }
                            .padding(.vertical, 4)
                        }
                    }
                }
                .padding()
            }
        }
    }
}

struct TraceStateRow: View {
    let state: TraceState
    let isSelected: Bool
    let isExpanded: Bool
    let onSelect: () -> Void
    let onToggleExpand: () -> Void

    var body: some View {
        VStack(alignment: .leading, spacing: 8) {
            // Header row
            Button(action: onSelect) {
                HStack {
                    // Step indicator
                    ZStack {
                        Circle()
                            .fill(state.isError ? Color.red : (state.stepNumber == 0 ? Color.green : Color.blue))
                            .frame(width: 28, height: 28)

                        Text("\(state.stepNumber)")
                            .font(.caption.bold())
                            .foregroundStyle(.white)
                    }

                    VStack(alignment: .leading, spacing: 2) {
                        Text(state.action)
                            .font(.subheadline.bold())
                            .foregroundStyle(.primary)

                        Text("\(state.variables.count) variables")
                            .font(.caption)
                            .foregroundStyle(.secondary)
                    }

                    Spacer()

                    // Expand button
                    Button(action: onToggleExpand) {
                        Image(systemName: isExpanded ? "chevron.up" : "chevron.down")
                            .font(.caption)
                            .foregroundStyle(.secondary)
                    }
                    .buttonStyle(.plain)
                }
                .padding(12)
                .background(
                    RoundedRectangle(cornerRadius: 8)
                        .fill(isSelected ? Color.accentColor.opacity(0.1) : Color.clear)
                )
                .overlay(
                    RoundedRectangle(cornerRadius: 8)
                        .stroke(
                            state.isError ? Color.red :
                                (isSelected ? Color.accentColor : Color.gray.opacity(0.3)),
                            lineWidth: state.isError ? 2 : 1
                        )
                )
            }
            .buttonStyle(.plain)

            // Expanded variable list
            if isExpanded {
                VStack(alignment: .leading, spacing: 4) {
                    ForEach(state.variables.sorted(by: { $0.key < $1.key }), id: \.key) { key, value in
                        HStack(alignment: .top) {
                            Text(key)
                                .font(.system(.caption, design: .monospaced))
                                .foregroundStyle(.blue)
                                .frame(width: 100, alignment: .leading)

                            Text("=")
                                .font(.system(.caption, design: .monospaced))
                                .foregroundStyle(.secondary)

                            Text(value)
                                .font(.system(.caption, design: .monospaced))
                                .foregroundStyle(.primary)
                                .textSelection(.enabled)

                            Spacer()
                        }
                        .padding(.horizontal, 8)
                        .padding(.vertical, 2)
                    }
                }
                .padding(8)
                .background(
                    RoundedRectangle(cornerRadius: 6)
                        .fill(Color.gray.opacity(0.1))
                )
                .padding(.leading, 40)
            }
        }
    }
}

// MARK: - Variable Diff View

struct VariableDiffView: View {
    let previousState: TraceState?
    let currentState: TraceState

    var body: some View {
        VStack(alignment: .leading, spacing: 8) {
            Text("Variable Changes")
                .font(.headline)

            ForEach(currentState.variables.sorted(by: { $0.key < $1.key }), id: \.key) { key, value in
                let previousValue = previousState?.variables[key]
                let hasChanged = previousValue != value

                HStack(alignment: .top) {
                    Image(systemName: hasChanged ? "arrow.right.circle.fill" : "circle")
                        .foregroundStyle(hasChanged ? .orange : .secondary)
                        .font(.caption)

                    VStack(alignment: .leading, spacing: 2) {
                        Text(key)
                            .font(.system(.subheadline, design: .monospaced).bold())

                        if hasChanged, let prev = previousValue {
                            HStack(spacing: 4) {
                                Text(prev)
                                    .font(.system(.caption, design: .monospaced))
                                    .foregroundStyle(.secondary)
                                    .strikethrough()

                                Image(systemName: "arrow.right")
                                    .font(.caption2)
                                    .foregroundStyle(.secondary)

                                Text(value)
                                    .font(.system(.caption, design: .monospaced))
                                    .foregroundStyle(.green)
                            }
                        } else {
                            Text(value)
                                .font(.system(.caption, design: .monospaced))
                                .foregroundStyle(.primary)
                        }
                    }

                    Spacer()
                }
                .padding(.vertical, 4)
            }
        }
        .padding()
    }
}

// MARK: - Full Trace Sheet

struct TraceSheetView: View {
    @Binding var isPresented: Bool
    let result: VerificationResult

    @State private var selectedStateIndex = 0
    @State private var expressionText = ""
    @State private var evaluatedExpressions: [UUID: String] = [:]  // State ID -> evaluation result
    @State private var evaluationError: String?

    private var trace: [TraceState] {
        // The counterexample is the trace - use it directly
        let counterexample = result.counterexample
        guard !counterexample.isEmpty else {
            return []
        }

        // Return as-is since TraceState already has the right structure
        return counterexample
    }

    var body: some View {
        NavigationStack {
            HStack(spacing: 0) {
                // Trace list
                TraceViewerView(trace: trace) { state in
                    if let index = trace.firstIndex(where: { $0.id == state.id }) {
                        selectedStateIndex = index
                    }
                }
                .frame(minWidth: 300)

                // Detail view
                if trace.indices.contains(selectedStateIndex) {
                    let currentState = trace[selectedStateIndex]
                    let previousState = selectedStateIndex > 0 ? trace[selectedStateIndex - 1] : nil

                    ScrollView {
                        VStack(alignment: .leading, spacing: 16) {
                            // State header
                            HStack {
                                Label(
                                    "Step \(currentState.stepNumber)",
                                    systemImage: currentState.isError ? "exclamationmark.triangle.fill" : "circle.fill"
                                )
                                .font(.title2.bold())
                                .foregroundStyle(currentState.isError ? .red : .primary)

                                Spacer()

                                Text(currentState.action)
                                    .font(.headline)
                                    .foregroundStyle(.secondary)
                            }

                            Divider()

                            // Variable diff
                            VariableDiffView(
                                previousState: previousState,
                                currentState: currentState
                            )

                            if currentState.isError {
                                // Error description
                                VStack(alignment: .leading, spacing: 8) {
                                    Label("Invariant Violation", systemImage: "xmark.circle.fill")
                                        .font(.headline)
                                        .foregroundStyle(.red)

                                    if let violation = result.violatedInvariant {
                                        Text(violation)
                                            .font(.system(.body, design: .monospaced))
                                            .padding()
                                            .background(
                                                RoundedRectangle(cornerRadius: 8)
                                                    .fill(Color.red.opacity(0.1))
                                            )
                                    }
                                }
                            }

                            Divider()

                            // Expression Evaluation Section
                            VStack(alignment: .leading, spacing: 8) {
                                Label("Evaluate Expression", systemImage: "function")
                                    .font(.headline)

                                HStack {
                                    TextField("Enter expression (e.g., x + y)", text: $expressionText)
                                        .textFieldStyle(.roundedBorder)
                                        .font(.system(.body, design: .monospaced))
                                        .onSubmit {
                                            evaluateExpressionForAllStates()
                                        }

                                    Button("Evaluate") {
                                        evaluateExpressionForAllStates()
                                    }
                                    .buttonStyle(.borderedProminent)
                                    .disabled(expressionText.isEmpty)

                                    if !evaluatedExpressions.isEmpty {
                                        Button("Clear") {
                                            evaluatedExpressions.removeAll()
                                            evaluationError = nil
                                        }
                                        .buttonStyle(.bordered)
                                    }
                                }

                                if let error = evaluationError {
                                    Text(error)
                                        .font(.caption)
                                        .foregroundStyle(.red)
                                }

                                if let evalResult = evaluatedExpressions[currentState.id] {
                                    HStack {
                                        Text("Result:")
                                            .font(.subheadline)
                                            .foregroundStyle(.secondary)
                                        Text(evalResult)
                                            .font(.system(.body, design: .monospaced))
                                            .foregroundStyle(.green)
                                            .textSelection(.enabled)
                                    }
                                    .padding()
                                    .background(
                                        RoundedRectangle(cornerRadius: 8)
                                            .fill(Color.green.opacity(0.1))
                                    )
                                }
                            }

                            Spacer()
                        }
                        .padding()
                    }
                    .frame(minWidth: 400)
                } else {
                    ContentUnavailableView(
                        "Select a State",
                        systemImage: "list.bullet.rectangle",
                        description: Text("Choose a state from the trace to see details")
                    )
                }
            }
            .navigationTitle("Error Trace")
            .toolbar {
                ToolbarItemGroup(placement: .primaryAction) {
                    Button(action: { navigatePrevious() }) {
                        Image(systemName: "chevron.left")
                    }
                    .disabled(selectedStateIndex <= 0)

                    Button(action: { navigateNext() }) {
                        Image(systemName: "chevron.right")
                    }
                    .disabled(selectedStateIndex >= trace.count - 1)
                }

                ToolbarItem(placement: .cancellationAction) {
                    Button("Done") {
                        isPresented = false
                    }
                }
            }
        }
    }

    private func navigatePrevious() {
        if selectedStateIndex > 0 {
            selectedStateIndex -= 1
        }
    }

    private func navigateNext() {
        if selectedStateIndex < trace.count - 1 {
            selectedStateIndex += 1
        }
    }

    /// Evaluates the expression for all states in the trace
    private func evaluateExpressionForAllStates() {
        guard !expressionText.isEmpty else { return }

        evaluatedExpressions.removeAll()
        evaluationError = nil

        let parser = TLAParser()
        let interpreter = TLAInterpreter()

        // Parse the expression once
        guard case .success(let expr) = parser.parseExpression(expressionText) else {
            evaluationError = "Failed to parse expression"
            return
        }

        // Evaluate for each state
        for state in trace {
            var env = TLAInterpreter.Environment()

            // Set up variables from the state
            for (key, valueStr) in state.variables {
                if let value = parseValueString(valueStr) {
                    env.variables[key] = value
                }
            }

            do {
                let result = try interpreter.evaluate(expr, in: env)
                evaluatedExpressions[state.id] = result.description
            } catch {
                evaluatedExpressions[state.id] = "Error: \(error.localizedDescription)"
            }
        }
    }

    /// Parse a string representation back to a TLAValue
    private func parseValueString(_ str: String) -> TLAValue? {
        let trimmed = str.trimmingCharacters(in: .whitespaces)

        // Boolean
        if trimmed == "TRUE" { return .boolean(true) }
        if trimmed == "FALSE" { return .boolean(false) }

        // Integer
        if let n = Int(trimmed) { return .integer(n) }

        // String (quoted)
        if trimmed.hasPrefix("\"") && trimmed.hasSuffix("\"") {
            return .string(String(trimmed.dropFirst().dropLast()))
        }

        // Set: {a, b, c}
        if trimmed.hasPrefix("{") && trimmed.hasSuffix("}") {
            let inner = String(trimmed.dropFirst().dropLast())
            if inner.isEmpty { return .set([]) }
            let elements = parseCommaSeparated(inner)
            var values: Set<TLAValue> = []
            for elem in elements {
                if let val = parseValueString(elem) {
                    values.insert(val)
                }
            }
            return .set(values)
        }

        // Sequence: <<a, b, c>>
        if trimmed.hasPrefix("<<") && trimmed.hasSuffix(">>") {
            let inner = String(trimmed.dropFirst(2).dropLast(2))
            if inner.isEmpty { return .sequence([]) }
            let elements = parseCommaSeparated(inner)
            var values: [TLAValue] = []
            for elem in elements {
                if let val = parseValueString(elem) {
                    values.append(val)
                }
            }
            return .sequence(values)
        }

        // Record: [a |-> 1, b |-> 2]
        if trimmed.hasPrefix("[") && trimmed.hasSuffix("]") {
            let inner = String(trimmed.dropFirst().dropLast())
            if inner.isEmpty { return .record([:]) }
            let fields = parseCommaSeparated(inner)
            var record: [String: TLAValue] = [:]
            for field in fields {
                let parts = field.components(separatedBy: "|->")
                if parts.count == 2 {
                    let key = parts[0].trimmingCharacters(in: .whitespaces)
                    let valStr = parts[1].trimmingCharacters(in: .whitespaces)
                    if let val = parseValueString(valStr) {
                        record[key] = val
                    }
                }
            }
            return .record(record)
        }

        // Default: model value
        return .modelValue(trimmed)
    }

    /// Parse comma-separated elements, respecting nesting
    private func parseCommaSeparated(_ str: String) -> [String] {
        var elements: [String] = []
        var current = ""
        var depth = 0

        for char in str {
            if char == "{" || char == "[" || char == "<" {
                depth += 1
                current.append(char)
            } else if char == "}" || char == "]" || char == ">" {
                depth -= 1
                current.append(char)
            } else if char == "," && depth == 0 {
                elements.append(current.trimmingCharacters(in: .whitespaces))
                current = ""
            } else {
                current.append(char)
            }
        }

        if !current.isEmpty {
            elements.append(current.trimmingCharacters(in: .whitespaces))
        }

        return elements
    }
}

// MARK: - Preview

#Preview {
    let sampleTrace = [
        TraceState(
            stepNumber: 0,
            action: "Init",
            state: ["x": "0", "y": "0", "pc": "\"start\""],
            isError: false
        ),
        TraceState(
            stepNumber: 1,
            action: "Increment",
            state: ["x": "1", "y": "0", "pc": "\"loop\""],
            isError: false
        ),
        TraceState(
            stepNumber: 2,
            action: "Increment",
            state: ["x": "2", "y": "0", "pc": "\"loop\""],
            isError: false
        ),
        TraceState(
            stepNumber: 3,
            action: "Check",
            state: ["x": "2", "y": "1", "pc": "\"done\""],
            isError: true
        )
    ]

    TraceViewerView(trace: sampleTrace)
}
