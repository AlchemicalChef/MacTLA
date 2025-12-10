import SwiftUI

struct VerificationResultsView: View {
    let results: [VerificationResult]
    @State private var selectedResult: VerificationResult?

    var body: some View {
        VStack(alignment: .leading, spacing: 0) {
            HStack {
                Text("Verification Results")
                    .font(.headline)
                Spacer()
                if let latest = results.last {
                    TLABadge(icon: latest.status.iconName, label: latest.status.rawValue, color: latest.status.color)
                }
            }
            .padding()
            .background(.bar)

            Divider()

            if results.isEmpty {
                ContentUnavailableView(
                    "No Results",
                    systemImage: "checkmark.shield",
                    description: Text("Run verification to see results")
                )
            } else {
                List(results) { result in
                    ResultRowView(result: result)
                        .onTapGesture { selectedResult = result }
                }
                .listStyle(.plain)
            }
        }
        .sheet(item: $selectedResult) { result in
            ResultDetailView(result: result)
        }
    }
}

// StatusBadge replaced with TLABadge from SharedComponents.swift

struct ResultRowView: View {
    let result: VerificationResult

    var body: some View {
        HStack {
            Image(systemName: result.status.iconName)
                .foregroundStyle(result.status.color)

            VStack(alignment: .leading) {
                Text(result.specificationName)
                    .font(.subheadline)
                Text(result.timestamp, style: .relative)
                    .font(.caption)
                    .foregroundStyle(.secondary)
            }

            Spacer()

            if result.status == .success {
                Text("\(result.statesExplored) states")
                    .font(.caption)
                    .foregroundStyle(.secondary)
            }
        }
        .padding(.vertical, 4)
    }
}

struct ResultDetailView: View {
    @Environment(\.dismiss) private var dismiss
    let result: VerificationResult

    var body: some View {
        NavigationStack {
            ScrollView {
                VStack(alignment: .leading, spacing: 16) {
                    GroupBox("Summary") {
                        LabeledContent("Status", value: result.status.rawValue)
                        LabeledContent("States Explored", value: "\(result.statesExplored)")
                        LabeledContent("Distinct States", value: "\(result.distinctStates)")
                        LabeledContent("Duration", value: String(format: "%.2fs", result.duration))
                    }

                    if let errorDetails = result.errorDetails {
                        GroupBox {
                            VStack(alignment: .leading, spacing: 12) {
                                HStack {
                                    Image(systemName: errorDetails.kind.icon)
                                        .foregroundStyle(.red)
                                    Text(errorDetails.kind.rawValue)
                                        .font(.headline)
                                        .foregroundStyle(.red)
                                }

                                Text(errorDetails.message)
                                    .font(.system(.body, design: .monospaced))

                                if let location = errorDetails.location {
                                    HStack {
                                        Image(systemName: "mappin.circle")
                                            .foregroundStyle(.secondary)
                                        Text("Line \(location.line), Column \(location.column)")
                                            .font(.caption)
                                            .foregroundStyle(.secondary)
                                    }
                                }

                                if let context = errorDetails.context {
                                    VStack(alignment: .leading, spacing: 4) {
                                        Text("Context:")
                                            .font(.caption.bold())
                                            .foregroundStyle(.secondary)
                                        Text(context)
                                            .font(.system(.caption, design: .monospaced))
                                            .padding(8)
                                            .background(.quaternary)
                                            .clipShape(RoundedRectangle(cornerRadius: 4))
                                    }
                                }

                                if !errorDetails.suggestions.isEmpty {
                                    VStack(alignment: .leading, spacing: 4) {
                                        Text("Suggestions:")
                                            .font(.caption.bold())
                                            .foregroundStyle(.secondary)
                                        ForEach(errorDetails.suggestions, id: \.self) { suggestion in
                                            HStack(alignment: .top) {
                                                Image(systemName: "lightbulb")
                                                    .foregroundStyle(.yellow)
                                                Text(suggestion)
                                                    .font(.caption)
                                            }
                                        }
                                    }
                                }
                            }
                        } label: {
                            Label("Error Details", systemImage: "exclamationmark.triangle.fill")
                                .foregroundStyle(.red)
                        }
                    } else if let error = result.error {
                        GroupBox("Error") {
                            Text(error)
                                .font(.system(.body, design: .monospaced))
                                .foregroundStyle(.red)
                        }
                    }

                    if !result.counterexample.isEmpty {
                        GroupBox("Counterexample") {
                            CounterexampleView(trace: result.counterexample)
                        }
                    }

                    GroupBox("Output") {
                        Text(result.output)
                            .font(.system(.caption, design: .monospaced))
                    }
                }
                .padding()
            }
            .navigationTitle("Verification Details")
            .toolbar {
                ToolbarItem(placement: .confirmationAction) {
                    Button("Done") { dismiss() }
                }
            }
        }
    }
}

struct CounterexampleView: View {
    let trace: [TraceState]

    var body: some View {
        ForEach(Array(trace.enumerated()), id: \.offset) { index, state in
            VStack(alignment: .leading, spacing: 4) {
                Text("State \(index + 1)")
                    .font(.caption)
                    .fontWeight(.semibold)

                ForEach(state.variables.sorted(by: { $0.key < $1.key }), id: \.key) { key, value in
                    HStack {
                        Text(key)
                            .foregroundStyle(.secondary)
                        Spacer()
                        Text(value)
                            .font(.system(.body, design: .monospaced))
                    }
                }
            }
            .padding()
            .background(.quaternary)
            .clipShape(RoundedRectangle(cornerRadius: 8))
        }
    }
}

#Preview {
    VerificationResultsView(results: [])
}
