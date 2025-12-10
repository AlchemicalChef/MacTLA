import SwiftUI

/// View for displaying proof checking results
struct ProofResultsView: View {
    let results: [ProofChecker.ProofResult]
    @State private var expandedTheorems: Set<String> = []

    var body: some View {
        List {
            ForEach(results, id: \.theorem) { result in
                ProofResultRow(
                    result: result,
                    isExpanded: expandedTheorems.contains(result.theorem)
                ) {
                    if expandedTheorems.contains(result.theorem) {
                        expandedTheorems.remove(result.theorem)
                    } else {
                        expandedTheorems.insert(result.theorem)
                    }
                }
            }
        }
        .listStyle(.sidebar)
        .navigationTitle("Proof Results")
    }
}

struct ProofResultRow: View {
    let result: ProofChecker.ProofResult
    let isExpanded: Bool
    let onToggle: () -> Void

    var body: some View {
        VStack(alignment: .leading, spacing: 8) {
            // Header
            Button(action: onToggle) {
                HStack {
                    statusIcon(for: result.overallStatus)

                    VStack(alignment: .leading) {
                        Text(result.theorem)
                            .font(.headline)
                        Text(statusText(for: result.overallStatus))
                            .font(.caption)
                            .foregroundStyle(.secondary)
                    }

                    Spacer()

                    Text(formatDuration(result.duration))
                        .font(.caption)
                        .foregroundStyle(.tertiary)

                    Image(systemName: isExpanded ? "chevron.down" : "chevron.right")
                        .foregroundStyle(.secondary)
                }
            }
            .buttonStyle(.plain)

            // Expanded content
            if isExpanded {
                VStack(alignment: .leading, spacing: 8) {
                    // Obligations
                    ForEach(result.obligations) { obligation in
                        ObligationRow(obligation: obligation)
                    }

                    // Messages
                    if !result.messages.isEmpty {
                        Divider()
                        ForEach(result.messages.indices, id: \.self) { index in
                            MessageRow(message: result.messages[index])
                        }
                    }
                }
                .padding(.leading, 24)
            }
        }
        .padding(.vertical, 4)
    }

    @ViewBuilder
    private func statusIcon(for status: ProofChecker.ProofStatus) -> some View {
        switch status {
        case .proved, .trivial, .byDefinition:
            Image(systemName: "checkmark.circle.fill")
                .foregroundStyle(.green)
        case .failed:
            Image(systemName: "xmark.circle.fill")
                .foregroundStyle(.red)
        case .pending, .checking:
            Image(systemName: "hourglass")
                .foregroundStyle(.orange)
        case .assumed:
            Image(systemName: "questionmark.circle.fill")
                .foregroundStyle(.yellow)
        }
    }

    private func statusText(for status: ProofChecker.ProofStatus) -> String {
        switch status {
        case .proved: return "Proved"
        case .trivial: return "Trivially true"
        case .byDefinition: return "By definition"
        case .failed: return "Failed"
        case .pending: return "Pending"
        case .checking: return "Checking..."
        case .assumed: return "Assumed"
        }
    }

    private func formatDuration(_ duration: TimeInterval) -> String {
        if duration < 0.001 {
            return "<1ms"
        } else if duration < 1.0 {
            return String(format: "%.1fms", duration * 1000)
        } else {
            return String(format: "%.2fs", duration)
        }
    }
}

struct ObligationRow: View {
    let obligation: ProofChecker.ProofObligation

    var body: some View {
        HStack(alignment: .top, spacing: 8) {
            statusIcon

            VStack(alignment: .leading, spacing: 2) {
                Text(obligation.name)
                    .font(.subheadline)
                    .fontWeight(.medium)

                if case .identifier(let goalName, _) = obligation.goal {
                    Text(goalName)
                        .font(.caption)
                        .foregroundStyle(.secondary)
                }
            }

            Spacer()

            Text(statusLabel)
                .font(.caption)
                .padding(.horizontal, 8)
                .padding(.vertical, 2)
                .background(statusColor.opacity(0.2))
                .foregroundStyle(statusColor)
                .clipShape(Capsule())
        }
        .padding(.vertical, 2)
    }

    @ViewBuilder
    private var statusIcon: some View {
        switch obligation.status {
        case .proved, .trivial, .byDefinition:
            Image(systemName: "checkmark.circle.fill")
                .foregroundStyle(.green)
                .font(.caption)
        case .failed:
            Image(systemName: "xmark.circle.fill")
                .foregroundStyle(.red)
                .font(.caption)
        case .pending, .checking:
            Image(systemName: "circle")
                .foregroundStyle(.secondary)
                .font(.caption)
        case .assumed:
            Image(systemName: "exclamationmark.circle.fill")
                .foregroundStyle(.yellow)
                .font(.caption)
        }
    }

    private var statusLabel: String {
        switch obligation.status {
        case .proved: return "proved"
        case .trivial: return "trivial"
        case .byDefinition: return "by def"
        case .failed: return "failed"
        case .pending: return "pending"
        case .checking: return "checking"
        case .assumed: return "assumed"
        }
    }

    private var statusColor: Color {
        switch obligation.status {
        case .proved, .trivial, .byDefinition: return .green
        case .failed: return .red
        case .pending, .checking: return .secondary
        case .assumed: return .yellow
        }
    }
}

struct MessageRow: View {
    let message: ProofChecker.ProofMessage

    var body: some View {
        HStack(alignment: .top, spacing: 8) {
            Image(systemName: iconName)
                .foregroundStyle(iconColor)
                .font(.caption)

            Text(message.message)
                .font(.caption)
                .foregroundStyle(iconColor)

            Spacer()
        }
    }

    private var iconName: String {
        switch message.level {
        case .info: return "info.circle"
        case .warning: return "exclamationmark.triangle"
        case .error: return "xmark.circle"
        }
    }

    private var iconColor: Color {
        switch message.level {
        case .info: return .secondary
        case .warning: return .orange
        case .error: return .red
        }
    }
}

// MARK: - Proof Checking Integration

struct ProofToolbarButton: View {
    @EnvironmentObject var appState: AppState
    @State private var isChecking = false
    @State private var showResults = false
    @State private var showError = false
    @State private var errorMessage = ""
    @State private var results: [ProofChecker.ProofResult] = []
    @State private var currentTask: Task<Void, Never>?

    var body: some View {
        Button(action: checkProofs) {
            if isChecking {
                ProgressView()
                    .progressViewStyle(.circular)
                    .scaleEffect(0.7)
            } else {
                Label("Check Proofs", systemImage: "checkmark.seal")
            }
        }
        .disabled(appState.selectedFile == nil || isChecking)
        .sheet(isPresented: $showResults) {
            NavigationStack {
                ProofResultsView(results: results)
                    .toolbar {
                        ToolbarItem(placement: .cancellationAction) {
                            Button("Done") { showResults = false }
                        }
                    }
            }
        }
        .alert("Parse Error", isPresented: $showError) {
            Button("OK", role: .cancel) {}
        } message: {
            Text(errorMessage)
        }
    }

    private func checkProofs() {
        guard let file = appState.selectedFile else { return }

        // Cancel any existing task
        currentTask?.cancel()

        currentTask = Task {
            isChecking = true
            defer { isChecking = false }

            let parser = TLAParser()
            let parseResult = parser.parse(file.content)

            switch parseResult {
            case .failure(let parseErrors):
                errorMessage = "Failed to parse specification:\n" + parseErrors.errors.map(\.description).joined(separator: "\n")
                showError = true
                return
            case .success(let module):
                let checker = ProofChecker()
                results = await checker.checkModule(module)
                showResults = true
            }
        }
    }
}

#Preview {
    NavigationStack {
        ProofResultsView(results: [
            ProofChecker.ProofResult(
                theorem: "TypeInvariant",
                obligations: [
                    ProofChecker.ProofObligation(
                        name: "TypeInvariant",
                        goal: .boolean(true, .unknown),
                        status: .proved
                    ),
                    ProofChecker.ProofObligation(
                        name: "Step 1",
                        goal: .identifier("x >= 0", .unknown),
                        status: .proved
                    )
                ],
                overallStatus: .proved,
                messages: [],
                duration: 0.012
            ),
            ProofChecker.ProofResult(
                theorem: "Safety",
                obligations: [
                    ProofChecker.ProofObligation(
                        name: "Safety",
                        goal: .boolean(true, .unknown),
                        status: .failed
                    )
                ],
                overallStatus: .failed,
                messages: [
                    ProofChecker.ProofMessage(
                        level: .error,
                        message: "Could not prove 'Safety' from given facts",
                        location: nil
                    )
                ],
                duration: 0.045
            )
        ])
    }
}
