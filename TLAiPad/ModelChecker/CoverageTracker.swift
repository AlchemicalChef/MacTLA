import Foundation

/// Tracks action coverage and state statistics during model checking
actor CoverageTracker {
    /// Statistics for each action
    struct ActionStats {
        var invocations: Int = 0
        var distinctStatesGenerated: Int = 0
        var lastInvokedAtState: Int = 0
    }

    /// Statistics for state space
    struct StateSpaceStats {
        var totalStates: Int = 0
        var distinctStates: Int = 0
        var deadlockStates: Int = 0
        var errorStates: Int = 0
        var maxDepth: Int = 0
    }

    private var actionStats: [String: ActionStats] = [:]
    private var stateSpaceStats = StateSpaceStats()
    private var enabled = false

    /// Enable or disable coverage tracking
    func setEnabled(_ enabled: Bool) {
        self.enabled = enabled
    }

    func isEnabled() -> Bool {
        return enabled
    }

    /// Record that an action was invoked
    func recordActionInvocation(action: String, generatedNewState: Bool, atState stateNumber: Int) {
        guard enabled else { return }

        var stats = actionStats[action, default: ActionStats()]
        stats.invocations += 1
        if generatedNewState {
            stats.distinctStatesGenerated += 1
        }
        stats.lastInvokedAtState = stateNumber
        actionStats[action] = stats
    }

    /// Record state statistics
    func recordState(isNew: Bool, depth: Int, isDeadlock: Bool = false, isError: Bool = false) {
        guard enabled else { return }

        stateSpaceStats.totalStates += 1
        if isNew {
            stateSpaceStats.distinctStates += 1
        }
        if isDeadlock {
            stateSpaceStats.deadlockStates += 1
        }
        if isError {
            stateSpaceStats.errorStates += 1
        }
        stateSpaceStats.maxDepth = max(stateSpaceStats.maxDepth, depth)
    }

    /// Reset all statistics
    func reset() {
        actionStats.removeAll()
        stateSpaceStats = StateSpaceStats()
    }

    /// Get coverage report
    func getReport() -> CoverageReport {
        CoverageReport(
            actionStats: actionStats,
            stateSpaceStats: stateSpaceStats
        )
    }
}

/// Coverage report for display
struct CoverageReport: Sendable {
    let actionStats: [String: CoverageTracker.ActionStats]
    let stateSpaceStats: CoverageTracker.StateSpaceStats

    var formattedReport: String {
        var lines: [String] = []
        lines.append("=== Coverage Report ===")
        lines.append("")

        // State space summary
        lines.append("State Space:")
        lines.append("  Total states: \(stateSpaceStats.totalStates)")
        lines.append("  Distinct states: \(stateSpaceStats.distinctStates)")
        lines.append("  Max depth: \(stateSpaceStats.maxDepth)")
        if stateSpaceStats.deadlockStates > 0 {
            lines.append("  Deadlock states: \(stateSpaceStats.deadlockStates)")
        }
        if stateSpaceStats.errorStates > 0 {
            lines.append("  Error states: \(stateSpaceStats.errorStates)")
        }
        lines.append("")

        // Action coverage
        lines.append("Action Coverage:")
        if actionStats.isEmpty {
            lines.append("  No actions recorded")
        } else {
            let sortedActions = actionStats.sorted { $0.value.invocations > $1.value.invocations }
            for (action, stats) in sortedActions {
                lines.append("  \(action):")
                lines.append("    Invocations: \(stats.invocations)")
                lines.append("    New states: \(stats.distinctStatesGenerated)")
            }
        }

        return lines.joined(separator: "\n")
    }
}
