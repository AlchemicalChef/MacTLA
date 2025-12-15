import Foundation

/// Profiles expression evaluation costs during model checking
actor Profiler {
    /// Statistics for each expression/operator
    struct ExpressionStats {
        var callCount: Int = 0
        var totalTimeNanos: UInt64 = 0
        var maxTimeNanos: UInt64 = 0

        var averageTimeNanos: Double {
            callCount > 0 ? Double(totalTimeNanos) / Double(callCount) : 0
        }

        var totalTimeMs: Double {
            Double(totalTimeNanos) / 1_000_000
        }

        var averageTimeMs: Double {
            averageTimeNanos / 1_000_000
        }
    }

    private var expressionStats: [String: ExpressionStats] = [:]
    private var enabled = false
    private var startTime: UInt64 = 0

    /// Enable or disable profiling
    func setEnabled(_ enabled: Bool) {
        self.enabled = enabled
    }

    func isEnabled() -> Bool {
        return enabled
    }

    /// Start timing an expression
    func startTiming() -> UInt64 {
        guard enabled else { return 0 }
        return DispatchTime.now().uptimeNanoseconds
    }

    /// End timing and record stats for an expression
    func endTiming(for expression: String, startTime: UInt64) {
        guard enabled, startTime > 0 else { return }

        let endTime = DispatchTime.now().uptimeNanoseconds
        let elapsed = endTime - startTime

        var stats = expressionStats[expression, default: ExpressionStats()]
        stats.callCount += 1
        stats.totalTimeNanos += elapsed
        stats.maxTimeNanos = max(stats.maxTimeNanos, elapsed)
        expressionStats[expression] = stats
    }

    /// Record a call without timing (for counting purposes)
    func recordCall(for expression: String) {
        guard enabled else { return }

        var stats = expressionStats[expression, default: ExpressionStats()]
        stats.callCount += 1
        expressionStats[expression] = stats
    }

    /// Reset all statistics
    func reset() {
        expressionStats.removeAll()
    }

    /// Get profiling report
    func getReport() -> ProfilingReport {
        ProfilingReport(expressionStats: expressionStats)
    }
}

/// Profiling report for display
struct ProfilingReport: Sendable {
    let expressionStats: [String: Profiler.ExpressionStats]

    var formattedReport: String {
        var lines: [String] = []
        lines.append("=== Profiling Report ===")
        lines.append("")

        if expressionStats.isEmpty {
            lines.append("No expressions profiled")
            return lines.joined(separator: "\n")
        }

        // Sort by total time descending
        let sortedExpressions = expressionStats.sorted { $0.value.totalTimeNanos > $1.value.totalTimeNanos }

        // Top 20 most expensive
        lines.append("Top Expressions by Total Time:")
        for (index, (expr, stats)) in sortedExpressions.prefix(20).enumerated() {
            let displayExpr = expr.count > 50 ? String(expr.prefix(47)) + "..." : expr
            lines.append("\(index + 1). \(displayExpr)")
            lines.append("   Calls: \(stats.callCount), Total: \(String(format: "%.2f", stats.totalTimeMs))ms, Avg: \(String(format: "%.3f", stats.averageTimeMs))ms")
        }

        lines.append("")

        // Summary statistics
        let totalCalls = expressionStats.values.reduce(0) { $0 + $1.callCount }
        let totalTime = expressionStats.values.reduce(UInt64(0)) { $0 + $1.totalTimeNanos }

        lines.append("Summary:")
        lines.append("  Total expression evaluations: \(totalCalls)")
        lines.append("  Total evaluation time: \(String(format: "%.2f", Double(totalTime) / 1_000_000))ms")
        lines.append("  Unique expressions: \(expressionStats.count)")

        return lines.joined(separator: "\n")
    }
}
