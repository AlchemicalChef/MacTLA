import Foundation
import SwiftUI

struct VerificationResult: Identifiable {
    let id: UUID
    let specificationName: String
    let status: VerificationStatus
    let statesExplored: Int
    let distinctStates: Int
    let duration: TimeInterval
    let timestamp: Date
    let output: String
    let error: String?
    let counterexample: [TraceState]
    let violatedInvariant: String?
    let explorationResult: ModelChecker.ExplorationResult?
    let errorDetails: ErrorDetails?
    let coverageReport: CoverageReport?
    let profilingReport: ProfilingReport?

    init(
        id: UUID = UUID(),
        specificationName: String,
        status: VerificationStatus,
        statesExplored: Int = 0,
        distinctStates: Int = 0,
        duration: TimeInterval = 0,
        timestamp: Date = Date(),
        output: String = "",
        error: String? = nil,
        counterexample: [TraceState] = [],
        violatedInvariant: String? = nil,
        explorationResult: ModelChecker.ExplorationResult? = nil,
        errorDetails: ErrorDetails? = nil,
        coverageReport: CoverageReport? = nil,
        profilingReport: ProfilingReport? = nil
    ) {
        self.id = id
        self.specificationName = specificationName
        self.status = status
        self.statesExplored = statesExplored
        self.distinctStates = distinctStates
        self.duration = duration
        self.timestamp = timestamp
        self.output = output
        self.error = error
        self.counterexample = counterexample
        self.violatedInvariant = violatedInvariant
        self.explorationResult = explorationResult
        self.errorDetails = errorDetails
        self.coverageReport = coverageReport
        self.profilingReport = profilingReport
    }
}

/// Detailed error information for model checker errors
struct ErrorDetails {
    let kind: ErrorKind
    let message: String
    let location: SourceLocation?
    let context: String?
    let suggestions: [String]

    init(
        kind: ErrorKind,
        message: String,
        location: SourceLocation? = nil,
        context: String? = nil,
        suggestions: [String] = []
    ) {
        self.kind = kind
        self.message = message
        self.location = location
        self.context = context
        self.suggestions = suggestions
    }

    enum ErrorKind: String {
        case parseError = "Parse Error"
        case typeError = "Type Error"
        case invariantViolation = "Invariant Violation"
        case deadlock = "Deadlock"
        case livenessViolation = "Liveness Violation"
        case fairnessViolation = "Fairness Violation"
        case evaluationError = "Evaluation Error"
        case resourceLimit = "Resource Limit"
        case unknownOperator = "Unknown Operator"
        case undefinedVariable = "Undefined Variable"

        var icon: String {
            switch self {
            case .parseError: return "exclamationmark.triangle"
            case .typeError: return "questionmark.diamond"
            case .invariantViolation: return "xmark.shield"
            case .deadlock: return "lock.trianglebadge.exclamationmark"
            case .livenessViolation: return "infinity.circle"
            case .fairnessViolation: return "arrow.triangle.2.circlepath.circle"
            case .evaluationError: return "function"
            case .resourceLimit: return "gauge.with.dots.needle.67percent"
            case .unknownOperator: return "questionmark.app"
            case .undefinedVariable: return "v.circle.fill"
            }
        }
    }
}

enum VerificationStatus: String {
    case success = "Success"
    case failure = "Failure"
    case error = "Error"
    case running = "Running"
    case cancelled = "Cancelled"

    var iconName: String {
        switch self {
        case .success: return "checkmark.circle.fill"
        case .failure: return "xmark.circle.fill"
        case .error: return "exclamationmark.triangle.fill"
        case .running: return "hourglass"
        case .cancelled: return "stop.circle.fill"
        }
    }

    var color: Color {
        switch self {
        case .success: return .green
        case .failure: return .red
        case .error: return .orange
        case .running: return .blue
        case .cancelled: return .gray
        }
    }
}

struct TraceState: Identifiable {
    let id: UUID
    let stepNumber: Int
    let action: String
    let state: [String: String]
    let isError: Bool

    // Backward compatible accessor
    var variables: [String: String] { state }

    init(
        id: UUID = UUID(),
        stepNumber: Int = 0,
        action: String = "",
        state: [String: String] = [:],
        isError: Bool = false
    ) {
        self.id = id
        self.stepNumber = stepNumber
        self.action = action
        self.state = state
        self.isError = isError
    }

    // Backward compatible initializer
    init(id: UUID = UUID(), variables: [String: String]) {
        self.id = id
        self.stepNumber = 0
        self.action = ""
        self.state = variables
        self.isError = false
    }
}
