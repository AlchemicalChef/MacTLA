import Foundation

// MARK: - TLAState Extensions

extension TLAState {
    /// Converts this TLAState to a TraceState for UI display
    /// - Parameters:
    ///   - stepNumber: The step number in the trace (default: 0)
    ///   - action: The action name that led to this state (default: "")
    ///   - isError: Whether this state represents an error state (default: false)
    /// - Returns: A TraceState suitable for UI display
    func toTraceState(stepNumber: Int = 0, action: String = "", isError: Bool = false) -> TraceState {
        TraceState(
            stepNumber: stepNumber,
            action: action,
            state: variables.mapValues { $0.description },
            isError: isError
        )
    }
}

// MARK: - TLAValue Extensions

extension TLAValue {
    /// Returns a human-readable type name for this value
    var typeName: String {
        switch self {
        case .boolean: return "Boolean"
        case .integer: return "Integer"
        case .string: return "String"
        case .set: return "Set"
        case .sequence: return "Sequence"
        case .function: return "Function"
        case .record: return "Record"
        case .modelValue: return "ModelValue"
        case .tuple: return "Tuple"
        }
    }

    /// Checks if this value is a collection type (set, sequence, or tuple)
    var isCollection: Bool {
        switch self {
        case .set, .sequence, .tuple:
            return true
        default:
            return false
        }
    }

    /// Returns the count of elements if this is a collection, nil otherwise
    var count: Int? {
        switch self {
        case .set(let elements):
            return elements.count
        case .sequence(let elements), .tuple(let elements):
            return elements.count
        case .function(let map):
            return map.count
        case .record(let fields):
            return fields.count
        default:
            return nil
        }
    }
}
