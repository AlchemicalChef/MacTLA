import Foundation

/// Manages parsing of indentation-based conjunction and disjunction lists in TLA+.
/// Based on SANY's JunctionListContext from the reference TLA+ parser.
///
/// TLA+ allows vertically-aligned bullet lists like:
/// ```
/// /\ A
/// /\ B
///    /\ C
///    /\ D
/// /\ E
/// ```
/// Which parses as: A /\ B /\ (C /\ D) /\ E
///
/// The alignment (column position) determines nesting.
final class JunctionListContext {

    /// Type of junction list
    enum JunctionType {
        case conjunction  // /\ or ∧
        case disjunction  // \/ or ∨
    }

    /// Information about an active junction list
    struct JunctionListInfo {
        let type: JunctionType
        let column: Int  // Column position of the bullet (codepoint-based)
        let line: Int    // Line where the list started
    }

    /// Stack of active junction lists (innermost at top)
    private var stack: [JunctionListInfo] = []

    /// Start a new junction list at the given position
    /// - Parameters:
    ///   - type: Whether this is a conjunction or disjunction list
    ///   - column: The column position of the bullet symbol
    ///   - line: The line number
    func startNewJunctionList(type: JunctionType, column: Int, line: Int) {
        stack.append(JunctionListInfo(type: type, column: column, line: line))
    }

    /// Terminate the current (innermost) junction list
    func terminateCurrentJunctionList() {
        if !stack.isEmpty {
            stack.removeLast()
        }
    }

    /// Check if we're currently inside any junction list
    var isInJunctionList: Bool {
        !stack.isEmpty
    }

    /// Get the current (innermost) junction list info
    var current: JunctionListInfo? {
        stack.last
    }

    /// Get the nesting depth
    var depth: Int {
        stack.count
    }

    /// Check if a bullet token at the given column continues the current list
    /// - Parameters:
    ///   - type: The type of bullet seen
    ///   - column: The column position of the bullet
    /// - Returns: true if this bullet is at the same column as the current list
    func isNewBullet(type: JunctionType, column: Int) -> Bool {
        guard let current = current else { return false }
        return current.type == type && current.column == column
    }

    /// Check if a token's column is indented relative to current list
    /// (i.e., it's part of the current list item, not a new item)
    /// - Parameter column: The column to check
    /// - Returns: true if the column is greater than the current list's column
    func isAboveCurrent(column: Int) -> Bool {
        guard let current = current else { return true }
        return column > current.column
    }

    /// Check if a token's column indicates we should terminate lists
    /// Returns the number of lists to terminate (0 if none)
    /// - Parameter column: The column of the token being checked
    /// - Returns: Number of junction lists that should be terminated
    func listsToTerminate(atColumn column: Int) -> Int {
        var count = 0
        for info in stack.reversed() {
            if column <= info.column {
                count += 1
            } else {
                break
            }
        }
        return count
    }

    /// Terminate all lists where the given column is at or before the list's column
    /// - Parameter column: The column position to check against
    func terminateListsAtOrBefore(column: Int) {
        while let current = current, column <= current.column {
            terminateCurrentJunctionList()
        }
    }

    /// Reset all context (for starting a new parse)
    func reset() {
        stack.removeAll()
    }

    /// Debug description
    var debugDescription: String {
        if stack.isEmpty {
            return "JunctionListContext: empty"
        }
        let items = stack.map { info in
            let typeStr = info.type == .conjunction ? "/\\" : "\\/"
            return "\(typeStr)@col\(info.column)"
        }
        return "JunctionListContext: [\(items.joined(separator: ", "))]"
    }
}
