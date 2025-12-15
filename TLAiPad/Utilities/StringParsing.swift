import Foundation

// MARK: - String Parsing Utilities

/// Extracts the text after a keyword, removing the keyword and trimming whitespace
/// - Parameters:
///   - text: The input text containing the keyword
///   - keyword: The keyword to remove from the beginning
/// - Returns: The text after the keyword, trimmed of whitespace
func extractAfterKeyword(_ text: String, _ keyword: String) -> String {
    text.replacingOccurrences(of: keyword, with: "").trimmingCharacters(in: .whitespaces)
}

// MARK: - String Extensions for TLA+ Parsing

extension String {
    /// Extracts the value after a TLA+ keyword
    /// - Parameter keyword: The TLA+ keyword (e.g., "INIT", "NEXT", "SPECIFICATION")
    /// - Returns: The value after the keyword, trimmed
    func afterKeyword(_ keyword: String) -> String {
        extractAfterKeyword(self, keyword)
    }

    /// Checks if this string starts with a TLA+ keyword (case-sensitive)
    /// - Parameter keyword: The keyword to check for
    /// - Returns: True if the trimmed string starts with the keyword
    func startsWithKeyword(_ keyword: String) -> Bool {
        self.trimmingCharacters(in: .whitespaces).hasPrefix(keyword)
    }

    /// Extracts content between delimiters
    /// - Parameters:
    ///   - start: The starting delimiter
    ///   - end: The ending delimiter
    /// - Returns: The content between delimiters, or nil if not found
    func contentBetween(_ start: String, _ end: String) -> String? {
        guard let startRange = range(of: start),
              let endRange = range(of: end, range: startRange.upperBound..<endIndex) else {
            return nil
        }
        return String(self[startRange.upperBound..<endRange.lowerBound])
    }

    /// Splits the string by a separator, trimming each component
    /// - Parameter separator: The separator to split by
    /// - Returns: Array of trimmed components
    func splitAndTrim(by separator: Character) -> [String] {
        self.split(separator: separator).map { String($0).trimmingCharacters(in: .whitespaces) }
    }
}

// MARK: - TLA+ Config Parsing Helpers

enum TLAConfigKeyword: String, CaseIterable {
    case specification = "SPECIFICATION"
    case initState = "INIT"
    case next = "NEXT"
    case invariant = "INVARIANT"
    case property = "PROPERTY"
    case constant = "CONSTANT"
    case constants = "CONSTANTS"
    case symmetry = "SYMMETRY"
    case constraint = "CONSTRAINT"
    case actionConstraint = "ACTION_CONSTRAINT"
    case view = "VIEW"
    case checkDeadlock = "CHECK_DEADLOCK"

    /// Extracts the value for this keyword from a line
    func extractValue(from line: String) -> String {
        extractAfterKeyword(line, rawValue)
    }
}

// MARK: - TLA+ Temporal Operator Parsing

enum TemporalOperator: String, CaseIterable {
    case alwaysEventually = "[]<>"
    case eventuallyAlways = "<>[]"
    case eventually = "<>"
    case always = "[]"

    /// Extracts the predicate from a temporal formula
    func extractPredicate(from formula: String) -> String {
        extractAfterKeyword(formula, rawValue)
    }

    /// Detects which temporal operator (if any) prefixes the formula
    static func detect(in formula: String) -> TemporalOperator? {
        let trimmed = formula.trimmingCharacters(in: .whitespaces)
        // Check longer operators first
        for op in [alwaysEventually, eventuallyAlways, eventually, always] {
            if trimmed.hasPrefix(op.rawValue) {
                return op
            }
        }
        return nil
    }
}
