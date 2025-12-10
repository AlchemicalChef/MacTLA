import SwiftUI

/// Provides real-time diagnostics for TLA+ code
final class TLADiagnostics {
    static let shared = TLADiagnostics()

    private init() {}

    struct Diagnostic: Identifiable {
        let id = UUID()
        let severity: Severity
        let message: String
        let location: SourceLocation
        let suggestions: [FixSuggestion]

        enum Severity {
            case error
            case warning
            case info
            case hint

            var icon: String {
                switch self {
                case .error: return "xmark.circle.fill"
                case .warning: return "exclamationmark.triangle.fill"
                case .info: return "info.circle.fill"
                case .hint: return "lightbulb.fill"
                }
            }

            var color: Color {
                switch self {
                case .error: return .red
                case .warning: return .orange
                case .info: return .blue
                case .hint: return .green
                }
            }
        }

        struct FixSuggestion {
            let title: String
            let replacement: String
            let range: Range<Int>?
        }
    }

    func analyze(_ source: String) -> [Diagnostic] {
        var diagnostics: [Diagnostic] = []

        // Parse to find syntax errors
        let parser = TLAParser()
        let result = parser.parse(source)

        if case .failure(let parseErrors) = result {
            for error in parseErrors.errors {
                diagnostics.append(Diagnostic(
                    severity: .error,
                    message: error.message,
                    location: error.location,
                    suggestions: []
                ))
            }
        }

        // Additional semantic checks
        diagnostics.append(contentsOf: checkSemantics(source))

        // Style warnings
        diagnostics.append(contentsOf: checkStyle(source))

        return diagnostics
    }

    private func checkSemantics(_ source: String) -> [Diagnostic] {
        var diagnostics: [Diagnostic] = []

        let lexer = TLALexer(source: source)
        let tokens = lexer.scanTokens()

        // Track declarations
        var declaredVariables = Set<String>()
        var declaredConstants = Set<String>()
        var extendedModules = Set<String>()
        var definedOperators = Set<String>()
        var usedIdentifiers = Set<String>()
        var primedVariables = Set<String>()

        // Standard modules and their operators
        let standardModules: [String: Set<String>] = [
            "Naturals": ["Nat", "Int", "+", "-", "*", "^", "<", ">", "<=", ">=", "..", "\\div", "%"],
            "Integers": ["Int", "+", "-", "*", "^", "<", ">", "<=", ">=", "..", "\\div", "%"],
            "Sequences": ["Seq", "Len", "Head", "Tail", "Append", "\\o", "SubSeq", "SelectSeq"],
            "FiniteSets": ["Cardinality", "IsFiniteSet"],
            "Bags": ["BagIn", "BagOfAll", "BagToSet", "BagCardinality", "CopiesIn", "EmptyBag", "SetToBag", "(+)", "(-)"],
            "TLC": ["Print", "Assert", "PrintT", "JavaTime", "TLCGet", "TLCSet", ":>", "@@"]
        ]

        // First pass: collect declarations
        var i = 0
        while i < tokens.count {
            let token = tokens[i]

            switch token.type {
            case .keyword(.variables), .keyword(.variable):
                // Collect variable names
                i += 1
                while i < tokens.count {
                    if case .identifier(let name) = tokens[i].type {
                        declaredVariables.insert(name)
                    } else if tokens[i].type != .comma {
                        break
                    }
                    i += 1
                }
                continue

            case .keyword(.constants), .keyword(.constant):
                // Collect constant names
                i += 1
                while i < tokens.count {
                    if case .identifier(let name) = tokens[i].type {
                        declaredConstants.insert(name)
                    } else if tokens[i].type != .comma {
                        break
                    }
                    i += 1
                }
                continue

            case .keyword(.extends):
                // Collect extended modules
                i += 1
                while i < tokens.count {
                    if case .identifier(let name) = tokens[i].type {
                        extendedModules.insert(name)
                    } else if tokens[i].type != .comma {
                        break
                    }
                    i += 1
                }
                continue

            case .identifier(let name):
                // Check if this is an operator definition
                if i + 1 < tokens.count {
                    let nextToken = tokens[i + 1]
                    if case .operator(.define) = nextToken.type {
                        definedOperators.insert(name)
                    } else if case .leftParen = nextToken.type {
                        // Could be operator definition with params
                        var j = i + 2
                        var parenDepth = 1
                        while j < tokens.count && parenDepth > 0 {
                            if case .leftParen = tokens[j].type { parenDepth += 1 }
                            if case .rightParen = tokens[j].type { parenDepth -= 1 }
                            j += 1
                        }
                        if j < tokens.count, case .operator(.define) = tokens[j].type {
                            definedOperators.insert(name)
                        }
                    }
                }
                usedIdentifiers.insert(name)

            case .operator(.prime):
                // Track what was primed (previous identifier)
                if i > 0, case .identifier(let name) = tokens[i - 1].type {
                    primedVariables.insert(name)
                }

            default:
                break
            }
            i += 1
        }

        // Second pass: check for issues

        // Check for primed non-variables
        for primedVar in primedVariables {
            if !declaredVariables.contains(primedVar) && !primedVar.isEmpty {
                // Find location
                for token in tokens {
                    if case .identifier(let name) = token.type, name == primedVar {
                        diagnostics.append(Diagnostic(
                            severity: .warning,
                            message: "'\(primedVar)' is primed but not declared as a VARIABLE",
                            location: SourceLocation(line: token.line, column: token.column, length: token.length),
                            suggestions: [
                                Diagnostic.FixSuggestion(
                                    title: "Add to VARIABLES",
                                    replacement: "VARIABLES \(primedVar)",
                                    range: nil
                                )
                            ]
                        ))
                        break
                    }
                }
            }
        }

        // Check for used but undefined identifiers
        // Add operators from extended standard modules to known identifiers
        var knownIdentifiers = declaredVariables
            .union(declaredConstants)
            .union(definedOperators)
            .union(Set(["TRUE", "FALSE", "BOOLEAN", "STRING"]))

        for module in extendedModules {
            if let ops = standardModules[module] {
                knownIdentifiers = knownIdentifiers.union(ops)
            }
        }

        // Check for missing standard module extends
        let needsNaturals = source.contains("..") || source.contains("\\div") || source.range(of: #"\b\d+\s*[+\-*/%^<>]"#, options: .regularExpression) != nil
        let needsSequences = source.contains("<<") || source.contains("Len(") || source.contains("Head(") || source.contains("Tail(") || source.contains("\\o")

        if needsNaturals && !extendedModules.contains("Naturals") && !extendedModules.contains("Integers") {
            diagnostics.append(Diagnostic(
                severity: .warning,
                message: "Arithmetic operations used but Naturals/Integers not extended",
                location: SourceLocation(line: 1, column: 1, length: 0),
                suggestions: [
                    Diagnostic.FixSuggestion(
                        title: "Add EXTENDS Naturals",
                        replacement: "EXTENDS Naturals",
                        range: nil
                    )
                ]
            ))
        }

        if needsSequences && !extendedModules.contains("Sequences") {
            diagnostics.append(Diagnostic(
                severity: .warning,
                message: "Sequence operations used but Sequences not extended",
                location: SourceLocation(line: 1, column: 1, length: 0),
                suggestions: [
                    Diagnostic.FixSuggestion(
                        title: "Add EXTENDS Sequences",
                        replacement: "EXTENDS Sequences",
                        range: nil
                    )
                ]
            ))
        }

        // Check for common issues
        diagnostics.append(contentsOf: checkCommonIssues(source, tokens: tokens))

        return diagnostics
    }

    private func checkCommonIssues(_ source: String, tokens: [TLAToken]) -> [Diagnostic] {
        var diagnostics: [Diagnostic] = []

        // Check for unbalanced brackets
        var parenCount = 0
        var bracketCount = 0
        var braceCount = 0

        for token in tokens {
            switch token.type {
            case .leftParen: parenCount += 1
            case .rightParen: parenCount -= 1
            case .leftBracket: bracketCount += 1
            case .rightBracket: bracketCount -= 1
            case .leftBrace: braceCount += 1
            case .rightBrace: braceCount -= 1
            default: break
            }

            if parenCount < 0 {
                diagnostics.append(Diagnostic(
                    severity: .error,
                    message: "Unmatched closing parenthesis",
                    location: SourceLocation(line: token.line, column: token.column, length: 1),
                    suggestions: []
                ))
                parenCount = 0
            }
            if bracketCount < 0 {
                diagnostics.append(Diagnostic(
                    severity: .error,
                    message: "Unmatched closing bracket",
                    location: SourceLocation(line: token.line, column: token.column, length: 1),
                    suggestions: []
                ))
                bracketCount = 0
            }
            if braceCount < 0 {
                diagnostics.append(Diagnostic(
                    severity: .error,
                    message: "Unmatched closing brace",
                    location: SourceLocation(line: token.line, column: token.column, length: 1),
                    suggestions: []
                ))
                braceCount = 0
            }
        }

        // Check for module structure
        var hasModuleStart = false
        var hasModuleEnd = false

        for token in tokens {
            if case .moduleStart = token.type { hasModuleStart = true }
            if case .moduleEnd = token.type { hasModuleEnd = true }
        }

        if !hasModuleStart {
            diagnostics.append(Diagnostic(
                severity: .error,
                message: "Missing module header (---- MODULE name ----)",
                location: SourceLocation(line: 1, column: 1, length: 0),
                suggestions: [
                    Diagnostic.FixSuggestion(
                        title: "Add module header",
                        replacement: "---- MODULE ModuleName ----\n",
                        range: nil
                    )
                ]
            ))
        }

        if hasModuleStart && !hasModuleEnd {
            diagnostics.append(Diagnostic(
                severity: .error,
                message: "Missing module footer (====)",
                location: SourceLocation(line: source.components(separatedBy: "\n").count, column: 1, length: 0),
                suggestions: [
                    Diagnostic.FixSuggestion(
                        title: "Add module footer",
                        replacement: "\n====\n",
                        range: nil
                    )
                ]
            ))
        }

        return diagnostics
    }

    private func checkStyle(_ source: String) -> [Diagnostic] {
        var diagnostics: [Diagnostic] = []
        let lines = source.components(separatedBy: "\n")

        for (index, line) in lines.enumerated() {
            // Check for very long lines
            if line.count > 120 {
                diagnostics.append(Diagnostic(
                    severity: .hint,
                    message: "Line exceeds 120 characters",
                    location: SourceLocation(line: index + 1, column: 121, length: line.count - 120),
                    suggestions: []
                ))
            }

            // Check for tabs (prefer spaces in TLA+)
            if line.contains("\t") {
                diagnostics.append(Diagnostic(
                    severity: .hint,
                    message: "Consider using spaces instead of tabs",
                    location: SourceLocation(line: index + 1, column: 1, length: line.count),
                    suggestions: []
                ))
            }
        }

        return diagnostics
    }
}

// MARK: - Diagnostics View

struct DiagnosticsListView: View {
    let diagnostics: [TLADiagnostics.Diagnostic]
    let onSelect: (TLADiagnostics.Diagnostic) -> Void

    var body: some View {
        List(diagnostics) { diagnostic in
            DiagnosticRowView(diagnostic: diagnostic)
                .onTapGesture { onSelect(diagnostic) }
        }
        .listStyle(.plain)
    }
}

struct DiagnosticRowView: View {
    let diagnostic: TLADiagnostics.Diagnostic

    var body: some View {
        HStack(spacing: 12) {
            Image(systemName: diagnostic.severity.icon)
                .foregroundStyle(diagnostic.severity.color)

            VStack(alignment: .leading, spacing: 4) {
                Text(diagnostic.message)
                    .font(.subheadline)

                Text("Line \(diagnostic.location.line), Column \(diagnostic.location.column)")
                    .font(.caption)
                    .foregroundStyle(.secondary)

                if !diagnostic.suggestions.isEmpty {
                    ForEach(diagnostic.suggestions, id: \.title) { suggestion in
                        Button(action: {}) {
                            Label(suggestion.title, systemImage: "wand.and.stars")
                                .font(.caption)
                        }
                        .buttonStyle(.bordered)
                        .controlSize(.small)
                    }
                }
            }
        }
        .padding(.vertical, 4)
    }
}

struct DiagnosticsInlineView: View {
    let diagnostic: TLADiagnostics.Diagnostic

    var body: some View {
        HStack(spacing: 4) {
            Image(systemName: diagnostic.severity.icon)
                .font(.caption)

            Text(diagnostic.message)
                .font(.caption)
        }
        .foregroundStyle(diagnostic.severity.color)
        .padding(.horizontal, 8)
        .padding(.vertical, 2)
        .background(diagnostic.severity.color.opacity(0.1))
        .clipShape(Capsule())
    }
}

#Preview {
    DiagnosticsListView(
        diagnostics: [
            TLADiagnostics.Diagnostic(
                severity: .error,
                message: "Undefined variable: foo",
                location: SourceLocation(line: 10, column: 5, length: 3),
                suggestions: []
            ),
            TLADiagnostics.Diagnostic(
                severity: .warning,
                message: "Variable 'x' is never primed",
                location: SourceLocation(line: 15, column: 1, length: 1),
                suggestions: [
                    TLADiagnostics.Diagnostic.FixSuggestion(
                        title: "Add to UNCHANGED",
                        replacement: "UNCHANGED x",
                        range: nil
                    )
                ]
            )
        ],
        onSelect: { _ in }
    )
}
