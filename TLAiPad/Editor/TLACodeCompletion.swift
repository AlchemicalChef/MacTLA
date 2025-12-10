import SwiftUI

/// Provides code completion suggestions for TLA+ code
final class TLACodeCompletion {
    static let shared = TLACodeCompletion()

    private init() {}

    struct Suggestion: Identifiable {
        let id = UUID()
        let text: String
        let displayText: String
        let category: Category
        let detail: String?
        let insertText: String

        enum Category {
            case keyword
            case `operator`
            case identifier
            case snippet
            case module

            var icon: String {
                switch self {
                case .keyword: return "k.circle.fill"
                case .operator: return "function"
                case .identifier: return "textformat"
                case .snippet: return "doc.text"
                case .module: return "shippingbox"
                }
            }

            var color: Color {
                switch self {
                case .keyword: return .purple
                case .operator: return .blue
                case .identifier: return .primary
                case .snippet: return .orange
                case .module: return .teal
                }
            }
        }
    }

    // Standard library modules
    private let standardModules = [
        ("Naturals", "Natural number operators (+, -, *, \\div, %, ..)"),
        ("Integers", "Integer operators including negative numbers"),
        ("Reals", "Real number operators"),
        ("Sequences", "Sequence operators (Append, Head, Tail, Len, etc.)"),
        ("FiniteSets", "Finite set operators (Cardinality, IsFiniteSet)"),
        ("Bags", "Bag/multiset operators"),
        ("TLC", "TLC model checker operators (Print, Assert, etc.)"),
        ("TLAPS", "TLA+ proof system definitions"),
    ]

    // Keyword suggestions
    private let keywords: [(String, String)] = [
        ("MODULE", "Module declaration"),
        ("EXTENDS", "Import standard modules"),
        ("CONSTANT", "Declare constants"),
        ("CONSTANTS", "Declare multiple constants"),
        ("VARIABLE", "Declare a variable"),
        ("VARIABLES", "Declare multiple variables"),
        ("ASSUME", "State an assumption"),
        ("THEOREM", "Declare a theorem"),
        ("INSTANCE", "Instantiate a module"),
        ("LOCAL", "Local definition"),
        ("LET", "Local definitions block"),
        ("IN", "Body of LET expression"),
        ("IF", "Conditional expression"),
        ("THEN", "Then branch"),
        ("ELSE", "Else branch"),
        ("CASE", "Case expression"),
        ("OTHER", "Default case"),
        ("CHOOSE", "Choose operator"),
        ("ENABLED", "Action enablement"),
        ("UNCHANGED", "Unchanged variables"),
        ("SUBSET", "Power set"),
        ("UNION", "Distributed union"),
        ("DOMAIN", "Function domain"),
    ]

    // Operator suggestions
    private let operators: [(String, String, String)] = [
        ("/\\", "Conjunction", " /\\ "),
        ("\\/", "Disjunction", " \\/ "),
        ("~", "Negation", "~"),
        ("=>", "Implication", " => "),
        ("<=>", "Equivalence", " <=> "),
        ("\\A", "Universal quantifier", "\\A x \\in S : "),
        ("\\E", "Existential quantifier", "\\E x \\in S : "),
        ("\\in", "Set membership", " \\in "),
        ("\\notin", "Not in set", " \\notin "),
        ("\\subseteq", "Subset or equal", " \\subseteq "),
        ("\\cup", "Set union", " \\cup "),
        ("\\cap", "Set intersection", " \\cap "),
        ("\\X", "Cartesian product", " \\X "),
        ("|->", "Maps to", " |-> "),
        ("==", "Definition", " == "),
        ("[]", "Always (temporal)", "[]"),
        ("<>", "Eventually (temporal)", "<>"),
        ("~>", "Leads to", " ~> "),
        ("'", "Next state (prime)", "'"),
    ]

    // Code snippets
    private let snippets: [(String, String, String)] = [
        ("module", "Module template", """
            ---- MODULE ${1:ModuleName} ----
            EXTENDS Naturals, Sequences

            VARIABLES ${2:var}

            Init == ${3:TRUE}

            Next == ${4:TRUE}

            Spec == Init /\\ [][Next]_<<${2:var}>>

            ====
            """),
        ("invariant", "Invariant template", """
            ${1:InvariantName} ==
                ${2:TRUE}
            """),
        ("action", "Action template", """
            ${1:ActionName} ==
                /\\ ${2:guard}
                /\\ ${3:effect}'
                /\\ UNCHANGED <<${4:vars}>>
            """),
        ("pluscal", "PlusCal algorithm template", """
            (*--algorithm ${1:AlgorithmName}
            variables ${2:x} = ${3:0};

            begin
              ${4:Label}:
                skip;
            end algorithm; *)
            """),
        ("process", "PlusCal process template", """
            process ${1:ProcessName} = ${2:1}
            begin
              ${3:Label}:
                skip;
            end process;
            """),
        ("function", "Function definition", """
            ${1:FunctionName}[${2:x} \\in ${3:Domain}] == ${4:body}
            """),
        ("record", "Record constructor", """
            [${1:field1} |-> ${2:value1}, ${3:field2} |-> ${4:value2}]
            """),
    ]

    func suggestions(for prefix: String, context: CompletionContext) -> [Suggestion] {
        var results: [Suggestion] = []

        let lowercasedPrefix = prefix.lowercased()

        // Add keyword suggestions
        for (keyword, detail) in keywords {
            if keyword.lowercased().hasPrefix(lowercasedPrefix) || prefix.isEmpty {
                results.append(Suggestion(
                    text: keyword,
                    displayText: keyword,
                    category: .keyword,
                    detail: detail,
                    insertText: keyword
                ))
            }
        }

        // Add operator suggestions
        for (op, detail, insertText) in operators {
            if op.lowercased().hasPrefix(lowercasedPrefix) || prefix.isEmpty {
                results.append(Suggestion(
                    text: op,
                    displayText: op,
                    category: .operator,
                    detail: detail,
                    insertText: insertText
                ))
            }
        }

        // Add module suggestions (for EXTENDS)
        if context.isAfterExtends {
            for (module, detail) in standardModules {
                if module.lowercased().hasPrefix(lowercasedPrefix) || prefix.isEmpty {
                    results.append(Suggestion(
                        text: module,
                        displayText: module,
                        category: .module,
                        detail: detail,
                        insertText: module
                    ))
                }
            }
        }

        // Add snippet suggestions
        for (name, detail, template) in snippets {
            if name.lowercased().hasPrefix(lowercasedPrefix) || prefix.isEmpty {
                results.append(Suggestion(
                    text: name,
                    displayText: name,
                    category: .snippet,
                    detail: detail,
                    insertText: template
                ))
            }
        }

        // Add identifiers from context
        for identifier in context.availableIdentifiers {
            if identifier.lowercased().hasPrefix(lowercasedPrefix) {
                results.append(Suggestion(
                    text: identifier,
                    displayText: identifier,
                    category: .identifier,
                    detail: nil,
                    insertText: identifier
                ))
            }
        }

        return results.sorted { $0.text < $1.text }
    }

    struct CompletionContext {
        var isAfterExtends: Bool = false
        var isInExpression: Bool = false
        var isInAction: Bool = false
        var availableIdentifiers: [String] = []

        static func analyze(_ content: String, cursorPosition: Int) -> CompletionContext {
            var context = CompletionContext()

            let beforeCursor = String(content.prefix(cursorPosition))
            let lines = beforeCursor.components(separatedBy: "\n")

            // Check if we're after EXTENDS
            if let lastLine = lines.last?.trimmingCharacters(in: .whitespaces) {
                context.isAfterExtends = lastLine.hasPrefix("EXTENDS")
            }

            // Extract identifiers from the content
            let lexer = TLALexer(source: content)
            let tokens = lexer.scanTokens()

            var identifiers = Set<String>()
            for token in tokens {
                if case .identifier(let name) = token.type {
                    identifiers.insert(name)
                }
            }
            context.availableIdentifiers = Array(identifiers)

            return context
        }
    }
}

// MARK: - Completion View

struct CompletionPopupView: View {
    let suggestions: [TLACodeCompletion.Suggestion]
    let onSelect: (TLACodeCompletion.Suggestion) -> Void
    @State private var selectedIndex = 0

    var body: some View {
        VStack(spacing: 0) {
            ForEach(Array(suggestions.enumerated()), id: \.element.id) { index, suggestion in
                CompletionRowView(
                    suggestion: suggestion,
                    isSelected: index == selectedIndex
                )
                .onTapGesture {
                    onSelect(suggestion)
                }
            }
        }
        .frame(width: 300)
        .background(.ultraThinMaterial)
        .clipShape(RoundedRectangle(cornerRadius: 8))
        .shadow(radius: 4)
    }
}

struct CompletionRowView: View {
    let suggestion: TLACodeCompletion.Suggestion
    let isSelected: Bool

    var body: some View {
        HStack(spacing: 8) {
            Image(systemName: suggestion.category.icon)
                .foregroundStyle(suggestion.category.color)
                .frame(width: 20)

            VStack(alignment: .leading, spacing: 2) {
                Text(suggestion.displayText)
                    .font(.system(.body, design: .monospaced))

                if let detail = suggestion.detail {
                    Text(detail)
                        .font(.caption)
                        .foregroundStyle(.secondary)
                }
            }

            Spacer()
        }
        .padding(.horizontal, 8)
        .padding(.vertical, 4)
        .background(isSelected ? Color.accentColor.opacity(0.2) : Color.clear)
    }
}

#Preview {
    CompletionPopupView(
        suggestions: TLACodeCompletion.shared.suggestions(
            for: "",
            context: TLACodeCompletion.CompletionContext()
        ),
        onSelect: { _ in }
    )
}
