import SwiftUI

/// Provides symbol navigation and go-to-definition functionality
final class SymbolNavigator {
    static let shared = SymbolNavigator()

    private init() {}

    // MARK: - Symbol Types

    struct Symbol: Identifiable, Hashable {
        let id: UUID
        let name: String
        let kind: SymbolKind
        let location: SourceLocation
        let detail: String?

        init(
            id: UUID = UUID(),
            name: String,
            kind: SymbolKind,
            location: SourceLocation,
            detail: String? = nil
        ) {
            self.id = id
            self.name = name
            self.kind = kind
            self.location = location
            self.detail = detail
        }

        func hash(into hasher: inout Hasher) {
            hasher.combine(id)
        }

        static func == (lhs: Symbol, rhs: Symbol) -> Bool {
            lhs.id == rhs.id
        }
    }

    enum SymbolKind {
        case module
        case constant
        case variable
        case `operator`
        case theorem
        case assumption
        case definition
        case process      // PlusCal
        case procedure    // PlusCal
        case label        // PlusCal

        var icon: String {
            switch self {
            case .module: return "shippingbox"
            case .constant: return "c.circle"
            case .variable: return "v.circle"
            case .operator: return "function"
            case .theorem: return "t.circle"
            case .assumption: return "a.circle"
            case .definition: return "d.circle"
            case .process: return "gearshape.2"
            case .procedure: return "arrow.right.circle"
            case .label: return "tag"
            }
        }

        var color: Color {
            switch self {
            case .module: return .teal
            case .constant: return .cyan
            case .variable: return .blue
            case .operator: return .purple
            case .theorem: return .green
            case .assumption: return .orange
            case .definition: return .indigo
            case .process: return .pink
            case .procedure: return .red
            case .label: return .gray
            }
        }
    }

    // MARK: - Symbol Extraction

    func extractSymbols(from source: String) -> [Symbol] {
        var symbols: [Symbol] = []

        // Parse the source
        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            // Add module symbol
            symbols.append(Symbol(
                name: module.name,
                kind: .module,
                location: module.location
            ))

            // Extract symbols from declarations
            for decl in module.declarations {
                symbols.append(contentsOf: extractSymbols(from: decl))
            }

        case .failure:
            // Fall back to lexer-based extraction for broken code
            symbols.append(contentsOf: extractSymbolsFromTokens(source))
        }

        // Also extract PlusCal symbols
        symbols.append(contentsOf: extractPlusCalSymbols(from: source))

        return symbols
    }

    private func extractSymbols(from declaration: TLADeclaration) -> [Symbol] {
        var symbols: [Symbol] = []

        switch declaration {
        case .constant(let decl):
            for name in decl.names {
                symbols.append(Symbol(
                    name: name,
                    kind: .constant,
                    location: decl.location
                ))
            }

        case .variable(let decl):
            for name in decl.names {
                symbols.append(Symbol(
                    name: name,
                    kind: .variable,
                    location: decl.location
                ))
            }

        case .operatorDef(let def):
            let detail = def.parameters.isEmpty ? nil : "(\(def.parameterNames.joined(separator: ", ")))"
            symbols.append(Symbol(
                name: def.name,
                kind: .operator,
                location: def.location,
                detail: detail
            ))

        case .theorem(let decl):
            if let name = decl.name {
                symbols.append(Symbol(
                    name: name,
                    kind: .theorem,
                    location: decl.location
                ))
            }

        case .assumption(let decl):
            if let name = decl.name {
                symbols.append(Symbol(
                    name: name,
                    kind: .assumption,
                    location: decl.location
                ))
            }

        case .instance(let decl):
            if let name = decl.name {
                symbols.append(Symbol(
                    name: name,
                    kind: .definition,
                    location: decl.location,
                    detail: "INSTANCE \(decl.moduleName)"
                ))
            }

        case .specification(let decl):
            symbols.append(Symbol(
                name: decl.name,
                kind: .definition,
                location: decl.location,
                detail: "SPECIFICATION"
            ))

        case .invariant(let decl):
            for name in decl.names {
                symbols.append(Symbol(
                    name: name,
                    kind: .definition,
                    location: decl.location,
                    detail: "INVARIANT"
                ))
            }

        case .property(let decl):
            for name in decl.names {
                symbols.append(Symbol(
                    name: name,
                    kind: .definition,
                    location: decl.location,
                    detail: "PROPERTY"
                ))
            }

        case .recursiveDecl(let decl):
            // Forward declaration for recursive operator
            let params = decl.parameterCount > 0 ? "(\(Array(repeating: "_", count: decl.parameterCount).joined(separator: ", ")))" : ""
            symbols.append(Symbol(
                name: decl.name,
                kind: .operator,
                location: decl.location,
                detail: "RECURSIVE\(params)"
            ))
        }

        return symbols
    }

    private func extractSymbolsFromTokens(_ source: String) -> [Symbol] {
        var symbols: [Symbol] = []
        let lexer = TLALexer(source: source)
        let tokens = lexer.scanTokens()

        var i = 0
        while i < tokens.count {
            let token = tokens[i]

            switch token.type {
            case .keyword(let kw):
                switch kw {
                case .constant, .constants:
                    // Look for identifiers after CONSTANT
                    i += 1
                    while i < tokens.count {
                        if case .identifier(let name) = tokens[i].type {
                            symbols.append(Symbol(
                                name: name,
                                kind: .constant,
                                location: SourceLocation(
                                    line: tokens[i].line,
                                    column: tokens[i].column,
                                    length: tokens[i].length
                                )
                            ))
                        } else if case .comma = tokens[i].type {
                            // Continue
                        } else {
                            break
                        }
                        i += 1
                    }
                    continue

                case .variable, .variables:
                    i += 1
                    while i < tokens.count {
                        if case .identifier(let name) = tokens[i].type {
                            symbols.append(Symbol(
                                name: name,
                                kind: .variable,
                                location: SourceLocation(
                                    line: tokens[i].line,
                                    column: tokens[i].column,
                                    length: tokens[i].length
                                )
                            ))
                        } else if case .comma = tokens[i].type {
                            // Continue
                        } else {
                            break
                        }
                        i += 1
                    }
                    continue

                default:
                    break
                }

            case .identifier(let name):
                // Check if followed by == (definition)
                if i + 1 < tokens.count {
                    if case .operator(.define) = tokens[i + 1].type {
                        symbols.append(Symbol(
                            name: name,
                            kind: .operator,
                            location: SourceLocation(
                                line: token.line,
                                column: token.column,
                                length: token.length
                            )
                        ))
                    }
                }

            default:
                break
            }

            i += 1
        }

        return symbols
    }

    private func extractPlusCalSymbols(from source: String) -> [Symbol] {
        var symbols: [Symbol] = []
        let lines = source.components(separatedBy: "\n")

        for (lineIndex, line) in lines.enumerated() {
            let trimmed = line.trimmingCharacters(in: .whitespaces)

            // Process declarations
            if let range = trimmed.range(of: #"process\s+(\w+)"#, options: .regularExpression) {
                let match = String(trimmed[range])
                let name = match.replacingOccurrences(of: "process", with: "")
                    .trimmingCharacters(in: .whitespaces)
                symbols.append(Symbol(
                    name: name,
                    kind: .process,
                    location: SourceLocation(line: lineIndex + 1, column: 1, length: name.count)
                ))
            }

            // Procedure declarations
            if let range = trimmed.range(of: #"procedure\s+(\w+)"#, options: .regularExpression) {
                let match = String(trimmed[range])
                let name = match.replacingOccurrences(of: "procedure", with: "")
                    .trimmingCharacters(in: .whitespaces)
                symbols.append(Symbol(
                    name: name,
                    kind: .procedure,
                    location: SourceLocation(line: lineIndex + 1, column: 1, length: name.count)
                ))
            }

            // Labels (identifier followed by colon)
            if let colonIndex = trimmed.firstIndex(of: ":"),
               colonIndex != trimmed.startIndex {
                let beforeColon = String(trimmed[..<colonIndex]).trimmingCharacters(in: .whitespaces)
                if beforeColon.allSatisfy({ $0.isLetter || $0.isNumber || $0 == "_" }),
                   !beforeColon.isEmpty,
                   !["if", "while", "either", "with", "begin", "end"].contains(beforeColon) {
                    symbols.append(Symbol(
                        name: beforeColon,
                        kind: .label,
                        location: SourceLocation(line: lineIndex + 1, column: 1, length: beforeColon.count)
                    ))
                }
            }
        }

        return symbols
    }

    // MARK: - Symbol Lookup

    func findDefinition(of symbolName: String, in source: String) -> SourceLocation? {
        let symbols = extractSymbols(from: source)
        return symbols.first { $0.name == symbolName }?.location
    }

    func findReferences(to symbolName: String, in source: String) -> [SourceLocation] {
        var references: [SourceLocation] = []
        let lexer = TLALexer(source: source)
        let tokens = lexer.scanTokens()

        for token in tokens {
            if case .identifier(let name) = token.type, name == symbolName {
                references.append(SourceLocation(
                    line: token.line,
                    column: token.column,
                    length: token.length
                ))
            }
        }

        return references
    }

    // MARK: - Rename Symbol

    /// Renames all occurrences of a symbol in the source code
    func renameSymbol(from oldName: String, to newName: String, in source: String) -> (newSource: String, changesCount: Int) {
        let references = findReferences(to: oldName, in: source)
        guard !references.isEmpty else {
            return (source, 0)
        }

        // Sort references by position (reverse order) to replace from end to start
        // This preserves line/column positions during replacement
        let sortedRefs = references.sorted { ref1, ref2 in
            if ref1.line != ref2.line {
                return ref1.line > ref2.line
            }
            return ref1.column > ref2.column
        }

        var lines = source.components(separatedBy: "\n")
        var changesCount = 0

        for ref in sortedRefs {
            let lineIndex = ref.line - 1
            guard lineIndex >= 0 && lineIndex < lines.count else { continue }

            var line = lines[lineIndex]
            let startIndex = line.index(line.startIndex, offsetBy: ref.column - 1, limitedBy: line.endIndex) ?? line.endIndex
            let endIndex = line.index(startIndex, offsetBy: ref.length, limitedBy: line.endIndex) ?? line.endIndex

            // Verify the text at this location matches
            let existingText = String(line[startIndex..<endIndex])
            if existingText == oldName {
                line.replaceSubrange(startIndex..<endIndex, with: newName)
                lines[lineIndex] = line
                changesCount += 1
            }
        }

        return (lines.joined(separator: "\n"), changesCount)
    }

    /// Validates if a rename is safe (new name is a valid identifier and doesn't conflict)
    func validateRename(from oldName: String, to newName: String, in source: String) -> RenameValidation {
        // Check if new name is valid identifier
        guard !newName.isEmpty,
              newName.first?.isLetter == true || newName.first == "_",
              newName.allSatisfy({ $0.isLetter || $0.isNumber || $0 == "_" }) else {
            return .invalid("New name must be a valid identifier")
        }

        // Check if new name is a keyword
        let keywords = ["MODULE", "EXTENDS", "CONSTANT", "CONSTANTS", "VARIABLE", "VARIABLES",
                       "ASSUME", "THEOREM", "INSTANCE", "LOCAL", "LET", "IN", "IF", "THEN",
                       "ELSE", "CASE", "OTHER", "CHOOSE", "WITH", "EXCEPT", "ENABLED",
                       "UNCHANGED", "TRUE", "FALSE", "BOOLEAN", "STRING", "SUBSET", "UNION",
                       "DOMAIN", "SF_", "WF_"]
        if keywords.contains(newName.uppercased()) {
            return .invalid("'\(newName)' is a reserved keyword")
        }

        // Check if new name already exists
        let existingSymbols = extractSymbols(from: source)
        if existingSymbols.contains(where: { $0.name == newName && $0.name != oldName }) {
            return .conflict("A symbol named '\(newName)' already exists")
        }

        let references = findReferences(to: oldName, in: source)
        if references.isEmpty {
            return .invalid("No references to '\(oldName)' found")
        }

        return .valid(referenceCount: references.count)
    }

    enum RenameValidation {
        case valid(referenceCount: Int)
        case invalid(String)
        case conflict(String)

        var isValid: Bool {
            if case .valid = self { return true }
            return false
        }

        var message: String? {
            switch self {
            case .valid(let count):
                return "Will rename \(count) occurrence\(count == 1 ? "" : "s")"
            case .invalid(let msg), .conflict(let msg):
                return msg
            }
        }
    }
}

// MARK: - Symbol List View

struct SymbolListView: View {
    let symbols: [SymbolNavigator.Symbol]
    let onSelect: (SymbolNavigator.Symbol) -> Void
    @State private var searchText = ""
    @State private var selectedKind: SymbolNavigator.SymbolKind?

    var filteredSymbols: [SymbolNavigator.Symbol] {
        symbols.filter { symbol in
            let matchesSearch = searchText.isEmpty ||
                symbol.name.localizedCaseInsensitiveContains(searchText)
            let matchesKind = selectedKind == nil || symbol.kind == selectedKind
            return matchesSearch && matchesKind
        }
    }

    var groupedSymbols: [(kind: SymbolNavigator.SymbolKind, symbols: [SymbolNavigator.Symbol])] {
        let grouped = Dictionary(grouping: filteredSymbols, by: \.kind)
        return grouped.map { (kind: $0.key, symbols: $0.value) }
            .sorted { $0.kind.icon < $1.kind.icon }
    }

    var body: some View {
        VStack(spacing: 0) {
            // Search bar
            HStack {
                Image(systemName: "magnifyingglass")
                    .foregroundStyle(.secondary)
                TextField("Search symbols...", text: $searchText)
                    .textFieldStyle(.plain)
                if !searchText.isEmpty {
                    Button(action: { searchText = "" }) {
                        Image(systemName: "xmark.circle.fill")
                            .foregroundStyle(.secondary)
                    }
                    .buttonStyle(.plain)
                }
            }
            .padding(8)
            .background(.quaternary)

            // Filter chips
            ScrollView(.horizontal, showsIndicators: false) {
                HStack(spacing: 8) {
                    FilterChipView(title: "All", isSelected: selectedKind == nil) {
                        selectedKind = nil
                    }
                    ForEach(allKinds, id: \.icon) { kind in
                        FilterChipView(
                            title: kindName(kind),
                            icon: kind.icon,
                            color: kind.color,
                            isSelected: selectedKind == kind
                        ) {
                            selectedKind = selectedKind == kind ? nil : kind
                        }
                    }
                }
                .padding(.horizontal, 8)
                .padding(.vertical, 4)
            }
            .background(.bar)

            Divider()

            // Symbol list
            List {
                ForEach(groupedSymbols, id: \.kind.icon) { group in
                    Section(kindName(group.kind)) {
                        ForEach(group.symbols) { symbol in
                            SymbolRowView(symbol: symbol)
                                .onTapGesture { onSelect(symbol) }
                        }
                    }
                }
            }
            .listStyle(.plain)
        }
    }

    private var allKinds: [SymbolNavigator.SymbolKind] {
        [.module, .constant, .variable, .operator, .theorem, .definition, .process, .procedure, .label]
    }

    private func kindName(_ kind: SymbolNavigator.SymbolKind) -> String {
        switch kind {
        case .module: return "Modules"
        case .constant: return "Constants"
        case .variable: return "Variables"
        case .operator: return "Operators"
        case .theorem: return "Theorems"
        case .assumption: return "Assumptions"
        case .definition: return "Definitions"
        case .process: return "Processes"
        case .procedure: return "Procedures"
        case .label: return "Labels"
        }
    }
}

// FilterChip replaced with FilterChipView from SharedComponents.swift

struct SymbolRowView: View {
    let symbol: SymbolNavigator.Symbol

    var body: some View {
        HStack(spacing: 12) {
            Image(systemName: symbol.kind.icon)
                .foregroundStyle(symbol.kind.color)
                .frame(width: 20)

            VStack(alignment: .leading, spacing: 2) {
                HStack(spacing: 4) {
                    Text(symbol.name)
                        .font(.system(.body, design: .monospaced))

                    if let detail = symbol.detail {
                        Text(detail)
                            .font(.system(.caption, design: .monospaced))
                            .foregroundStyle(.secondary)
                    }
                }

                Text("Line \(symbol.location.line)")
                    .font(.caption)
                    .foregroundStyle(.tertiary)
            }

            Spacer()

            Image(systemName: "chevron.right")
                .font(.caption)
                .foregroundStyle(.tertiary)
        }
        .padding(.vertical, 4)
    }
}

// MARK: - References View

/// View showing all references to a symbol
struct ReferencesView: View {
    let symbolName: String
    let references: [SourceLocation]
    let source: String
    let onSelect: (SourceLocation) -> Void

    var body: some View {
        VStack(alignment: .leading, spacing: 0) {
            // Header
            HStack {
                Label(
                    "\(references.count) reference\(references.count == 1 ? "" : "s") to '\(symbolName)'",
                    systemImage: "link"
                )
                .font(.headline)

                Spacer()
            }
            .padding()
            .background(.bar)

            Divider()

            // References list
            List {
                ForEach(references.indices, id: \.self) { index in
                    let ref = references[index]
                    ReferenceRow(
                        location: ref,
                        lineContent: getLineContent(at: ref.line),
                        onSelect: { onSelect(ref) }
                    )
                }
            }
            .listStyle(.plain)
        }
    }

    private func getLineContent(at lineNumber: Int) -> String {
        let lines = source.components(separatedBy: "\n")
        guard lineNumber > 0 && lineNumber <= lines.count else {
            return ""
        }
        return lines[lineNumber - 1].trimmingCharacters(in: .whitespaces)
    }
}

struct ReferenceRow: View {
    let location: SourceLocation
    let lineContent: String
    let onSelect: () -> Void

    var body: some View {
        Button(action: onSelect) {
            HStack(alignment: .top, spacing: 12) {
                // Line number
                Text("L\(location.line)")
                    .font(.system(.caption, design: .monospaced))
                    .foregroundStyle(.secondary)
                    .frame(width: 40, alignment: .trailing)

                // Line content
                Text(lineContent)
                    .font(.system(.caption, design: .monospaced))
                    .foregroundStyle(.primary)
                    .lineLimit(1)
                    .truncationMode(.tail)

                Spacer()

                Image(systemName: "chevron.right")
                    .font(.caption2)
                    .foregroundStyle(.tertiary)
            }
            .padding(.vertical, 4)
        }
        .buttonStyle(.plain)
    }
}

// MARK: - Rename Dialog View

/// Dialog for renaming a symbol
struct RenameSymbolView: View {
    @Binding var isPresented: Bool
    let symbolName: String
    let source: String
    let onRename: (String, Int) -> Void

    @State private var newName: String = ""
    @State private var validation: SymbolNavigator.RenameValidation?

    var body: some View {
        VStack(alignment: .leading, spacing: 16) {
            Text("Rename Symbol")
                .font(.headline)

            Text("Rename '\(symbolName)' to:")
                .font(.subheadline)
                .foregroundStyle(.secondary)

            TextField("New name", text: $newName)
                .textFieldStyle(.roundedBorder)
                .font(.system(.body, design: .monospaced))
                .onChange(of: newName) { _, _ in
                    validateNewName()
                }

            if let validation = validation {
                HStack {
                    Image(systemName: validation.isValid ? "checkmark.circle.fill" : "exclamationmark.circle.fill")
                        .foregroundStyle(validation.isValid ? .green : .red)

                    Text(validation.message ?? "")
                        .font(.caption)
                        .foregroundColor(validation.isValid ? .secondary : .red)
                }
            }

            HStack {
                Spacer()

                Button("Cancel") {
                    isPresented = false
                }
                .buttonStyle(.bordered)

                Button("Rename") {
                    performRename()
                }
                .buttonStyle(.borderedProminent)
                .disabled(validation?.isValid != true)
            }
        }
        .padding()
        .frame(minWidth: 300)
        .onAppear {
            newName = symbolName
            validateNewName()
        }
    }

    private func validateNewName() {
        if newName == symbolName {
            validation = nil
            return
        }
        validation = SymbolNavigator.shared.validateRename(
            from: symbolName,
            to: newName,
            in: source
        )
    }

    private func performRename() {
        let result = SymbolNavigator.shared.renameSymbol(
            from: symbolName,
            to: newName,
            in: source
        )
        onRename(result.newSource, result.changesCount)
        isPresented = false
    }
}

#Preview {
    SymbolListView(
        symbols: [
            SymbolNavigator.Symbol(name: "Init", kind: .operator, location: SourceLocation(line: 5, column: 1, length: 4)),
            SymbolNavigator.Symbol(name: "Next", kind: .operator, location: SourceLocation(line: 10, column: 1, length: 4)),
            SymbolNavigator.Symbol(name: "x", kind: .variable, location: SourceLocation(line: 3, column: 1, length: 1)),
            SymbolNavigator.Symbol(name: "N", kind: .constant, location: SourceLocation(line: 2, column: 1, length: 1)),
        ],
        onSelect: { _ in }
    )
}
