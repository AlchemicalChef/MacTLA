import SwiftUI

/// Search and replace functionality for the TLA+ editor
struct SearchReplaceView: View {
    @Binding var content: String
    @Binding var isPresented: Bool
    @State private var searchText = ""
    @State private var replaceText = ""
    @State private var matchCase = false
    @State private var useRegex = false
    @State private var wholeWord = false
    @State private var currentMatchIndex = 0
    @State private var matches: [SearchMatch] = []
    @FocusState private var focusedField: Field?

    enum Field {
        case search, replace
    }

    var body: some View {
        VStack(spacing: 0) {
            // Search bar
            HStack(spacing: 8) {
                Image(systemName: "magnifyingglass")
                    .foregroundStyle(.secondary)

                TextField("Search", text: $searchText)
                    .textFieldStyle(.plain)
                    .focused($focusedField, equals: .search)
                    .onSubmit { findNext() }
                    .onChange(of: searchText) { _, _ in
                        performSearch()
                    }

                if !matches.isEmpty {
                    Text("\(currentMatchIndex + 1)/\(matches.count)")
                        .font(.caption)
                        .foregroundStyle(.secondary)
                        .monospacedDigit()
                }

                Button(action: findPrevious) {
                    Image(systemName: "chevron.up")
                }
                .disabled(matches.isEmpty)

                Button(action: findNext) {
                    Image(systemName: "chevron.down")
                }
                .disabled(matches.isEmpty)

                Button(action: { isPresented = false }) {
                    Image(systemName: "xmark")
                }
            }
            .padding(8)
            .background(.bar)

            Divider()

            // Replace bar
            HStack(spacing: 8) {
                Image(systemName: "arrow.triangle.2.circlepath")
                    .foregroundStyle(.secondary)

                TextField("Replace", text: $replaceText)
                    .textFieldStyle(.plain)
                    .focused($focusedField, equals: .replace)
                    .onSubmit { replaceAndFindNext() }

                Button(action: replaceCurrent) {
                    Text("Replace")
                        .font(.caption)
                }
                .disabled(matches.isEmpty)

                Button(action: replaceAll) {
                    Text("All")
                        .font(.caption)
                }
                .disabled(matches.isEmpty)
            }
            .padding(8)
            .background(.bar)

            Divider()

            // Options
            HStack(spacing: 12) {
                Toggle(isOn: $matchCase) {
                    Text("Aa")
                        .font(.caption.bold())
                }
                .toggleStyle(OptionToggleStyle())
                .help("Match Case")

                Toggle(isOn: $wholeWord) {
                    Image(systemName: "textformat.size")
                }
                .toggleStyle(OptionToggleStyle())
                .help("Whole Word")

                Toggle(isOn: $useRegex) {
                    Text(".*")
                        .font(.caption.bold())
                }
                .toggleStyle(OptionToggleStyle())
                .help("Use Regular Expression")

                Spacer()
            }
            .padding(8)
            .background(.quaternary)
        }
        .clipShape(RoundedRectangle(cornerRadius: 8))
        .shadow(radius: 4)
        .onAppear {
            focusedField = .search
        }
        .onChange(of: matchCase) { _, _ in performSearch() }
        .onChange(of: wholeWord) { _, _ in performSearch() }
        .onChange(of: useRegex) { _, _ in performSearch() }
    }

    private func performSearch() {
        guard !searchText.isEmpty else {
            matches = []
            currentMatchIndex = 0
            return
        }

        matches = SearchEngine.findMatches(
            in: content,
            searchText: searchText,
            matchCase: matchCase,
            wholeWord: wholeWord,
            useRegex: useRegex
        )
        currentMatchIndex = 0
    }

    private func findNext() {
        guard !matches.isEmpty else { return }
        currentMatchIndex = (currentMatchIndex + 1) % matches.count
        scrollToCurrentMatch()
    }

    private func findPrevious() {
        guard !matches.isEmpty else { return }
        currentMatchIndex = (currentMatchIndex - 1 + matches.count) % matches.count
        scrollToCurrentMatch()
    }

    private func scrollToCurrentMatch() {
        // Notify editor to scroll to current match
        NotificationCenter.default.post(
            name: .scrollToMatch,
            object: matches[currentMatchIndex]
        )
    }

    private func replaceCurrent() {
        guard !matches.isEmpty else { return }

        let match = matches[currentMatchIndex]
        content = SearchEngine.replace(
            in: content,
            match: match,
            with: replaceText
        )

        performSearch()
        if currentMatchIndex >= matches.count {
            currentMatchIndex = max(0, matches.count - 1)
        }
    }

    private func replaceAndFindNext() {
        replaceCurrent()
        if !matches.isEmpty {
            scrollToCurrentMatch()
        }
    }

    private func replaceAll() {
        content = SearchEngine.replaceAll(
            in: content,
            searchText: searchText,
            replaceText: replaceText,
            matchCase: matchCase,
            wholeWord: wholeWord,
            useRegex: useRegex
        )
        performSearch()
    }
}

struct OptionToggleStyle: ToggleStyle {
    func makeBody(configuration: Configuration) -> some View {
        Button(action: { configuration.isOn.toggle() }) {
            configuration.label
                .padding(.horizontal, 8)
                .padding(.vertical, 4)
                .background(configuration.isOn ? Color.accentColor.opacity(0.2) : Color.clear)
                .foregroundStyle(configuration.isOn ? .primary : .secondary)
                .clipShape(RoundedRectangle(cornerRadius: 4))
                .overlay(
                    RoundedRectangle(cornerRadius: 4)
                        .stroke(configuration.isOn ? Color.accentColor : Color.clear, lineWidth: 1)
                )
        }
        .buttonStyle(.plain)
    }
}

// MARK: - Search Engine

struct SearchMatch: Equatable {
    let range: Range<String.Index>
    let line: Int
    let column: Int
    let text: String
}

final class SearchEngine {
    static func findMatches(
        in content: String,
        searchText: String,
        matchCase: Bool,
        wholeWord: Bool,
        useRegex: Bool
    ) -> [SearchMatch] {
        var matches: [SearchMatch] = []

        if useRegex {
            matches = findRegexMatches(in: content, pattern: searchText, matchCase: matchCase)
        } else {
            matches = findTextMatches(
                in: content,
                searchText: searchText,
                matchCase: matchCase,
                wholeWord: wholeWord
            )
        }

        return matches
    }

    private static func findTextMatches(
        in content: String,
        searchText: String,
        matchCase: Bool,
        wholeWord: Bool
    ) -> [SearchMatch] {
        var matches: [SearchMatch] = []
        let compareContent = matchCase ? content : content.lowercased()
        let compareSearch = matchCase ? searchText : searchText.lowercased()

        var searchRange = compareContent.startIndex..<compareContent.endIndex

        while let range = compareContent.range(of: compareSearch, range: searchRange) {
            // Check whole word if needed
            if wholeWord {
                let isWholeWord = isWordBoundary(content, at: range.lowerBound) &&
                                  isWordBoundary(content, at: range.upperBound)
                if !isWholeWord {
                    searchRange = range.upperBound..<compareContent.endIndex
                    continue
                }
            }

            // Calculate line and column
            let (line, column) = lineAndColumn(for: range.lowerBound, in: content)

            // Get the original text (preserve case)
            let originalRange = Range(uncheckedBounds: (
                lower: content.index(content.startIndex, offsetBy: content.distance(from: content.startIndex, to: range.lowerBound)),
                upper: content.index(content.startIndex, offsetBy: content.distance(from: content.startIndex, to: range.upperBound))
            ))

            matches.append(SearchMatch(
                range: originalRange,
                line: line,
                column: column,
                text: String(content[originalRange])
            ))

            searchRange = range.upperBound..<compareContent.endIndex
        }

        return matches
    }

    private static func findRegexMatches(
        in content: String,
        pattern: String,
        matchCase: Bool
    ) -> [SearchMatch] {
        var matches: [SearchMatch] = []

        var options: NSRegularExpression.Options = []
        if !matchCase {
            options.insert(.caseInsensitive)
        }

        guard let regex = try? NSRegularExpression(pattern: pattern, options: options) else {
            return []
        }

        let nsContent = content as NSString
        let results = regex.matches(in: content, range: NSRange(location: 0, length: nsContent.length))

        for result in results {
            guard let range = Range(result.range, in: content) else { continue }

            let (line, column) = lineAndColumn(for: range.lowerBound, in: content)

            matches.append(SearchMatch(
                range: range,
                line: line,
                column: column,
                text: String(content[range])
            ))
        }

        return matches
    }

    private static func isWordBoundary(_ content: String, at index: String.Index) -> Bool {
        if index == content.startIndex || index == content.endIndex {
            return true
        }

        let prevIndex = content.index(before: index)
        let prevChar = content[prevIndex]
        let currChar = index < content.endIndex ? content[index] : Character(" ")

        let prevIsWord = prevChar.isLetter || prevChar.isNumber || prevChar == "_"
        let currIsWord = currChar.isLetter || currChar.isNumber || currChar == "_"

        return prevIsWord != currIsWord
    }

    private static func lineAndColumn(for index: String.Index, in content: String) -> (line: Int, column: Int) {
        var line = 1
        var column = 1

        for char in content[..<index] {
            if char == "\n" {
                line += 1
                column = 1
            } else {
                column += 1
            }
        }

        return (line, column)
    }

    static func replace(in content: String, match: SearchMatch, with replacement: String) -> String {
        var result = content
        result.replaceSubrange(match.range, with: replacement)
        return result
    }

    static func replaceAll(
        in content: String,
        searchText: String,
        replaceText: String,
        matchCase: Bool,
        wholeWord: Bool,
        useRegex: Bool
    ) -> String {
        if useRegex {
            var options: NSRegularExpression.Options = []
            if !matchCase {
                options.insert(.caseInsensitive)
            }

            guard let regex = try? NSRegularExpression(pattern: searchText, options: options) else {
                return content
            }

            return regex.stringByReplacingMatches(
                in: content,
                range: NSRange(content.startIndex..., in: content),
                withTemplate: replaceText
            )
        } else {
            // Simple string replacement
            let matches = findTextMatches(
                in: content,
                searchText: searchText,
                matchCase: matchCase,
                wholeWord: wholeWord
            )

            // Replace from end to beginning to preserve indices
            var result = content
            for match in matches.reversed() {
                result.replaceSubrange(match.range, with: replaceText)
            }

            return result
        }
    }
}

// Notification names moved to Utilities/NotificationNames.swift

// MARK: - Search Bar Overlay for Editor

struct EditorSearchOverlay: ViewModifier {
    @Binding var content: String
    @Binding var showSearch: Bool

    func body(content: Content) -> some View {
        content
            .overlay(alignment: .top) {
                if showSearch {
                    SearchReplaceView(
                        content: $content,
                        isPresented: $showSearch
                    )
                    .padding()
                    .transition(.move(edge: .top).combined(with: .opacity))
                }
            }
            .animation(.easeInOut(duration: 0.2), value: showSearch)
    }
}

extension View {
    func searchOverlay(content: Binding<String>, isPresented: Binding<Bool>) -> some View {
        modifier(EditorSearchOverlay(content: content, showSearch: isPresented))
    }
}

#Preview {
    @Previewable @State var content = """
    ---- MODULE Test ----
    VARIABLES x, y

    Init == x = 0 /\\ y = 0

    Next == x' = x + 1 /\\ y' = y

    ====
    """
    @Previewable @State var showSearch = true

    VStack {
        SearchReplaceView(content: $content, isPresented: $showSearch)
            .padding()
        Spacer()
    }
}
