#if os(macOS)
import SwiftUI
import AppKit

// MARK: - Native Text Editor with Line Numbers

/// Native macOS text editor using NSTextView with line number gutter
struct NativeTextEditor: View {
    @Binding var text: String
    var font: NSFont = .monospacedSystemFont(ofSize: 13, weight: .regular)
    var onTextChange: ((String) -> Void)?

    @State private var scrollOffset: CGFloat = 0

    var body: some View {
        HStack(spacing: 0) {
            // Line number gutter
            LineNumberGutter(text: text, scrollOffset: scrollOffset, font: font)

            // Editor
            EditorTextView(
                text: $text,
                font: font,
                onTextChange: onTextChange,
                onScrollChange: { offset in
                    scrollOffset = offset
                }
            )
        }
    }
}

// MARK: - Line Number Gutter

/// SwiftUI view showing line numbers that syncs with editor scroll
struct LineNumberGutter: View {
    let text: String
    let scrollOffset: CGFloat
    let font: NSFont

    private var lineCount: Int {
        max(1, text.components(separatedBy: "\n").count)
    }

    private var lineHeight: CGFloat {
        // Approximate line height based on font
        font.pointSize * 1.3
    }

    var body: some View {
        GeometryReader { geometry in
            VStack(alignment: .trailing, spacing: 0) {
                ForEach(0..<lineCount, id: \.self) { index in
                    let lineNumber = index + 1
                    Text("\(lineNumber)")
                        .font(.system(size: font.pointSize - 2, design: .monospaced))
                        .foregroundColor(.secondary)
                        .frame(height: lineHeight)
                }
            }
            .padding(.top, 8)
            .padding(.trailing, 6)
            .offset(y: -scrollOffset)
        }
        .frame(width: 44)
        .background(Color(nsColor: .controlBackgroundColor))
        .clipped()
    }
}

// MARK: - Editor Text View (NSViewRepresentable)

/// The actual NSTextView wrapper
struct EditorTextView: NSViewRepresentable {
    @Binding var text: String
    var font: NSFont
    var onTextChange: ((String) -> Void)?
    var onScrollChange: ((CGFloat) -> Void)?

    func makeNSView(context: Context) -> NSScrollView {
        // Create custom text system
        let textStorage = NSTextStorage()
        let layoutManager = NSLayoutManager()
        textStorage.addLayoutManager(layoutManager)

        // Create scroll view
        let scrollView = NSScrollView()
        scrollView.hasVerticalScroller = true
        scrollView.hasHorizontalScroller = false
        scrollView.autohidesScrollers = true
        scrollView.borderType = .noBorder
        scrollView.backgroundColor = NSColor.textBackgroundColor

        // Create text container
        let textContainer = NSTextContainer()
        textContainer.widthTracksTextView = true
        textContainer.heightTracksTextView = false
        textContainer.containerSize = NSSize(width: 0, height: CGFloat.greatestFiniteMagnitude)
        layoutManager.addTextContainer(textContainer)

        // Create text view
        let textView = NSTextView(frame: .zero, textContainer: textContainer)
        textView.delegate = context.coordinator
        textView.isEditable = true
        textView.isSelectable = true
        textView.allowsUndo = true
        textView.backgroundColor = NSColor.textBackgroundColor
        textView.font = font
        textView.textColor = NSColor.textColor
        textView.insertionPointColor = .labelColor

        // Disable smart text features
        textView.isAutomaticQuoteSubstitutionEnabled = false
        textView.isAutomaticDashSubstitutionEnabled = false
        textView.isAutomaticTextReplacementEnabled = false
        textView.isAutomaticSpellingCorrectionEnabled = false
        textView.isContinuousSpellCheckingEnabled = false
        textView.isGrammarCheckingEnabled = false

        // Configure sizing
        textView.isHorizontallyResizable = false
        textView.isVerticallyResizable = true
        textView.autoresizingMask = [.width]
        textView.textContainerInset = NSSize(width: 8, height: 8)
        textView.minSize = NSSize(width: 0, height: 0)
        textView.maxSize = NSSize(width: CGFloat.greatestFiniteMagnitude, height: CGFloat.greatestFiniteMagnitude)

        // Set document view
        scrollView.documentView = textView

        // Set initial text and apply highlighting
        textView.string = text
        context.coordinator.applyHighlighting(to: textView)

        // Store references
        context.coordinator.textView = textView
        context.coordinator.onScrollChange = onScrollChange

        // Add click gesture recognizer for Cmd+Click
        let clickRecognizer = NSClickGestureRecognizer(target: context.coordinator, action: #selector(Coordinator.handleTextClick(_:)))
        clickRecognizer.numberOfClicksRequired = 1
        textView.addGestureRecognizer(clickRecognizer)

        // Observe scroll changes
        scrollView.contentView.postsBoundsChangedNotifications = true
        context.coordinator.scrollObserver = NotificationCenter.default.addObserver(
            forName: NSView.boundsDidChangeNotification,
            object: scrollView.contentView,
            queue: .main
        ) { [weak coordinator = context.coordinator] _ in
            coordinator?.handleScrollChange()
        }

        return scrollView
    }

    func updateNSView(_ scrollView: NSScrollView, context: Context) {
        guard let textView = scrollView.documentView as? NSTextView else { return }

        // Skip if we're in the middle of an internal update
        guard !context.coordinator.isUpdating else { return }

        // Only update if text changed externally (e.g., from binding)
        if textView.string != text {
            context.coordinator.applyHighlighting(to: textView, newText: text)
        }

        // Update font if changed
        if textView.font != font {
            textView.font = font
            context.coordinator.applyHighlighting(to: textView)
        }
    }

    func makeCoordinator() -> Coordinator {
        Coordinator(self)
    }

    class Coordinator: NSObject, NSTextViewDelegate {
        var parent: EditorTextView
        var isUpdating = false
        weak var textView: NSTextView?
        var onScrollChange: ((CGFloat) -> Void)?
        var scrollObserver: NSObjectProtocol?
        var currentBracketHighlightRange: NSRange?
        var matchingBracketHighlightRange: NSRange?

        // Bracket pairs to match
        static let bracketPairs: [(open: String, close: String)] = [
            ("(", ")"),
            ("[", "]"),
            ("{", "}"),
            ("<<", ">>")
        ]

        init(_ parent: EditorTextView) {
            self.parent = parent
            super.init()
        }

        deinit {
            if let observer = scrollObserver {
                NotificationCenter.default.removeObserver(observer)
            }
        }

        func handleScrollChange() {
            guard let textView = textView,
                  let scrollView = textView.enclosingScrollView else { return }
            let offset = scrollView.contentView.bounds.origin.y
            onScrollChange?(offset)
        }

        func textDidChange(_ notification: Notification) {
            guard !isUpdating,
                  let textView = notification.object as? NSTextView else { return }

            let newText = textView.string

            // Update binding without triggering view update loop
            isUpdating = true
            parent.text = newText
            parent.onTextChange?(newText)
            isUpdating = false

            // Apply highlighting with a slight delay to avoid conflicts
            applyHighlightingDebounced(to: textView)
        }

        private var highlightWorkItem: DispatchWorkItem?

        private func applyHighlightingDebounced(to textView: NSTextView) {
            highlightWorkItem?.cancel()

            let workItem = DispatchWorkItem { [weak self] in
                guard let self = self else { return }
                self.applyHighlightingAttributesOnly(to: textView)
            }
            highlightWorkItem = workItem

            // Small delay to batch rapid typing
            DispatchQueue.main.asyncAfter(deadline: .now() + 0.05, execute: workItem)
        }

        private func applyHighlightingAttributesOnly(to textView: NSTextView) {
            guard !isUpdating else { return }
            isUpdating = true
            defer { isUpdating = false }

            guard let textStorage = textView.textStorage, textStorage.length > 0 else { return }

            let selectedRanges = textView.selectedRanges
            let fullRange = NSRange(location: 0, length: textStorage.length)

            textStorage.beginEditing()

            // Reset to default attributes
            textStorage.setAttributes([
                .font: parent.font,
                .foregroundColor: NSColor.textColor
            ], range: fullRange)

            // Apply syntax highlighting
            TLASyntaxHighlighter.shared.applyHighlightingAttributes(to: textStorage, font: parent.font)

            textStorage.endEditing()

            // Restore selection
            if let firstRange = selectedRanges.first as? NSRange,
               firstRange.location + firstRange.length <= textStorage.length {
                textView.setSelectedRange(firstRange)
            }

            updateBracketMatching(in: textView)
        }

        // Handle special keys like Enter for auto-indent
        func textView(_ textView: NSTextView, doCommandBy commandSelector: Selector) -> Bool {
            if commandSelector == #selector(NSStandardKeyBindingResponding.insertNewline(_:)) {
                handleNewlineWithAutoIndent(textView: textView)
                return true
            }
            return false
        }

        // Handle Cmd+Click for go-to-definition
        func textView(_ textView: NSTextView, clickedOnLink link: Any, at charIndex: Int) -> Bool {
            return false // We handle clicks differently
        }

        func textView(_ textView: NSTextView, willChangeSelectionFromCharacterRange oldSelectedCharRange: NSRange, toCharacterRange newSelectedCharRange: NSRange) -> NSRange {
            return newSelectedCharRange
        }

        // Called when user clicks - check for Cmd+Click
        @objc func handleTextClick(_ recognizer: NSClickGestureRecognizer) {
            guard let textView = recognizer.view as? NSTextView,
                  NSEvent.modifierFlags.contains(.command) else { return }

            // Get click location in text
            let location = recognizer.location(in: textView)
            guard let textContainer = textView.textContainer,
                  let layoutManager = textView.layoutManager else { return }

            var fraction: CGFloat = 0
            let characterIndex = layoutManager.characterIndex(
                for: location,
                in: textContainer,
                fractionOfDistanceBetweenInsertionPoints: &fraction
            )

            // Find the word at this position
            let text = textView.string
            guard characterIndex < text.count else { return }

            // Get the word under cursor
            if let word = getWordAt(index: characterIndex, in: text) {
                goToDefinition(of: word, in: text)
            }
        }

        private func getWordAt(index: Int, in text: String) -> String? {
            let chars = Array(text)
            guard index < chars.count else { return nil }

            // Find start of word
            var start = index
            while start > 0 && (chars[start - 1].isLetter || chars[start - 1].isNumber || chars[start - 1] == "_") {
                start -= 1
            }

            // Find end of word
            var end = index
            while end < chars.count && (chars[end].isLetter || chars[end].isNumber || chars[end] == "_") {
                end += 1
            }

            guard start < end else { return nil }
            return String(chars[start..<end])
        }

        private func goToDefinition(of symbol: String, in source: String) {
            if let location = SymbolNavigator.shared.findDefinition(of: symbol, in: source) {
                // Post notification to navigate to line
                NotificationCenter.default.post(
                    name: .navigateToLine,
                    object: location
                )
            }
        }

        private func handleNewlineWithAutoIndent(textView: NSTextView) {
            let text = textView.string
            let cursorPosition = textView.selectedRange().location

            // Find the current line
            let lineRange = (text as NSString).lineRange(for: NSRange(location: cursorPosition, length: 0))
            let currentLine = (text as NSString).substring(with: lineRange)

            // Get leading whitespace from current line
            var leadingWhitespace = ""
            for char in currentLine {
                if char == " " || char == "\t" {
                    leadingWhitespace.append(char)
                } else {
                    break
                }
            }

            // Check if we should increase indent (after certain keywords)
            let trimmedLine = currentLine.trimmingCharacters(in: .whitespaces)
            let shouldIncreaseIndent = trimmedLine.hasSuffix("begin") ||
                                       trimmedLine.hasSuffix("then") ||
                                       trimmedLine.hasSuffix("else") ||
                                       trimmedLine.hasSuffix("do") ||
                                       trimmedLine.hasSuffix("==") ||
                                       trimmedLine.hasSuffix("/\\") ||
                                       trimmedLine.hasSuffix("\\/") ||
                                       trimmedLine.hasSuffix("LET") ||
                                       trimmedLine.hasSuffix("IN")

            if shouldIncreaseIndent {
                leadingWhitespace += "    "  // Add 4 spaces
            }

            // Insert newline + indentation
            let insertText = "\n" + leadingWhitespace

            // Perform the insertion
            isUpdating = true
            if textView.shouldChangeText(in: textView.selectedRange(), replacementString: insertText) {
                textView.replaceCharacters(in: textView.selectedRange(), with: insertText)
                textView.didChangeText()
            }
            isUpdating = false

            // Update binding
            parent.text = textView.string
            parent.onTextChange?(textView.string)
            applyHighlighting(to: textView)
        }

        func textViewDidChangeSelection(_ notification: Notification) {
            guard let textView = notification.object as? NSTextView else { return }
            updateBracketMatching(in: textView)
        }

        func applyHighlighting(to textView: NSTextView, newText: String? = nil) {
            isUpdating = true
            defer { isUpdating = false }

            let selectedRanges = textView.selectedRanges

            // If newText is provided and differs from current text, update text first
            if let newText = newText, textView.string != newText {
                // Use textStorage to avoid triggering textDidChange
                if let textStorage = textView.textStorage {
                    textStorage.beginEditing()
                    textStorage.replaceCharacters(in: NSRange(location: 0, length: textStorage.length), with: newText)
                    textStorage.endEditing()
                }
            }

            // Apply highlighting attributes WITHOUT replacing text content
            // This prevents the race condition that causes text to vanish
            if let textStorage = textView.textStorage, textStorage.length > 0 {
                let fullRange = NSRange(location: 0, length: textStorage.length)
                textStorage.beginEditing()

                // Reset to default attributes first
                textStorage.setAttributes([
                    .font: parent.font,
                    .foregroundColor: NSColor.textColor
                ], range: fullRange)

                // Apply syntax highlighting colors
                TLASyntaxHighlighter.shared.applyHighlightingAttributes(to: textStorage, font: parent.font)

                textStorage.endEditing()
            }

            // Restore selection
            let text = textView.string
            if let firstRange = selectedRanges.first as? NSRange,
               firstRange.location + firstRange.length <= text.count {
                textView.setSelectedRange(firstRange)
            }

            // Update bracket matching
            updateBracketMatching(in: textView)
        }

        func updateBracketMatching(in textView: NSTextView) {
            guard let layoutManager = textView.layoutManager else { return }

            // Clear previous highlights
            if let oldRange = currentBracketHighlightRange {
                layoutManager.removeTemporaryAttribute(.backgroundColor, forCharacterRange: oldRange)
            }
            if let oldRange = matchingBracketHighlightRange {
                layoutManager.removeTemporaryAttribute(.backgroundColor, forCharacterRange: oldRange)
            }
            currentBracketHighlightRange = nil
            matchingBracketHighlightRange = nil

            let text = textView.string
            let cursorPosition = textView.selectedRange().location

            guard cursorPosition <= text.count else { return }

            // Check for bracket at or before cursor
            if let (bracketRange, matchRange) = findMatchingBracket(in: text, at: cursorPosition) {
                let highlightColor = NSColor.systemYellow.withAlphaComponent(0.3)

                layoutManager.addTemporaryAttribute(.backgroundColor, value: highlightColor, forCharacterRange: bracketRange)
                layoutManager.addTemporaryAttribute(.backgroundColor, value: highlightColor, forCharacterRange: matchRange)

                currentBracketHighlightRange = bracketRange
                matchingBracketHighlightRange = matchRange
            }
        }

        func findMatchingBracket(in text: String, at position: Int) -> (NSRange, NSRange)? {
            let chars = Array(text)
            guard position >= 0 && position <= chars.count else { return nil }

            // Check position before cursor and at cursor
            let positionsToCheck = position > 0 ? [position - 1, position] : [position]

            for checkPos in positionsToCheck {
                guard checkPos < chars.count else { continue }

                // Check for multi-char brackets first (<<, >>)
                if checkPos + 1 < chars.count {
                    let twoChar = String(chars[checkPos...checkPos + 1])
                    if twoChar == "<<" {
                        if let matchPos = findClosingBracket(chars: chars, from: checkPos, open: "<<", close: ">>") {
                            return (NSRange(location: checkPos, length: 2), NSRange(location: matchPos, length: 2))
                        }
                    } else if twoChar == ">>" {
                        if let matchPos = findOpeningBracket(chars: chars, from: checkPos + 1, open: "<<", close: ">>") {
                            return (NSRange(location: checkPos, length: 2), NSRange(location: matchPos, length: 2))
                        }
                    }
                }

                // Check single char brackets
                let char = String(chars[checkPos])
                for pair in Self.bracketPairs where pair.open.count == 1 {
                    if char == pair.open {
                        if let matchPos = findClosingBracket(chars: chars, from: checkPos, open: pair.open, close: pair.close) {
                            return (NSRange(location: checkPos, length: 1), NSRange(location: matchPos, length: 1))
                        }
                    } else if char == pair.close {
                        if let matchPos = findOpeningBracket(chars: chars, from: checkPos, open: pair.open, close: pair.close) {
                            return (NSRange(location: checkPos, length: 1), NSRange(location: matchPos, length: 1))
                        }
                    }
                }
            }

            return nil
        }

        func findClosingBracket(chars: [Character], from start: Int, open: String, close: String) -> Int? {
            let openChars = Array(open)
            let closeChars = Array(close)
            var depth = 1
            var i = start + openChars.count

            while i < chars.count {
                // Check for close bracket
                if i + closeChars.count <= chars.count {
                    var matches = true
                    for j in 0..<closeChars.count {
                        if chars[i + j] != closeChars[j] {
                            matches = false
                            break
                        }
                    }
                    if matches {
                        depth -= 1
                        if depth == 0 {
                            return i
                        }
                        i += closeChars.count
                        continue
                    }
                }

                // Check for open bracket (nested)
                if i + openChars.count <= chars.count {
                    var matches = true
                    for j in 0..<openChars.count {
                        if chars[i + j] != openChars[j] {
                            matches = false
                            break
                        }
                    }
                    if matches {
                        depth += 1
                        i += openChars.count
                        continue
                    }
                }

                i += 1
            }

            return nil
        }

        func findOpeningBracket(chars: [Character], from start: Int, open: String, close: String) -> Int? {
            let openChars = Array(open)
            let closeChars = Array(close)
            var depth = 1
            var i = start - 1

            while i >= 0 {
                // Check for open bracket
                if i - openChars.count + 1 >= 0 {
                    var matches = true
                    for j in 0..<openChars.count {
                        if chars[i - openChars.count + 1 + j] != openChars[j] {
                            matches = false
                            break
                        }
                    }
                    if matches {
                        depth -= 1
                        if depth == 0 {
                            return i - openChars.count + 1
                        }
                        i -= openChars.count
                        continue
                    }
                }

                // Check for close bracket (nested)
                if i - closeChars.count + 1 >= 0 {
                    var matches = true
                    for j in 0..<closeChars.count {
                        if chars[i - closeChars.count + 1 + j] != closeChars[j] {
                            matches = false
                            break
                        }
                    }
                    if matches {
                        depth += 1
                        i -= closeChars.count
                        continue
                    }
                }

                i -= 1
            }

            return nil
        }
    }
}
#endif
