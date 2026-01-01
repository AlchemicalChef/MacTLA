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
    @State private var cachedLineCount: Int = 1
    @State private var visibleHeight: CGFloat = 500

    var body: some View {
        GeometryReader { geometry in
            HStack(spacing: 0) {
                // Line number gutter (NSView-based for reliability)
                LineNumberGutter(
                    scrollOffset: scrollOffset,
                    font: font,
                    cachedLineCount: cachedLineCount,
                    visibleHeight: geometry.size.height
                )
                .frame(width: 44)

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
            .onAppear {
                visibleHeight = geometry.size.height
                cachedLineCount = max(1, text.filter { $0 == "\n" }.count + 1)
            }
            .onChange(of: text) { _, newText in
                // Only recount when text changes
                cachedLineCount = max(1, newText.filter { $0 == "\n" }.count + 1)
            }
            .onChange(of: geometry.size.height) { _, newHeight in
                visibleHeight = newHeight
            }
        }
    }
}

// MARK: - Line Number Gutter (NSView-based for reliability)

/// NSView-based line number gutter that syncs with editor scroll
struct LineNumberGutter: NSViewRepresentable {
    let scrollOffset: CGFloat
    let font: NSFont
    let cachedLineCount: Int
    let visibleHeight: CGFloat

    func makeNSView(context: Context) -> LineNumberGutterView {
        let view = LineNumberGutterView()
        view.font = font
        view.lineCount = cachedLineCount
        return view
    }

    func updateNSView(_ nsView: LineNumberGutterView, context: Context) {
        nsView.font = font
        nsView.lineCount = cachedLineCount
        nsView.scrollOffset = scrollOffset
        nsView.needsDisplay = true
    }
}

/// Custom NSView that draws line numbers efficiently
class LineNumberGutterView: NSView {
    var font: NSFont = .monospacedSystemFont(ofSize: 13, weight: .regular)
    var lineCount: Int = 1
    var scrollOffset: CGFloat = 0

    private var lineHeight: CGFloat {
        // Match NSTextView's default line height calculation
        let layoutManager = NSLayoutManager()
        return layoutManager.defaultLineHeight(for: font)
    }

    override var isFlipped: Bool { true }  // Top-to-bottom coordinate system

    override func draw(_ dirtyRect: NSRect) {
        // Draw background
        NSColor.controlBackgroundColor.setFill()
        dirtyRect.fill()

        // Calculate visible line range
        let topPadding: CGFloat = 8  // Match textContainerInset
        let lh = lineHeight
        let firstVisibleLine = max(0, Int((scrollOffset - topPadding) / lh))
        let visibleLines = Int(bounds.height / lh) + 2
        let lastVisibleLine = min(lineCount, firstVisibleLine + visibleLines)

        // Text attributes
        let paragraphStyle = NSMutableParagraphStyle()
        paragraphStyle.alignment = .right
        let attributes: [NSAttributedString.Key: Any] = [
            .font: NSFont.monospacedSystemFont(ofSize: font.pointSize - 2, weight: .regular),
            .foregroundColor: NSColor.secondaryLabelColor,
            .paragraphStyle: paragraphStyle
        ]

        // Draw only visible line numbers
        for lineNum in firstVisibleLine..<lastVisibleLine {
            let y = topPadding + CGFloat(lineNum) * lh - scrollOffset
            let text = "\(lineNum + 1)"
            let rect = NSRect(x: 0, y: y, width: bounds.width - 6, height: lh)
            text.draw(in: rect, withAttributes: attributes)
        }
    }

    override var intrinsicContentSize: NSSize {
        return NSSize(width: 44, height: NSView.noIntrinsicMetric)
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

        // Scroll throttling - only update when scroll changes by more than lineHeight
        private var lastReportedScrollOffset: CGFloat = 0
        private var scrollThreshold: CGFloat = 10 // pixels before updating

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

            // Throttle updates: only notify when scroll changes significantly
            let delta = abs(offset - lastReportedScrollOffset)
            if delta >= scrollThreshold {
                lastReportedScrollOffset = offset
                onScrollChange?(offset)
            }
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
        private var highlightTask: Task<Void, Never>?

        /// Main highlighting entry point - uses temporary attributes for performance
        /// All heavy computation (tokenization, range calculation) happens on background thread
        private func applyHighlightingDebounced(to textView: NSTextView) {
            highlightWorkItem?.cancel()
            highlightTask?.cancel()

            let workItem = DispatchWorkItem { [weak self, weak textView] in
                guard let self = self, let textView = textView else { return }

                let text = textView.string
                let textLength = (text as NSString).length

                self.highlightTask?.cancel()

                // All heavy work on background thread: tokenize + prepare operations
                self.highlightTask = Task.detached(priority: .userInitiated) { [weak self, weak textView] in
                    guard !Task.isCancelled else { return }

                    // Heavy work 1: Tokenization (PROFILED)
                    let tokenizeStart = CFAbsoluteTimeGetCurrent()
                    let lexer = TLALexer(source: text)
                    let tokens = lexer.scanTokens()
                    let tokenizeTime = CFAbsoluteTimeGetCurrent() - tokenizeStart

                    guard !Task.isCancelled else { return }

                    // Heavy work 2: Prepare highlight operations (PROFILED)
                    let prepareStart = CFAbsoluteTimeGetCurrent()
                    let operations = TLASyntaxHighlighter.shared.prepareHighlightOperations(
                        tokens: tokens,
                        source: text
                    )
                    let prepareTime = CFAbsoluteTimeGetCurrent() - prepareStart

                    guard !Task.isCancelled, let textView = textView else { return }

                    // Minimal main thread work: just apply pre-computed operations
                    await MainActor.run { [weak self, weak textView] in
                        guard let self = self, let textView = textView else { return }
                        self.applyPreparedHighlighting(
                            operations: operations,
                            textLength: textLength,
                            tokenizeTime: tokenizeTime,
                            prepareTime: prepareTime,
                            to: textView
                        )
                    }
                }
            }
            highlightWorkItem = workItem

            // 100ms delay to batch rapid typing
            DispatchQueue.main.asyncAfter(deadline: .now() + 0.1, execute: workItem)
        }

        /// Apply pre-computed highlighting operations (minimal main thread work)
        private func applyPreparedHighlighting(
            operations: [TLASyntaxHighlighter.HighlightOperation],
            textLength: Int,
            tokenizeTime: Double = 0,
            prepareTime: Double = 0,
            to textView: NSTextView
        ) {
            guard !isUpdating,
                  let layoutManager = textView.layoutManager,
                  textLength > 0 else { return }

            isUpdating = true
            defer { isUpdating = false }

            let applyStart = CFAbsoluteTimeGetCurrent()

            let fullRange = NSRange(location: 0, length: textLength)

            // Clear previous highlighting
            layoutManager.removeTemporaryAttribute(.foregroundColor, forCharacterRange: fullRange)

            // Apply pre-computed operations (very fast - just dictionary lookups and attribute calls)
            TLASyntaxHighlighter.shared.applyHighlightOperations(operations, to: layoutManager)

            let applyTime = CFAbsoluteTimeGetCurrent() - applyStart

            // Write profiling results to file
            let profileLine = String(format: "[%@] tokenize=%.2fms, prepare=%.2fms, apply=%.2fms, ops=%d, chars=%d\n",
                                     ISO8601DateFormatter().string(from: Date()),
                                     tokenizeTime * 1000, prepareTime * 1000, applyTime * 1000, operations.count, textLength)
            let profilePath = "/Users/night/Documents/GitHub/MacTLA/Profiler.txt"
            if let data = profileLine.data(using: .utf8) {
                if FileManager.default.fileExists(atPath: profilePath) {
                    if let handle = FileHandle(forWritingAtPath: profilePath) {
                        handle.seekToEndOfFile()
                        handle.write(data)
                        handle.closeFile()
                    }
                } else {
                    FileManager.default.createFile(atPath: profilePath, contents: data)
                }
            }

            updateBracketMatching(in: textView)
        }

        // Legacy method - now uses temporary attributes
        private func applyHighlightingAttributesOnly(to textView: NSTextView) {
            applyHighlightingDebounced(to: textView)
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
                if let textStorage = textView.textStorage {
                    textStorage.beginEditing()
                    textStorage.replaceCharacters(in: NSRange(location: 0, length: textStorage.length), with: newText)
                    textStorage.endEditing()
                }
            }

            // Trigger debounced highlighting with temporary attributes
            isUpdating = false
            applyHighlightingDebounced(to: textView)
            isUpdating = true

            // Restore selection
            let text = textView.string
            if let firstRange = selectedRanges.first as? NSRange,
               firstRange.location + firstRange.length <= text.count {
                textView.setSelectedRange(firstRange)
            }
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

        /// Maximum search radius for bracket matching (characters in each direction)
        private static let bracketSearchRadius = 5000

        func findMatchingBracket(in text: String, at position: Int) -> (NSRange, NSRange)? {
            // Use NSString for O(1) character access
            let nsText = text as NSString
            let length = nsText.length
            guard position >= 0 && position <= length else { return nil }

            // Check position before cursor and at cursor
            let positionsToCheck = position > 0 ? [position - 1, position] : [position]

            for checkPos in positionsToCheck {
                guard checkPos < length else { continue }

                let char = nsText.character(at: checkPos)

                // Check for multi-char brackets first (<<, >>)
                if checkPos + 1 < length {
                    let nextChar = nsText.character(at: checkPos + 1)
                    // Check for << (60, 60 in ASCII)
                    if char == 60 && nextChar == 60 {
                        if let matchPos = findClosingBracketEfficient(in: nsText, from: checkPos, openLen: 2, closeLen: 2, openFirst: 60, closeFirst: 62) {
                            return (NSRange(location: checkPos, length: 2), NSRange(location: matchPos, length: 2))
                        }
                    }
                    // Check for >> (62, 62 in ASCII)
                    else if char == 62 && nextChar == 62 {
                        if let matchPos = findOpeningBracketEfficient(in: nsText, from: checkPos + 1, openLen: 2, closeLen: 2, openFirst: 60, closeFirst: 62) {
                            return (NSRange(location: checkPos, length: 2), NSRange(location: matchPos, length: 2))
                        }
                    }
                }

                // Check single char brackets using Unicode scalars
                // ( = 40, ) = 41, [ = 91, ] = 93, { = 123, } = 125
                switch char {
                case 40: // (
                    if let matchPos = findClosingBracketEfficient(in: nsText, from: checkPos, openLen: 1, closeLen: 1, openFirst: 40, closeFirst: 41) {
                        return (NSRange(location: checkPos, length: 1), NSRange(location: matchPos, length: 1))
                    }
                case 41: // )
                    if let matchPos = findOpeningBracketEfficient(in: nsText, from: checkPos, openLen: 1, closeLen: 1, openFirst: 40, closeFirst: 41) {
                        return (NSRange(location: checkPos, length: 1), NSRange(location: matchPos, length: 1))
                    }
                case 91: // [
                    if let matchPos = findClosingBracketEfficient(in: nsText, from: checkPos, openLen: 1, closeLen: 1, openFirst: 91, closeFirst: 93) {
                        return (NSRange(location: checkPos, length: 1), NSRange(location: matchPos, length: 1))
                    }
                case 93: // ]
                    if let matchPos = findOpeningBracketEfficient(in: nsText, from: checkPos, openLen: 1, closeLen: 1, openFirst: 91, closeFirst: 93) {
                        return (NSRange(location: checkPos, length: 1), NSRange(location: matchPos, length: 1))
                    }
                case 123: // {
                    if let matchPos = findClosingBracketEfficient(in: nsText, from: checkPos, openLen: 1, closeLen: 1, openFirst: 123, closeFirst: 125) {
                        return (NSRange(location: checkPos, length: 1), NSRange(location: matchPos, length: 1))
                    }
                case 125: // }
                    if let matchPos = findOpeningBracketEfficient(in: nsText, from: checkPos, openLen: 1, closeLen: 1, openFirst: 123, closeFirst: 125) {
                        return (NSRange(location: checkPos, length: 1), NSRange(location: matchPos, length: 1))
                    }
                default:
                    break
                }
            }

            return nil
        }

        /// Efficient forward search for closing bracket with search radius limit
        private func findClosingBracketEfficient(in text: NSString, from start: Int, openLen: Int, closeLen: Int, openFirst: unichar, closeFirst: unichar) -> Int? {
            var depth = 1
            var i = start + openLen
            let maxPos = min(text.length, start + Self.bracketSearchRadius)

            while i < maxPos {
                let char = text.character(at: i)

                // Check for close bracket
                if char == closeFirst {
                    if closeLen == 1 || (i + 1 < text.length && text.character(at: i + 1) == closeFirst) {
                        depth -= 1
                        if depth == 0 { return i }
                        i += closeLen
                        continue
                    }
                }

                // Check for open bracket (nested)
                if char == openFirst {
                    if openLen == 1 || (i + 1 < text.length && text.character(at: i + 1) == openFirst) {
                        depth += 1
                        i += openLen
                        continue
                    }
                }

                i += 1
            }

            return nil
        }

        /// Efficient backward search for opening bracket with search radius limit
        private func findOpeningBracketEfficient(in text: NSString, from start: Int, openLen: Int, closeLen: Int, openFirst: unichar, closeFirst: unichar) -> Int? {
            var depth = 1
            var i = start - 1
            let minPos = max(0, start - Self.bracketSearchRadius)

            while i >= minPos {
                let char = text.character(at: i)

                // Check for open bracket
                if char == openFirst {
                    if openLen == 1 {
                        depth -= 1
                        if depth == 0 { return i }
                    } else if i > 0 && text.character(at: i - 1) == openFirst {
                        depth -= 1
                        if depth == 0 { return i - 1 }
                        i -= 1
                    }
                    i -= 1
                    continue
                }

                // Check for close bracket (nested)
                if char == closeFirst {
                    if closeLen == 1 {
                        depth += 1
                    } else if i > 0 && text.character(at: i - 1) == closeFirst {
                        depth += 1
                        i -= 1
                    }
                    i -= 1
                    continue
                }

                i -= 1
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
