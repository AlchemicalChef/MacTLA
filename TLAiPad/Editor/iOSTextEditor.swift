#if os(iOS)
import SwiftUI
import UIKit

/// A UITextView-based text editor for iOS with syntax highlighting support
struct iOSTextEditor: UIViewRepresentable {
    @Binding var text: String
    var fontSize: CGFloat
    var fontFamily: String
    var showLineNumbers: Bool
    var onChange: ((String) -> Void)?

    private let highlighter = TLASyntaxHighlighter.shared

    init(
        text: Binding<String>,
        fontSize: CGFloat = 14,
        fontFamily: String = "Menlo",
        showLineNumbers: Bool = true,
        onChange: ((String) -> Void)? = nil
    ) {
        self._text = text
        self.fontSize = fontSize
        self.fontFamily = fontFamily
        self.showLineNumbers = showLineNumbers
        self.onChange = onChange
    }

    func makeUIView(context: Context) -> iOSTextEditorView {
        let view = iOSTextEditorView(frame: .zero)
        view.configure(
            fontSize: fontSize,
            fontFamily: fontFamily,
            showLineNumbers: showLineNumbers
        )
        view.delegate = context.coordinator
        view.text = text
        view.applySyntaxHighlighting(using: highlighter)
        return view
    }

    func updateUIView(_ view: iOSTextEditorView, context: Context) {
        if view.text != text {
            // Preserve selection
            let selectedRange = view.textView.selectedRange
            view.text = text
            view.applySyntaxHighlighting(using: highlighter)

            // Restore selection if valid
            if selectedRange.location + selectedRange.length <= text.count {
                view.textView.selectedRange = selectedRange
            }
        }

        // Update font if changed
        view.updateFont(fontSize: fontSize, fontFamily: fontFamily)
    }

    func makeCoordinator() -> Coordinator {
        Coordinator(self)
    }

    class Coordinator: NSObject, UITextViewDelegate {
        var parent: iOSTextEditor
        private var isUpdating = false
        private var highlightWorkItem: DispatchWorkItem?
        private var lineNumberWorkItem: DispatchWorkItem?

        init(_ parent: iOSTextEditor) {
            self.parent = parent
        }

        func textViewDidChange(_ textView: UITextView) {
            guard !isUpdating else { return }
            isUpdating = true
            defer { isUpdating = false }

            parent.text = textView.text
            parent.onChange?(textView.text)

            // Debounce syntax highlighting (100ms)
            highlightWorkItem?.cancel()
            let workItem = DispatchWorkItem { [weak self, weak textView] in
                guard let textView = textView,
                      let editorView = textView.superview as? iOSTextEditorView else { return }
                editorView.applySyntaxHighlighting(using: self?.parent.highlighter ?? TLASyntaxHighlighter.shared)
                editorView.updateLineNumbers()
            }
            highlightWorkItem = workItem
            DispatchQueue.main.asyncAfter(deadline: .now() + 0.1, execute: workItem)
        }

        func textViewDidChangeSelection(_ textView: UITextView) {
            // Debounce line number updates on selection change (50ms)
            lineNumberWorkItem?.cancel()
            let workItem = DispatchWorkItem { [weak textView] in
                if let editorView = textView?.superview as? iOSTextEditorView {
                    editorView.updateLineNumbers()
                }
            }
            lineNumberWorkItem = workItem
            DispatchQueue.main.asyncAfter(deadline: .now() + 0.05, execute: workItem)
        }
    }
}

/// Custom UIView that combines a UITextView with a line number gutter
class iOSTextEditorView: UIView {
    let textView: UITextView
    private let lineNumberView: UITextView
    private let scrollView: UIScrollView
    private var showLineNumbers: Bool = true

    // Cached values for line number optimization
    private var cachedLineCount: Int = 0
    private var cachedCurrentLine: Int = 0

    var text: String {
        get { textView.text }
        set { textView.text = newValue }
    }

    var delegate: UITextViewDelegate? {
        get { textView.delegate }
        set { textView.delegate = newValue }
    }

    override init(frame: CGRect) {
        scrollView = UIScrollView(frame: frame)
        textView = UITextView(frame: .zero)
        lineNumberView = UITextView(frame: .zero)

        super.init(frame: frame)
        setupViews()
    }

    required init?(coder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }

    private func setupViews() {
        // Configure scroll view
        scrollView.translatesAutoresizingMaskIntoConstraints = false
        scrollView.showsHorizontalScrollIndicator = true
        scrollView.showsVerticalScrollIndicator = true
        addSubview(scrollView)

        // Configure text view
        textView.translatesAutoresizingMaskIntoConstraints = false
        textView.isScrollEnabled = false
        textView.autocorrectionType = .no
        textView.autocapitalizationType = .none
        textView.smartQuotesType = .no
        textView.smartDashesType = .no
        textView.smartInsertDeleteType = .no
        textView.spellCheckingType = .no
        textView.backgroundColor = .clear
        textView.textContainerInset = UIEdgeInsets(top: 8, left: 8, bottom: 8, right: 8)
        scrollView.addSubview(textView)

        // Configure line number view
        lineNumberView.translatesAutoresizingMaskIntoConstraints = false
        lineNumberView.isEditable = false
        lineNumberView.isSelectable = false
        lineNumberView.isScrollEnabled = false
        lineNumberView.backgroundColor = UIColor.secondarySystemBackground
        lineNumberView.textContainerInset = UIEdgeInsets(top: 8, left: 4, bottom: 8, right: 4)
        lineNumberView.textContainer.lineBreakMode = .byClipping
        addSubview(lineNumberView)

        // Setup constraints
        NSLayoutConstraint.activate([
            lineNumberView.topAnchor.constraint(equalTo: topAnchor),
            lineNumberView.leadingAnchor.constraint(equalTo: leadingAnchor),
            lineNumberView.bottomAnchor.constraint(equalTo: bottomAnchor),
            lineNumberView.widthAnchor.constraint(equalToConstant: 50),

            scrollView.topAnchor.constraint(equalTo: topAnchor),
            scrollView.leadingAnchor.constraint(equalTo: lineNumberView.trailingAnchor),
            scrollView.trailingAnchor.constraint(equalTo: trailingAnchor),
            scrollView.bottomAnchor.constraint(equalTo: bottomAnchor),

            textView.topAnchor.constraint(equalTo: scrollView.contentLayoutGuide.topAnchor),
            textView.leadingAnchor.constraint(equalTo: scrollView.contentLayoutGuide.leadingAnchor),
            textView.trailingAnchor.constraint(equalTo: scrollView.contentLayoutGuide.trailingAnchor),
            textView.bottomAnchor.constraint(equalTo: scrollView.contentLayoutGuide.bottomAnchor),
            textView.widthAnchor.constraint(greaterThanOrEqualTo: scrollView.frameLayoutGuide.widthAnchor),
        ])

        // Sync scrolling
        textView.addObserver(self, forKeyPath: "contentOffset", options: .new, context: nil)
    }

    override func observeValue(forKeyPath keyPath: String?, of object: Any?, change: [NSKeyValueChangeKey : Any]?, context: UnsafeMutableRawPointer?) {
        if keyPath == "contentOffset" {
            lineNumberView.contentOffset = textView.contentOffset
        }
    }

    func configure(fontSize: CGFloat, fontFamily: String, showLineNumbers: Bool) {
        self.showLineNumbers = showLineNumbers
        lineNumberView.isHidden = !showLineNumbers

        let font = UIFont(name: fontFamily, size: fontSize) ?? UIFont.monospacedSystemFont(ofSize: fontSize, weight: .regular)
        textView.font = font
        lineNumberView.font = font

        // Update line number view width constraint
        if showLineNumbers {
            for constraint in lineNumberView.constraints where constraint.firstAttribute == .width {
                constraint.constant = 50
            }
        } else {
            for constraint in lineNumberView.constraints where constraint.firstAttribute == .width {
                constraint.constant = 0
            }
        }

        updateLineNumbers()
    }

    func updateFont(fontSize: CGFloat, fontFamily: String) {
        let font = UIFont(name: fontFamily, size: fontSize) ?? UIFont.monospacedSystemFont(ofSize: fontSize, weight: .regular)
        textView.font = font
        lineNumberView.font = font
        updateLineNumbers()
    }

    func updateLineNumbers() {
        guard showLineNumbers else { return }

        let text = textView.text ?? ""

        // Efficiently count lines without creating array
        let newLineCount = text.isEmpty ? 1 : text.filter { $0 == "\n" }.count + 1

        // Get current cursor line efficiently
        let cursorPosition = textView.selectedRange.location
        var currentLine = 1
        var charCount = 0
        for char in text {
            if charCount >= cursorPosition { break }
            charCount += 1
            if char == "\n" { currentLine += 1 }
        }

        // Only rebuild if line count or current line changed
        guard newLineCount != cachedLineCount || currentLine != cachedCurrentLine else { return }
        cachedLineCount = newLineCount
        cachedCurrentLine = currentLine

        // Build line numbers string
        rebuildLineNumberText(lineCount: newLineCount, currentLine: currentLine)
    }

    private func rebuildLineNumberText(lineCount: Int, currentLine: Int) {
        let lineNumbers = (1...max(lineCount, 1)).map { lineNum -> NSAttributedString in
            let color: UIColor = lineNum == currentLine ? .label : .secondaryLabel
            return NSAttributedString(
                string: "\(lineNum)\n",
                attributes: [
                    .foregroundColor: color,
                    .font: lineNumberView.font ?? UIFont.monospacedSystemFont(ofSize: 14, weight: .regular)
                ]
            )
        }

        let attributedText = NSMutableAttributedString()
        for lineNumber in lineNumbers {
            attributedText.append(lineNumber)
        }

        lineNumberView.attributedText = attributedText
        lineNumberView.textAlignment = .right
    }

    func applySyntaxHighlighting(using highlighter: TLASyntaxHighlighter) {
        let text = textView.text ?? ""
        guard !text.isEmpty else { return }

        // Store current selection
        let selectedRange = textView.selectedRange

        // Apply highlighting
        let attributedString = highlighter.highlight(text, fontSize: textView.font?.pointSize ?? 14)

        // Set attributed text
        textView.attributedText = attributedString

        // Restore selection
        if selectedRange.location + selectedRange.length <= text.count {
            textView.selectedRange = selectedRange
        }
    }

    deinit {
        textView.removeObserver(self, forKeyPath: "contentOffset")
    }
}

// MARK: - Preview

#Preview {
    iOSTextEditor(
        text: .constant("""
        ---- MODULE Example ----
        EXTENDS Naturals

        VARIABLE x

        Init == x = 0

        Next == x' = x + 1

        Spec == Init /\\ [][Next]_x
        ====
        """),
        fontSize: 14,
        fontFamily: "Menlo"
    )
}
#endif
