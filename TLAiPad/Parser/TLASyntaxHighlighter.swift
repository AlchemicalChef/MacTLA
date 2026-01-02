import SwiftUI

/// Provides syntax highlighting for TLA+ code
final class TLASyntaxHighlighter {
    static let shared = TLASyntaxHighlighter()

    private init() {}

    // MARK: - Theme Configuration

    struct HighlightTheme {
        var keyword: Color = .purple
        var `operator`: Color = .blue
        var identifier: Color = .primary
        var number: Color = .orange
        var string: Color = .red
        var comment: Color = .gray
        var module: Color = .teal
        var constant: Color = .cyan
        var error: Color = .red

        static let `default` = HighlightTheme()

        static let dark = HighlightTheme(
            keyword: .purple,
            operator: .cyan,
            identifier: .white,
            number: .orange,
            string: .green,
            comment: Color(.systemGray),
            module: .yellow,
            constant: .pink,
            error: .red
        )
    }

    struct HighlightedRange {
        let range: Range<String.Index>
        let color: Color
        let style: HighlightStyle
    }

    enum HighlightStyle {
        case normal
        case bold
        case italic
    }

    // MARK: - Public Methods

    func highlight(_ source: String, theme: HighlightTheme = .default) -> AttributedString {
        let lexer = TLALexer(source: source)
        let tokens = lexer.scanTokens()
        let lineOffsets = precomputeLineOffsets(in: source)
        let sourceCount = source.count  // Cache - String.count is O(n)

        var attributedString = AttributedString(source)

        for token in tokens {
            guard token.length > 0 else { continue }

            let offset = characterOffset(for: token, using: lineOffsets)
            guard offset < sourceCount else { continue }

            let startIndex = source.index(source.startIndex, offsetBy: offset)
            guard startIndex < source.endIndex else { continue }

            let endIndex = source.index(startIndex, offsetBy: min(token.length, source.distance(from: startIndex, to: source.endIndex)))
            guard let range = Range(NSRange(startIndex..<endIndex, in: source), in: attributedString) else { continue }

            let (color, style) = colorAndStyle(for: token.type, theme: theme)

            attributedString[range].foregroundColor = color
            if style == .bold {
                attributedString[range].font = .system(.body, design: .monospaced).bold()
            } else if style == .italic {
                attributedString[range].font = .system(.body, design: .monospaced).italic()
            }
        }

        return attributedString
    }

    // MARK: - Private Methods

    /// Precomputes line start offsets for efficient line/column to character offset conversion - O(n) single pass
    private func precomputeLineOffsets(in source: String) -> [Int] {
        var lineOffsets = [0]  // Line 1 starts at offset 0
        var offset = 0
        for char in source {
            offset += 1
            if char == "\n" {
                lineOffsets.append(offset)
            }
        }
        return lineOffsets
    }

    /// Converts line/column to character offset using precomputed line offsets - O(1)
    private func characterOffset(for token: TLAToken, using lineOffsets: [Int]) -> Int {
        guard token.line >= 1 && token.line <= lineOffsets.count else {
            return 0
        }
        return lineOffsets[token.line - 1] + (token.column - 1)
    }

    /// Legacy method for backward compatibility - O(n) per call, avoid in loops
    private func characterOffset(for token: TLAToken, in source: String) -> Int {
        var offset = 0
        var currentLine = 1
        var currentColumn = 1

        for char in source {
            if currentLine == token.line && currentColumn == token.column {
                return offset
            }

            offset += 1
            if char == "\n" {
                currentLine += 1
                currentColumn = 1
            } else {
                currentColumn += 1
            }
        }

        return offset
    }

    private func colorAndStyle(for tokenType: TLATokenType, theme: HighlightTheme) -> (Color, HighlightStyle) {
        switch tokenType {
        case .keyword(let kw):
            switch kw {
            case .module, .extends:
                return (theme.module, .bold)
            case .constant, .constants, .variable, .variables:
                return (theme.constant, .bold)
            default:
                return (theme.keyword, .bold)
            }

        case .operator:
            return (theme.operator, .normal)

        case .identifier:
            return (theme.identifier, .normal)

        case .number:
            return (theme.number, .normal)

        case .string:
            return (theme.string, .normal)

        case .comment, .blockComment:
            return (theme.comment, .italic)

        case .moduleStart, .moduleEnd:
            return (theme.module, .bold)

        case .unknown:
            return (theme.error, .normal)

        default:
            return (theme.identifier, .normal)
        }
    }
}

// MARK: - NSAttributedString for UITextView (iOS)

#if os(iOS)
import UIKit

extension TLASyntaxHighlighter {
    /// Generates an NSAttributedString suitable for UITextView syntax highlighting
    func highlight(_ source: String, fontSize: CGFloat, fontFamily: String = "Menlo", theme: HighlightTheme = .default) -> NSAttributedString {
        let font = UIFont(name: fontFamily, size: fontSize) ?? .monospacedSystemFont(ofSize: fontSize, weight: .regular)
        return attributedStringForUITextView(source, font: font, theme: theme)
    }

    func attributedStringForUITextView(_ source: String, font: UIFont = .monospacedSystemFont(ofSize: 13, weight: .regular), theme: HighlightTheme = .default) -> NSAttributedString {
        let lexer = TLALexer(source: source)
        let tokens = lexer.scanTokens()
        let lineOffsets = precomputeLineOffsets(in: source)
        let sourceCount = source.count  // Cache - String.count is O(n)

        // Create mutable attributed string with default attributes
        let attributedString = NSMutableAttributedString(string: source, attributes: [
            .font: font,
            .foregroundColor: UIColor.label
        ])

        for token in tokens {
            guard token.length > 0 else { continue }

            let offset = characterOffset(for: token, using: lineOffsets)
            guard offset < sourceCount else { continue }

            let length = min(token.length, sourceCount - offset)
            let range = NSRange(location: offset, length: length)

            let (swiftUIColor, style) = colorAndStyle(for: token.type, theme: theme)
            let uiColor = uiColor(from: swiftUIColor)

            attributedString.addAttribute(.foregroundColor, value: uiColor, range: range)

            // Apply font style
            switch style {
            case .bold:
                let boldFont = UIFont.boldSystemFont(ofSize: font.pointSize)
                let monospacedBold = UIFont(name: "\(font.fontName)-Bold", size: font.pointSize) ?? boldFont
                attributedString.addAttribute(.font, value: monospacedBold, range: range)
            case .italic:
                let italicFont = UIFont.italicSystemFont(ofSize: font.pointSize)
                let monospacedItalic = UIFont(name: "\(font.fontName)-Italic", size: font.pointSize) ?? italicFont
                attributedString.addAttribute(.font, value: monospacedItalic, range: range)
            case .normal:
                break
            }
        }

        return attributedString
    }

    /// Convert SwiftUI Color to UIColor
    private func uiColor(from color: Color) -> UIColor {
        switch color {
        case .purple:
            return UIColor.systemPurple
        case .blue:
            return UIColor.systemBlue
        case .orange:
            return UIColor.systemOrange
        case .red:
            return UIColor.systemRed
        case .gray:
            return UIColor.systemGray
        case .green:
            return UIColor.systemGreen
        case .cyan:
            return UIColor.systemCyan
        case .teal:
            return UIColor.systemTeal
        case .pink:
            return UIColor.systemPink
        case .yellow:
            return UIColor.systemYellow
        case .white:
            return UIColor.white
        case .primary:
            return UIColor.label
        default:
            return UIColor(color)
        }
    }
}
#endif

// MARK: - NSAttributedString for NSTextView (macOS)

#if os(macOS)
import AppKit

extension TLASyntaxHighlighter {
    /// Generates an NSAttributedString suitable for NSTextView syntax highlighting
    func attributedStringForNSTextView(_ source: String, font: NSFont = .monospacedSystemFont(ofSize: 13, weight: .regular), theme: HighlightTheme = .default) -> NSAttributedString {
        let lexer = TLALexer(source: source)
        let tokens = lexer.scanTokens()
        let lineOffsets = precomputeLineOffsets(in: source)
        let sourceCount = source.count  // Cache - String.count is O(n)

        // Create mutable attributed string with default attributes
        let attributedString = NSMutableAttributedString(string: source, attributes: [
            .font: font,
            .foregroundColor: NSColor.textColor
        ])

        for token in tokens {
            guard token.length > 0 else { continue }

            let offset = characterOffset(for: token, using: lineOffsets)
            guard offset < sourceCount else { continue }

            let length = min(token.length, sourceCount - offset)
            let range = NSRange(location: offset, length: length)

            let (swiftUIColor, style) = colorAndStyle(for: token.type, theme: theme)
            let nsColor = nsColor(from: swiftUIColor)

            attributedString.addAttribute(.foregroundColor, value: nsColor, range: range)

            // Apply font style
            switch style {
            case .bold:
                if let boldFont = NSFontManager.shared.convert(font, toHaveTrait: .boldFontMask) as NSFont? {
                    attributedString.addAttribute(.font, value: boldFont, range: range)
                }
            case .italic:
                if let italicFont = NSFontManager.shared.convert(font, toHaveTrait: .italicFontMask) as NSFont? {
                    attributedString.addAttribute(.font, value: italicFont, range: range)
                }
            case .normal:
                break
            }
        }

        return attributedString
    }

    /// Applies syntax highlighting attributes directly to existing NSTextStorage
    /// This method does NOT replace the text content - it only modifies attributes
    func applyHighlightingAttributes(to textStorage: NSTextStorage, font: NSFont = .monospacedSystemFont(ofSize: 13, weight: .regular), theme: HighlightTheme = .default) {
        let source = textStorage.string
        guard !source.isEmpty else { return }

        let lexer = TLALexer(source: source)
        let tokens = lexer.scanTokens()
        let lineOffsets = precomputeLineOffsets(in: source)
        let sourceCount = source.count  // Cache - String.count is O(n)

        for token in tokens {
            guard token.length > 0 else { continue }

            let offset = characterOffset(for: token, using: lineOffsets)
            guard offset < sourceCount else { continue }

            let length = min(token.length, sourceCount - offset)
            let range = NSRange(location: offset, length: length)

            let (swiftUIColor, style) = colorAndStyle(for: token.type, theme: theme)
            let nsColor = nsColor(from: swiftUIColor)

            textStorage.addAttribute(.foregroundColor, value: nsColor, range: range)

            // Apply font style
            switch style {
            case .bold:
                if let boldFont = NSFontManager.shared.convert(font, toHaveTrait: .boldFontMask) as NSFont? {
                    textStorage.addAttribute(.font, value: boldFont, range: range)
                }
            case .italic:
                if let italicFont = NSFontManager.shared.convert(font, toHaveTrait: .italicFontMask) as NSFont? {
                    textStorage.addAttribute(.font, value: italicFont, range: range)
                }
            case .normal:
                break
            }
        }
    }

    /// Applies syntax highlighting using pre-tokenized tokens (for background tokenization)
    /// This version accepts tokens that were already computed on a background thread
    func applyHighlightingAttributesWithTokens(_ tokens: [TLAToken], to textStorage: NSTextStorage, font: NSFont = .monospacedSystemFont(ofSize: 13, weight: .regular), theme: HighlightTheme = .default) {
        let source = textStorage.string
        guard !source.isEmpty else { return }

        let lineOffsets = precomputeLineOffsets(in: source)
        let sourceCount = source.count  // Cache - String.count is O(n)

        // Collect all attributes first for batching
        var attributeOperations: [(NSRange, NSColor, NSFont?)] = []

        for token in tokens {
            guard token.length > 0 else { continue }

            let offset = characterOffset(for: token, using: lineOffsets)
            guard offset < sourceCount else { continue }

            let length = min(token.length, sourceCount - offset)
            let range = NSRange(location: offset, length: length)

            let (swiftUIColor, style) = colorAndStyle(for: token.type, theme: theme)
            let color = nsColor(from: swiftUIColor)

            var styledFont: NSFont? = nil
            switch style {
            case .bold:
                styledFont = NSFontManager.shared.convert(font, toHaveTrait: .boldFontMask)
            case .italic:
                styledFont = NSFontManager.shared.convert(font, toHaveTrait: .italicFontMask)
            case .normal:
                break
            }

            attributeOperations.append((range, color, styledFont))
        }

        // Apply all attributes in a single batch
        for (range, color, styledFont) in attributeOperations {
            textStorage.addAttribute(.foregroundColor, value: color, range: range)
            if let font = styledFont {
                textStorage.addAttribute(.font, value: font, range: range)
            }
        }
    }

    /// Prepared highlight operation for applying on main thread
    struct HighlightOperation: Sendable {
        let range: NSRange
        let colorKey: String
    }

    /// Prepare highlight operations on background thread (thread-safe, no UI calls)
    /// Returns operations that can be quickly applied on main thread
    func prepareHighlightOperations(
        tokens: [TLAToken],
        source: String
    ) -> [HighlightOperation] {
        guard !source.isEmpty else { return [] }

        let lineOffsets = precomputeLineOffsets(in: source)
        let sourceCount = source.count  // IMPORTANT: Cache this! String.count is O(n) in Swift
        var operations: [HighlightOperation] = []
        operations.reserveCapacity(tokens.count / 2)  // Rough estimate after filtering

        for token in tokens {
            guard token.length > 0 else { continue }

            // Skip tokens that use default text color
            if shouldSkipToken(token.type) { continue }

            let offset = characterOffset(for: token, using: lineOffsets)
            guard offset < sourceCount else { continue }

            let length = min(token.length, sourceCount - offset)
            let range = NSRange(location: offset, length: length)
            let key = colorKey(for: token.type)

            operations.append(HighlightOperation(range: range, colorKey: key))
        }

        return operations
    }

    /// Apply pre-computed highlight operations on main thread (fast, minimal work)
    func applyHighlightOperations(
        _ operations: [HighlightOperation],
        to layoutManager: NSLayoutManager,
        theme: HighlightTheme = .default
    ) {
        let colorCache = buildColorCache(theme: theme)

        for op in operations {
            let color = colorCache[op.colorKey] ?? NSColor.textColor
            layoutManager.addTemporaryAttribute(.foregroundColor, value: color, forCharacterRange: op.range)
        }
    }

    /// Apply highlighting using temporary attributes (no layout recalculation - FAST)
    /// This is the recommended approach for large files per Apple documentation.
    /// Temporary attributes are display-only and don't trigger re-layout.
    func applyHighlightingWithTemporaryAttributes(
        _ tokens: [TLAToken],
        to layoutManager: NSLayoutManager,
        source: String,
        theme: HighlightTheme = .default
    ) {
        guard !source.isEmpty else { return }

        let lineOffsets = precomputeLineOffsets(in: source)
        let sourceCount = source.count  // IMPORTANT: Cache this! String.count is O(n) in Swift

        // Pre-cache NSColor objects for better performance
        let colorCache = buildColorCache(theme: theme)

        for token in tokens {
            guard token.length > 0 else { continue }

            // Skip tokens that use default text color (identifiers, etc.)
            // This significantly reduces the number of attribute operations
            if shouldSkipToken(token.type) { continue }

            let offset = characterOffset(for: token, using: lineOffsets)
            guard offset < sourceCount else { continue }

            let length = min(token.length, sourceCount - offset)
            let range = NSRange(location: offset, length: length)

            // Use cached color lookup
            let color = colorCache[colorKey(for: token.type)] ?? NSColor.textColor
            layoutManager.addTemporaryAttribute(.foregroundColor, value: color, forCharacterRange: range)
        }
    }

    /// Check if token uses default text color and can be skipped
    private func shouldSkipToken(_ tokenType: TLATokenType) -> Bool {
        switch tokenType {
        case .identifier:
            return true  // Identifiers use default text color
        case .eof:
            return true  // EOF has no visual representation
        case .leftParen, .rightParen, .leftBracket, .rightBracket,
             .leftBrace, .rightBrace, .comma, .colon, .doubleColon,
             .semicolon, .dot, .exclamation, .pipe, .subscriptSeparator:
            return true  // Delimiters use default text color
        default:
            return false
        }
    }

    /// Generate a key for color cache lookup
    private func colorKey(for tokenType: TLATokenType) -> String {
        switch tokenType {
        case .keyword(let kw):
            switch kw {
            case .module, .extends:
                return "module"
            case .constant, .constants, .variable, .variables:
                return "constant"
            default:
                return "keyword"
            }
        case .operator: return "operator"
        case .number: return "number"
        case .string: return "string"
        case .comment, .blockComment: return "comment"
        case .moduleStart, .moduleEnd: return "module"
        case .unknown: return "error"
        default: return "default"
        }
    }

    /// Build a cache of NSColor objects for each token category
    private func buildColorCache(theme: HighlightTheme) -> [String: NSColor] {
        return [
            "keyword": nsColor(from: theme.keyword),
            "constant": nsColor(from: theme.constant),
            "operator": nsColor(from: theme.operator),
            "number": nsColor(from: theme.number),
            "string": nsColor(from: theme.string),
            "comment": nsColor(from: theme.comment),
            "module": nsColor(from: theme.module),
            "error": nsColor(from: theme.error),
            "default": NSColor.textColor
        ]
    }

    /// Convert SwiftUI Color to NSColor
    private func nsColor(from color: Color) -> NSColor {
        // Handle standard colors
        switch color {
        case .purple:
            return NSColor.systemPurple
        case .blue:
            return NSColor.systemBlue
        case .orange:
            return NSColor.systemOrange
        case .red:
            return NSColor.systemRed
        case .gray:
            return NSColor.systemGray
        case .green:
            return NSColor.systemGreen
        case .cyan:
            return NSColor.systemCyan
        case .teal:
            return NSColor.systemTeal
        case .pink:
            return NSColor.systemPink
        case .yellow:
            return NSColor.systemYellow
        case .white:
            return NSColor.white
        case .primary:
            return NSColor.textColor
        default:
            // Try to resolve via NSColor
            return NSColor(color)
        }
    }
}
#endif

// MARK: - Line-based highlighting for editor

extension TLASyntaxHighlighter {
    struct LineHighlight {
        let lineNumber: Int
        let segments: [HighlightSegment]
    }

    struct HighlightSegment {
        let range: NSRange
        let color: Color
        let isBold: Bool
        let isItalic: Bool
    }

    func highlightLines(_ source: String, theme: HighlightTheme = .default) -> [LineHighlight] {
        let lexer = TLALexer(source: source)
        let tokens = lexer.scanTokens()

        var lineHighlights: [Int: [HighlightSegment]] = [:]

        for token in tokens {
            guard token.length > 0 else { continue }

            let (color, style) = colorAndStyle(for: token.type, theme: theme)
            let segment = HighlightSegment(
                range: NSRange(location: token.column - 1, length: token.length),
                color: color,
                isBold: style == .bold,
                isItalic: style == .italic
            )

            if lineHighlights[token.line] == nil {
                lineHighlights[token.line] = []
            }
            lineHighlights[token.line]?.append(segment)
        }

        return lineHighlights
            .sorted { $0.key < $1.key }
            .map { LineHighlight(lineNumber: $0.key, segments: $0.value) }
    }
}
