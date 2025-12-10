import SwiftUI

/// Provides syntax highlighting for TLA+ code
final class TLASyntaxHighlighter {
    static let shared = TLASyntaxHighlighter()

    private init() {}

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

    func highlight(_ source: String, theme: HighlightTheme = .default) -> AttributedString {
        let lexer = TLALexer(source: source)
        let tokens = lexer.scanTokens()

        var attributedString = AttributedString(source)

        for token in tokens {
            guard token.length > 0 else { continue }

            let startIndex = source.index(source.startIndex, offsetBy: characterOffset(for: token, in: source))
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

// MARK: - NSAttributedString for NSTextView (macOS)

#if os(macOS)
import AppKit

extension TLASyntaxHighlighter {
    /// Generates an NSAttributedString suitable for NSTextView syntax highlighting
    func attributedStringForNSTextView(_ source: String, font: NSFont = .monospacedSystemFont(ofSize: 13, weight: .regular), theme: HighlightTheme = .default) -> NSAttributedString {
        let lexer = TLALexer(source: source)
        let tokens = lexer.scanTokens()

        // Create mutable attributed string with default attributes
        let attributedString = NSMutableAttributedString(string: source, attributes: [
            .font: font,
            .foregroundColor: NSColor.textColor
        ])

        for token in tokens {
            guard token.length > 0 else { continue }

            let offset = characterOffset(for: token, in: source)
            guard offset < source.count else { continue }

            let length = min(token.length, source.count - offset)
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

        for token in tokens {
            guard token.length > 0 else { continue }

            let offset = characterOffset(for: token, in: source)
            guard offset < source.count else { continue }

            let length = min(token.length, source.count - offset)
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
