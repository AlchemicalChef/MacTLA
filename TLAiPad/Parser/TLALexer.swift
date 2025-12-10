import Foundation

/// Token types for TLA+ lexical analysis
enum TLATokenType: Equatable {
    // Keywords
    case keyword(TLAKeyword)

    // Literals
    case identifier(String)
    case number(Int)
    case string(String)

    // Operators
    case `operator`(TLAOperator)

    // Delimiters
    case leftParen
    case rightParen
    case leftBracket
    case rightBracket
    case leftBrace
    case rightBrace
    case leftAngle          // <<
    case rightAngle         // >>
    case comma
    case colon
    case doubleColon        // :: (used in proofs)
    case semicolon
    case dot
    case exclamation        // ! (used in EXCEPT expressions)
    case pipe               // | (used in set builder notation)
    case subscriptSeparator // _ (used in [A]_v and <<A>>_v when not part of identifier)

    // Special
    case moduleStart       // ----
    case moduleEnd         // ====
    case comment(String)
    case blockComment(String)

    // Error
    case unknown(String)
    case eof
}

enum TLAKeyword: String, CaseIterable {
    // Module structure
    case module = "MODULE"
    case extends = "EXTENDS"
    case constant = "CONSTANT"
    case constants = "CONSTANTS"
    case variable = "VARIABLE"
    case variables = "VARIABLES"
    case instance = "INSTANCE"
    case with = "WITH"
    case local = "LOCAL"
    case specification = "SPECIFICATION"
    case invariant = "INVARIANT"
    case property = "PROPERTY"

    // Assumptions and theorems
    case assume = "ASSUME"
    case assumption = "ASSUMPTION"
    case axiom = "AXIOM"
    case theorem = "THEOREM"
    case lemma = "LEMMA"
    case proposition = "PROPOSITION"
    case corollary = "COROLLARY"

    // Proof keywords
    case proof = "PROOF"
    case by = "BY"
    case qed = "QED"
    case obvious = "OBVIOUS"
    case omitted = "OMITTED"
    case take = "TAKE"
    case have = "HAVE"
    case witness = "WITNESS"
    case pick = "PICK"
    case suffices = "SUFFICES"
    case prove = "PROVE"
    case use = "USE"
    case hide = "HIDE"
    case define = "DEFINE"
    case def = "DEF"
    case only = "ONLY"
    case new_ = "NEW"
    case state = "STATE"
    case action = "ACTION"
    case temporal = "TEMPORAL"

    // Boolean constants
    case true_ = "TRUE"
    case false_ = "FALSE"

    // Definitions
    case recursive = "RECURSIVE"
    case let_ = "LET"
    case in_ = "IN"

    // Control flow
    case if_ = "IF"
    case then = "THEN"
    case else_ = "ELSE"
    case case_ = "CASE"
    case other = "OTHER"

    // Set/function operations
    case choose = "CHOOSE"
    case except = "EXCEPT"
    case domain = "DOMAIN"
    case subset = "SUBSET"
    case union = "UNION"
    case intersect = "INTERSECT"
    case lambda = "LAMBDA"

    // Temporal/action
    case enabled = "ENABLED"
    case unchanged = "UNCHANGED"
    case sf = "SF_"
    case wf = "WF_"

    // PlusCal keywords
    case algorithm = "algorithm"
    case fair = "fair"
    case process = "process"
    case begin = "begin"
    case end = "end"
    case await = "await"
    case when = "when"
    case `while` = "while"
    case `do` = "do"
    case either = "either"
    case or = "or"
    case skip = "skip"
    case `return` = "return"
    case goto = "goto"
    case call = "call"
    case procedure = "procedure"
    case macro = "macro"
    case print = "print"
    case assert = "assert"
}

enum TLAOperator: String, CaseIterable {
    // Logical
    case conjunction = "/\\"
    case disjunction = "\\/"
    case negation = "~"
    case implication = "=>"
    case equivalence = "<=>"
    case forall = "\\A"
    case exists = "\\E"
    case negationAlt = "\\lnot"
    case conjunctionAlt = "\\land"
    case disjunctionAlt = "\\lor"

    // Temporal
    case always = "[]"
    case eventually = "<>"
    case leadsto = "~>"
    case weakFairnessLeadsto = "-+->"  // Weak fairness leads-to operator
    // Note: WF_ and SF_ are in TLAKeyword enum, not here (to avoid duplicates)

    // Set operations
    case elementOf = "\\in"
    case notElementOf = "\\notin"
    case subsetOf = "\\subseteq"
    case supersetOf = "\\supseteq"
    case properSubset = "\\subset"
    case properSuperset = "\\supset"
    case setMinus = "\\"
    case times = "\\X"
    case cup = "\\cup"
    case cap = "\\cap"
    case unionAlt = "\\union"
    case intersectAlt = "\\intersect"
    case uplus = "\\uplus"

    // Relations
    case equal = "="
    case notEqual = "#"
    case notEqualAlt = "/="
    case notEqualUnicode = "\\neq"
    case lessThan = "<"
    case lessThanOrEqual = "<="
    case lessThanOrEqualAlt = "\\leq"
    case greaterThan = ">"
    case greaterThanOrEqual = ">="
    case greaterThanOrEqualAlt = "\\geq"
    case prec = "\\prec"
    case preceq = "\\preceq"
    case succ = "\\succ"
    case succeq = "\\succeq"
    case sim = "\\sim"
    case simeq = "\\simeq"
    case approx = "\\approx"
    case cong = "\\cong"
    case doteq = "\\doteq"
    case propto = "\\propto"
    case asymp = "\\asymp"

    // Arithmetic
    case plus = "+"
    case minus = "-"
    case multiply = "*"
    case divide = "/"
    case intDivide = "\\div"
    case modulo = "%"
    case power = "^"
    case dotDot = ".."

    // Sequence operations
    case concat = "\\o"
    case concatAlt = "\\circ"

    // Assignment and primes
    case prime = "'"
    case assign = ":="
    case define = "=="
    case mapsto = "|->"
    case colonGreater = ":>"  // TLC module: x :> y creates [z \in {x} |-> y]

    // Arrows
    case rightArrow = "->"
    case leftArrow = "<-"
    case mapsTo = "\\mapsto"

    // Square operators
    case sqcap = "\\sqcap"
    case sqcup = "\\sqcup"
    case sqsubseteq = "\\sqsubseteq"
    case sqsupseteq = "\\sqsupseteq"

    // Other
    case cdot = "\\cdot"
    case bullet = "\\bullet"
    case star = "\\star"
    case bigcirc = "\\bigcirc"
    case wr = "\\wr"
    case oplus = "\\oplus"
    case ominus = "\\ominus"
    case otimes = "\\otimes"
    case oslash = "\\oslash"
    case odot = "\\odot"

    // Function override
    case functionOverride = "@@"

    // BNF
    case bnfDef = "::="
}

/// Token with position information
struct TLAToken: Equatable {
    let type: TLATokenType
    let lexeme: String
    let line: Int
    let column: Int
    let length: Int

    var range: Range<Int> {
        column..<(column + length)
    }
}

/// Lexer for TLA+ source code
final class TLALexer {
    private let source: String
    private var tokens: [TLAToken] = []
    private var start: String.Index
    private var current: String.Index
    private var line: Int = 1
    private var column: Int = 1
    private var startColumn: Int = 1

    init(source: String) {
        self.source = source
        self.start = source.startIndex
        self.current = source.startIndex
    }

    func scanTokens() -> [TLAToken] {
        tokens = []

        while !isAtEnd {
            start = current
            startColumn = column
            scanToken()
        }

        tokens.append(TLAToken(type: .eof, lexeme: "", line: line, column: column, length: 0))
        return tokens
    }

    private var isAtEnd: Bool {
        current >= source.endIndex
    }

    private func scanToken() {
        let c = advance()

        switch c {
        case "(":
            if match("*") {
                // TLA+ block comment (* *)
                scanTLABlockComment()
            } else {
                addToken(.leftParen)
            }
        case ")": addToken(.rightParen)
        case "[":
            if peek() == "]" {
                _ = advance()
                addToken(.operator(.always))  // [] is the always (box) operator
            } else {
                addToken(.leftBracket)
            }
        case "]": addToken(.rightBracket)
        case "{": addToken(.leftBrace)
        case "}": addToken(.rightBrace)
        case ",": addToken(.comma)
        case ";": addToken(.semicolon)
        case "'": addToken(.operator(.prime))
        case "+": addToken(.operator(.plus))
        case "*": addToken(.operator(.multiply))
        case "%": addToken(.operator(.modulo))
        case "^": addToken(.operator(.power))
        case "#": addToken(.operator(.notEqual))
        case "~":
            if peek() == ">" {
                _ = advance()
                addToken(.operator(.leadsto))
            } else {
                addToken(.operator(.negation))
            }
        case "-":
            if match("-") {
                if match("-") && match("-") {
                    // Module start: ----
                    while peek() == "-" { _ = advance() }
                    addToken(.moduleStart)
                } else {
                    // Comment
                    scanLineComment()
                }
            } else if match("+") {
                if match("-") && match(">") {
                    addToken(.operator(.weakFairnessLeadsto))  // -+->
                } else {
                    // Backtrack - we consumed + but it's not -+->
                    // This is an error case, treat as minus followed by plus
                    current = source.index(before: current)  // Put back the +
                    column -= 1
                    addToken(.operator(.minus))
                }
            } else if match(">") {
                addToken(.operator(.rightArrow))
            } else {
                addToken(.operator(.minus))
            }
        case "=":
            if match("=") {
                // Check for module end (====) before define (==)
                if match("=") && match("=") {
                    // Module end: ====
                    while peek() == "=" { _ = advance() }
                    addToken(.moduleEnd)
                } else {
                    addToken(.operator(.define))
                }
            } else if match(">") {
                addToken(.operator(.implication))
            } else {
                addToken(.operator(.equal))
            }
        case "<":
            if match("<") {
                // << for tuple/sequence start
                addToken(.leftAngle)
            } else if match("=") {
                if match(">") {
                    addToken(.operator(.equivalence))
                } else {
                    addToken(.operator(.lessThanOrEqual))
                }
            } else if match(">") {
                addToken(.operator(.eventually))
            } else if match("-") {
                addToken(.operator(.leftArrow))
            } else {
                addToken(.operator(.lessThan))
            }
        case ">":
            if match(">") {
                // >> for tuple/sequence end
                addToken(.rightAngle)
            } else if match("=") {
                addToken(.operator(.greaterThanOrEqual))
            } else {
                addToken(.operator(.greaterThan))
            }
        case "/":
            if match("\\") {
                addToken(.operator(.conjunction))
            } else if match("=") {
                addToken(.operator(.notEqualAlt))
            } else if match("*") {
                scanBlockComment()
            } else {
                addToken(.operator(.divide))
            }
        case "\\":
            scanBackslashOperator()
        case ":":
            if match(":") {
                if match("=") {
                    addToken(.operator(.bnfDef))
                } else {
                    // :: is used in proof syntax
                    addToken(.doubleColon)
                }
            } else if match("=") {
                addToken(.operator(.assign))
            } else if match(">") {
                addToken(.operator(.colonGreater))  // :> operator from TLC module
            } else {
                addToken(.colon)
            }
        case "|":
            if match("-") && match(">") {
                addToken(.operator(.mapsto))
            } else {
                addToken(.pipe)
            }
        case "@":
            if match("@") {
                addToken(.operator(.functionOverride))
            } else {
                addToken(.unknown("@"))
            }
        case "!":
            addToken(.exclamation)
        case ".":
            if match(".") {
                addToken(.operator(.dotDot))
            } else {
                addToken(.dot)
            }
        case "\"":
            scanString()
        case " ", "\r", "\t":
            break // Ignore whitespace
        case "\n":
            line += 1
            column = 1

        // Unicode operator support (TLA+ specification compliance)
        case "∈": addToken(.operator(.elementOf))          // \in
        case "∉": addToken(.operator(.notElementOf))       // \notin
        case "⊆": addToken(.operator(.subsetOf))           // \subseteq
        case "⊇": addToken(.operator(.supersetOf))         // \supseteq
        case "⊂": addToken(.operator(.properSubset))       // \subset
        case "⊃": addToken(.operator(.properSuperset))     // \supset
        case "∪": addToken(.operator(.cup))                // \cup
        case "∩": addToken(.operator(.cap))                // \cap
        case "¬": addToken(.operator(.negation))           // ~
        case "∧": addToken(.operator(.conjunction))        // /\
        case "∨": addToken(.operator(.disjunction))        // \/
        case "⇒": addToken(.operator(.implication))        // =>
        case "⟺", "⇔": addToken(.operator(.equivalence))  // <=>
        case "∀": addToken(.operator(.forall))             // \A
        case "∃": addToken(.operator(.exists))             // \E
        case "□": addToken(.operator(.always))             // []
        case "◇": addToken(.operator(.eventually))         // <>
        case "↝": addToken(.operator(.leadsto))            // ~>
        case "≠": addToken(.operator(.notEqual))           // #
        case "≤": addToken(.operator(.lessThanOrEqual))    // <=
        case "≥": addToken(.operator(.greaterThanOrEqual)) // >=
        case "×": addToken(.operator(.times))              // \X
        case "÷": addToken(.operator(.divide))             // \div
        case "′": addToken(.operator(.prime))              // ' (prime mark)

        case "_":
            // Check if underscore is standalone (subscript separator) or part of identifier
            if peek().isTLALetter || peek().isNumber || peek() == "_" {
                // Part of identifier like _foo or continuing underscore
                scanIdentifier()
            } else {
                // Standalone underscore - subscript separator for [A]_v or <<A>>_v
                addToken(.subscriptSeparator)
            }

        default:
            if c.isNumber {
                scanNumber()
            } else if c.isTLALetter {
                scanIdentifier()
            } else {
                addToken(.unknown(String(c)))
            }
        }
    }

    private func scanLineComment() {
        while peek() != "\n" && !isAtEnd {
            _ = advance()
        }
        let comment = String(source[start..<current])
        addToken(.comment(comment))
    }

    private func scanBlockComment() {
        var depth = 1
        while depth > 0 && !isAtEnd {
            if peek() == "/" && peekNext() == "*" {
                _ = advance()
                _ = advance()
                depth += 1
            } else if peek() == "*" && peekNext() == "/" {
                _ = advance()
                _ = advance()
                depth -= 1
            } else {
                if peek() == "\n" {
                    line += 1
                    column = 1
                }
                _ = advance()
            }
        }
        if depth > 0 {
            // Unclosed comment - report error
            addToken(.unknown("Unclosed block comment"))
        } else {
            let comment = String(source[start..<current])
            addToken(.blockComment(comment))
        }
    }

    private func scanTLABlockComment() {
        // TLA+ block comments use (* *) and can be nested
        var depth = 1
        while depth > 0 && !isAtEnd {
            if peek() == "(" && peekNext() == "*" {
                _ = advance()
                _ = advance()
                depth += 1
            } else if peek() == "*" && peekNext() == ")" {
                _ = advance()
                _ = advance()
                depth -= 1
            } else {
                if peek() == "\n" {
                    line += 1
                    column = 1
                }
                _ = advance()
            }
        }
        if depth > 0 {
            // Unclosed comment - report error
            addToken(.unknown("Unclosed block comment"))
        } else {
            let comment = String(source[start..<current])
            addToken(.blockComment(comment))
        }
    }

    private func scanString() {
        var stringValue = ""

        while peek() != "\"" && !isAtEnd {
            if peek() == "\n" {
                line += 1
                column = 1
                stringValue.append(advance())
            } else if peek() == "\\" {
                // Handle escape sequences
                _ = advance() // consume backslash
                if !isAtEnd {
                    let escaped = advance()
                    switch escaped {
                    case "\"": stringValue.append("\"")
                    case "\\": stringValue.append("\\")
                    case "n": stringValue.append("\n")
                    case "t": stringValue.append("\t")
                    case "r": stringValue.append("\r")
                    default:
                        // Unknown escape - keep as-is
                        stringValue.append("\\")
                        stringValue.append(escaped)
                    }
                }
            } else {
                stringValue.append(advance())
            }
        }

        if isAtEnd {
            addToken(.unknown("Unterminated string"))
            return
        }

        _ = advance() // Closing quote
        addToken(.string(stringValue))
    }

    private func scanNumber() {
        while peek().isNumber {
            _ = advance()
        }
        let numStr = String(source[start..<current])
        if let value = Int(numStr) {
            addToken(.number(value))
        } else {
            // Try to handle very large numbers by storing as string
            // This allows the parser to provide a more helpful error message
            // with the exact location and original value
            addToken(.unknown("Number too large for Int: '\(numStr)' (max: \(Int.max))"))
        }
    }

    private func scanIdentifier() {
        while peek().isTLALetter || peek().isNumber || peek() == "_" {
            _ = advance()

            // Special handling for WF_ and SF_ - these are keywords that should stop
            // before consuming the subscript variable (e.g., WF_vars -> WF_ + vars)
            let text = String(source[start..<current])
            if text == "WF_" || text == "SF_" {
                // Stop here - emit the keyword and let the next scan handle the rest
                addToken(.keyword(TLAKeyword(rawValue: text)!))
                return
            }
        }

        let text = String(source[start..<current])

        if let keyword = TLAKeyword(rawValue: text) {
            addToken(.keyword(keyword))
        } else {
            addToken(.identifier(text))
        }
    }

    private func scanBackslashOperator() {
        // Check for TLA+ line comment: \*
        if peek() == "*" {
            _ = advance() // consume *
            scanLineComment()
            return
        }

        // Check for multi-character operators starting with \
        // Order matters: longer matches first
        let operators: [(String, TLAOperator)] = [
            // Logical
            ("lnot", .negationAlt),
            ("land", .conjunctionAlt),
            ("lor", .disjunctionAlt),
            ("/", .disjunction),

            // Quantifiers
            ("A", .forall),
            ("E", .exists),

            // Set operations (longer first)
            ("subseteq", .subsetOf),
            ("supseteq", .supersetOf),
            ("subset", .properSubset),
            ("supset", .properSuperset),
            ("notin", .notElementOf),
            ("in", .elementOf),
            ("union", .unionAlt),
            ("intersect", .intersectAlt),
            ("cup", .cup),
            ("cap", .cap),
            ("uplus", .uplus),
            ("X", .times),

            // Relations (longer first)
            ("preceq", .preceq),
            ("prec", .prec),
            ("succeq", .succeq),
            ("succ", .succ),
            ("simeq", .simeq),
            ("sim", .sim),
            ("approx", .approx),
            ("cong", .cong),
            ("doteq", .doteq),
            ("propto", .propto),
            ("asymp", .asymp),
            ("leq", .lessThanOrEqualAlt),
            ("geq", .greaterThanOrEqualAlt),
            ("neq", .notEqualUnicode),

            // Square operators
            ("sqsubseteq", .sqsubseteq),
            ("sqsupseteq", .sqsupseteq),
            ("sqcap", .sqcap),
            ("sqcup", .sqcup),

            // Arithmetic
            ("div", .intDivide),

            // Sequence
            ("circ", .concatAlt),
            ("o", .concat),

            // Circle operators
            ("bigcirc", .bigcirc),
            ("oplus", .oplus),
            ("ominus", .ominus),
            ("otimes", .otimes),
            ("oslash", .oslash),
            ("odot", .odot),

            // Other
            ("cdot", .cdot),
            ("bullet", .bullet),
            ("star", .star),
            ("wr", .wr),
            ("mapsto", .mapsTo),
        ]

        for (suffix, op) in operators {
            if matchSequence(suffix) {
                addToken(.operator(op))
                return
            }
        }

        // Just a backslash (set minus)
        addToken(.operator(.setMinus))
    }

    private func matchSequence(_ expected: String) -> Bool {
        var tempCurrent = current
        for char in expected {
            guard tempCurrent < source.endIndex,
                  source[tempCurrent] == char else {
                return false
            }
            tempCurrent = source.index(after: tempCurrent)
        }
        // Advance current to after the matched sequence
        for _ in expected {
            _ = advance()
        }
        return true
    }

    @discardableResult
    private func advance() -> Character {
        let c = source[current]
        current = source.index(after: current)
        column += 1
        return c
    }

    private func peek() -> Character {
        guard !isAtEnd else { return "\0" }
        return source[current]
    }

    private func peekNext() -> Character {
        let next = source.index(after: current)
        guard next < source.endIndex else { return "\0" }
        return source[next]
    }

    private func match(_ expected: Character) -> Bool {
        guard !isAtEnd, source[current] == expected else { return false }
        current = source.index(after: current)
        column += 1
        return true
    }

    private func addToken(_ type: TLATokenType) {
        let lexeme = String(source[start..<current])
        let token = TLAToken(
            type: type,
            lexeme: lexeme,
            line: line,
            column: startColumn,
            length: lexeme.count
        )
        tokens.append(token)
    }
}

// Helper extension
private extension Character {
    var isNumber: Bool {
        self >= "0" && self <= "9"
    }

    /// Unicode-aware letter check for TLA+ identifier support
    /// Allows Greek letters and other Unicode letters in identifiers
    var isTLALetter: Bool {
        // Use ASCII check for base Latin letters
        let isASCII = (self >= "a" && self <= "z") || (self >= "A" && self <= "Z")
        if isASCII { return true }
        // Check for Unicode letters (Greek, etc.) using scalar properties
        guard let scalar = self.unicodeScalars.first else { return false }
        return CharacterSet.letters.contains(scalar)
    }
}
