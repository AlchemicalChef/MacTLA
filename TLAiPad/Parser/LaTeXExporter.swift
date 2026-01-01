import Foundation

/// Converts TLA+ specifications to LaTeX format
class LaTeXExporter {
    static let shared = LaTeXExporter()

    private init() {}

    // MARK: - Main Export Function

    /// Converts TLA+ source code to LaTeX
    func exportToLaTeX(_ source: String, title: String? = nil) -> String {
        var latex = """
        \\documentclass[11pt]{article}
        \\usepackage{tlatex}
        \\usepackage{amsmath}
        \\usepackage{amssymb}
        \\usepackage{geometry}
        \\geometry{margin=1in}

        \\begin{document}

        """

        if let title = title {
            latex += """
            \\title{\\textbf{\(escapeLatex(title))}}
            \\maketitle

            """
        }

        // Parse and convert
        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            latex += convertModule(module)
        case .failure:
            // Fallback: escape the source and render as verbatim
            latex += """
            \\begin{verbatim}
            \(source)
            \\end{verbatim}
            """
        }

        latex += """

        \\end{document}
        """

        return latex
    }

    // MARK: - Module Conversion

    private func convertModule(_ module: TLAModule) -> String {
        var latex = """
        \\begin{tla}
        \\tlamodule{\(escapeLatex(module.name))}

        """

        // EXTENDS
        if !module.extends.isEmpty {
            latex += "\\textsc{extends} \(module.extends.map(escapeLatex).joined(separator: ", "))\n\n"
        }

        // Declarations
        for decl in module.declarations {
            latex += convertDeclaration(decl)
            latex += "\n"
        }

        latex += """
        \\tlaendmodule
        \\end{tla}
        """

        return latex
    }

    // MARK: - Declaration Conversion

    private func convertDeclaration(_ decl: TLADeclaration) -> String {
        switch decl {
        case .constant(let d):
            return "\\textsc{constant} \(d.names.map(escapeLatex).joined(separator: ", "))\n"

        case .variable(let d):
            return "\\textsc{variable} \(d.names.map(escapeLatex).joined(separator: ", "))\n"

        case .operatorDef(let def):
            return convertOperatorDef(def)

        case .theorem(let d):
            var latex = "\\textsc{theorem}"
            if let name = d.name {
                latex += " \(escapeLatex(name))"
            }
            latex += " $\\triangleq$ \(convertExpression(d.body))\n"
            return latex

        case .assumption(let d):
            var latex = "\\textsc{assume}"
            if let name = d.name {
                latex += " \(escapeLatex(name))"
            }
            latex += " $\\triangleq$ \(convertExpression(d.body))\n"
            return latex

        case .instance(let d):
            var latex = ""
            if let name = d.name {
                latex += "\(escapeLatex(name)) $\\triangleq$ "
            }
            latex += "\\textsc{instance} \(escapeLatex(d.moduleName))"
            if !d.substitutions.isEmpty {
                let subs = d.substitutions.map { "\(escapeLatex($0.parameter)) $\\leftarrow$ \(convertExpression($0.expression))" }
                latex += " \\textsc{with} \(subs.joined(separator: ", "))"
            }
            latex += "\n"
            return latex

        case .specification(let d):
            // SpecificationDeclaration only has name, not a formula
            return "\\textsc{specification} \(escapeLatex(d.name))\n"

        case .invariant(let d):
            return "\\textsc{invariant} \(d.names.map(escapeLatex).joined(separator: ", "))\n"

        case .property(let d):
            return "\\textsc{property} \(d.names.map(escapeLatex).joined(separator: ", "))\n"

        case .recursiveDecl(let d):
            let params = d.parameterCount > 0 ? "(\(Array(repeating: "\\_", count: d.parameterCount).joined(separator: ", ")))" : ""
            return "\\textsc{recursive} \(escapeLatex(d.name))\(params)\n"
        }
    }

    private func convertOperatorDef(_ def: OperatorDefinition) -> String {
        var latex = escapeLatex(def.name)

        if !def.parameters.isEmpty {
            let params = def.parameterNames.map(escapeLatex).joined(separator: ", ")
            latex += "(\(params))"
        }

        latex += " $\\triangleq$ "
        latex += convertExpression(def.body)
        latex += "\n"

        return latex
    }

    // MARK: - Expression Conversion

    private func convertExpression(_ expr: TLAExpression) -> String {
        switch expr {
        case .identifier(let name, _):
            return escapeLatex(name)

        case .number(let n, _):
            return String(n)

        case .string(let s, _):
            return "``\(escapeLatex(s))''"

        case .boolean(let b, _):
            return b ? "\\textsc{true}" : "\\textsc{false}"

        case .setEnumeration(let elements, _):
            let elems = elements.map { convertExpression($0) }.joined(separator: ", ")
            return "\\{$\(elems)$\\}"

        case .tuple(let elements, _):
            let elems = elements.map { convertExpression($0) }.joined(separator: ", ")
            return "$\\langle$\(elems)$\\rangle$"

        case .recordConstruction(let fields, _):
            let fs = fields.map { "\(escapeLatex($0.0)) $\\mapsto$ \(convertExpression($0.1))" }
            return "[\(fs.joined(separator: ", "))]"

        case .recordAccess(let expr, let field, _):
            return "\(convertExpression(expr)).\(escapeLatex(field))"

        case .functionConstruction(let bindings, let body, _):
            let bs = bindings.map { "\(convertBoundVariable($0))" }
            return "[\(bs.joined(separator: ", ")) $\\mapsto$ \(convertExpression(body))]"

        case .setComprehension(let binding, let predicate, _):
            return "\\{\(convertBoundVariable(binding)): \(convertExpression(predicate))\\}"

        case .setMap(let mapExpr, let binding, _):
            return "\\{\(convertExpression(mapExpr)): \(convertBoundVariable(binding))\\}"

        case .setRange(let from, let to, _):
            return "\(convertExpression(from))..\(convertExpression(to))"

        case .binary(let left, let op, let right, _):
            return "(\(convertExpression(left)) \(convertBinaryOp(op)) \(convertExpression(right)))"

        case .unary(let op, let operand, _):
            return "\(convertUnaryOp(op))\(convertExpression(operand))"

        case .ternary(let cond, let then, let else_, _):
            return "\\textsc{if} \(convertExpression(cond)) \\textsc{then} \(convertExpression(then)) \\textsc{else} \(convertExpression(else_))"

        case .forall(let bindings, let body, _):
            let bs = bindings.map { convertBoundVariable($0) }
            return "$\\forall$ \(bs.joined(separator: ", ")): \(convertExpression(body))"

        case .exists(let bindings, let body, _):
            let bs = bindings.map { convertBoundVariable($0) }
            return "$\\exists$ \(bs.joined(separator: ", ")): \(convertExpression(body))"

        case .choose(let binding, let predicate, _):
            return "\\textsc{choose} \(convertBoundVariable(binding)): \(convertExpression(predicate))"

        case .caseExpr(let cases, let other, _):
            var latex = "\\textsc{case} "
            let cs = cases.map { "\(convertExpression($0.condition)) $\\rightarrow$ \(convertExpression($0.result))" }
            latex += cs.joined(separator: " $\\Box$ ")
            if let oth = other {
                latex += " $\\Box$ \\textsc{other} $\\rightarrow$ \(convertExpression(oth))"
            }
            return latex

        case .letIn(let defs, let body, _):
            var latex = "\\textsc{let} "
            let ds = defs.map { "\(escapeLatex($0.name)) $\\triangleq$ \(convertExpression($0.body))" }
            latex += ds.joined(separator: ", ")
            latex += " \\textsc{in} \(convertExpression(body))"
            return latex

        case .functionApplication(let func_, let args, _):
            let argStr = args.map { convertExpression($0) }.joined(separator: ", ")
            return "\(convertExpression(func_))[\(argStr)]"

        case .prime(let expr, _):
            return "\(convertExpression(expr))'"

        case .unchanged(let expr, _):
            return "\\textsc{unchanged} \(convertExpression(expr))"

        case .enabled(let expr, _):
            return "\\textsc{enabled} \(convertExpression(expr))"

        case .stuttering(let formula, let vars, _):
            return "[\(convertExpression(formula))]_{\(convertExpression(vars))}"

        case .action(let formula, let vars, _):
            return "$\\langle\\langle$\(convertExpression(formula))$\\rangle\\rangle$_{\(convertExpression(vars))}"

        case .always(let formula, _):
            return "$\\Box$\(convertExpression(formula))"

        case .eventually(let formula, _):
            return "$\\Diamond$\(convertExpression(formula))"

        case .leadsto(let left, let right, _):
            return "\(convertExpression(left)) $\\leadsto$ \(convertExpression(right))"

        case .weakFairnessLeadsto(let left, let right, _):
            return "\(convertExpression(left)) $-+\\rightarrow$ \(convertExpression(right))"

        case .weakFairness(let vars, let action, _):
            return "WF_{\(convertExpression(vars))}(\(convertExpression(action)))"

        case .strongFairness(let vars, let action, _):
            return "SF_{\(convertExpression(vars))}(\(convertExpression(action)))"

        case .except(let expr, let updates, _):
            let us = updates.map { "!\(convertExceptPath($0.path)) = \(convertExpression($0.value))" }
            return "[\(convertExpression(expr)) \\textsc{except} \(us.joined(separator: ", "))]"

        case .lambda(let params, let body, _):
            let ps = params.map(escapeLatex).joined(separator: ", ")
            return "\\textsc{lambda} \(ps): \(convertExpression(body))"
        }
    }

    // MARK: - Bound Variable Conversion

    private func convertBoundVariable(_ bv: BoundVariable) -> String {
        let name: String
        switch bv.pattern {
        case .single(let n):
            name = escapeLatex(n)
        case .tuple(let names):
            name = "$\\langle$\(names.map(escapeLatex).joined(separator: ", "))$\\rangle$"
        }

        if let domain = bv.domain {
            return "\(name) $\\in$ \(convertExpression(domain))"
        } else {
            return name
        }
    }

    private func convertExceptPath(_ path: [TLAExpression]) -> String {
        return path.map { convertExpression($0) }.joined(separator: "][")
    }

    // MARK: - Operator Conversion

    private func convertBinaryOp(_ op: TLABinaryOp) -> String {
        switch op {
        // Logical
        case .and: return "$\\land$"
        case .or: return "$\\lor$"
        case .implies: return "$\\Rightarrow$"
        case .iff: return "$\\Leftrightarrow$"
        // Comparison
        case .eq: return "="
        case .neq: return "$\\neq$"
        case .lt: return "<"
        case .le: return "$\\leq$"
        case .gt: return ">"
        case .ge: return "$\\geq$"
        // Arithmetic
        case .plus: return "+"
        case .minus: return "-"
        case .times: return "$\\times$"
        case .div: return "$\\div$"
        case .mod: return "\\%"
        case .exp: return "\\^{}"
        // Set
        case .elementOf: return "$\\in$"
        case .notElementOf: return "$\\notin$"
        case .subsetOf: return "$\\subseteq$"
        case .supersetOf: return "$\\supseteq$"
        case .properSubset: return "$\\subset$"
        case .properSuperset: return "$\\supset$"
        case .setUnion: return "$\\cup$"
        case .setIntersect: return "$\\cap$"
        case .setMinus: return "$\\setminus$"
        case .cartesian: return "$\\times$"
        // Sequence
        case .concat: return "$\\circ$"
        case .append: return "$\\circ$"
        // Function
        case .compose: return "$\\cdot$"
        case .functionOverride: return "@@"
        case .colonGreater: return ":>"
        // Relations (ordering)
        case .prec: return "$\\prec$"
        case .preceq: return "$\\preceq$"
        case .succ: return "$\\succ$"
        case .succeq: return "$\\succeq$"
        // Relations (similarity)
        case .sim: return "$\\sim$"
        case .simeq: return "$\\simeq$"
        case .approx: return "$\\approx$"
        case .cong: return "$\\cong$"
        case .doteq: return "$\\doteq$"
        case .propto: return "$\\propto$"
        case .asymp: return "$\\asymp$"
        // Square operators
        case .sqcap: return "$\\sqcap$"
        case .sqcup: return "$\\sqcup$"
        case .sqsubseteq: return "$\\sqsubseteq$"
        case .sqsupseteq: return "$\\sqsupseteq$"
        // Circle operators
        case .oplus: return "$\\oplus$"
        case .ominus: return "$\\ominus$"
        case .otimes: return "$\\otimes$"
        case .oslash: return "$\\oslash$"
        case .odot: return "$\\odot$"
        // Other mathematical operators
        case .cdot: return "$\\cdot$"
        case .bullet: return "$\\bullet$"
        case .star: return "$\\star$"
        case .bigcirc: return "$\\bigcirc$"
        case .wr: return "$\\wr$"
        }
    }

    private func convertUnaryOp(_ op: TLAUnaryOp) -> String {
        switch op {
        case .not: return "$\\lnot$"
        case .negative: return "-"
        case .domain: return "\\textsc{domain} "
        case .subset: return "\\textsc{subset} "
        case .union: return "\\textsc{union} "
        }
    }

    // MARK: - Helpers

    private func escapeLatex(_ text: String) -> String {
        var result = text
        result = result.replacingOccurrences(of: "\\", with: "\\textbackslash{}")
        result = result.replacingOccurrences(of: "{", with: "\\{")
        result = result.replacingOccurrences(of: "}", with: "\\}")
        result = result.replacingOccurrences(of: "_", with: "\\_")
        result = result.replacingOccurrences(of: "&", with: "\\&")
        result = result.replacingOccurrences(of: "%", with: "\\%")
        result = result.replacingOccurrences(of: "$", with: "\\$")
        result = result.replacingOccurrences(of: "#", with: "\\#")
        result = result.replacingOccurrences(of: "^", with: "\\^{}")
        result = result.replacingOccurrences(of: "~", with: "\\~{}")
        return result
    }
}

// MARK: - TLA+ LaTeX Style Package (minimal inline version)

extension LaTeXExporter {
    /// Generates a minimal tlatex.sty for users who don't have it installed
    static var tlatexStyle: String {
        """
        % Minimal TLA+ LaTeX style
        \\NeedsTeXFormat{LaTeX2e}
        \\ProvidesPackage{tlatex}[2024/01/01 Minimal TLA+ Style]

        \\RequirePackage{amsmath}
        \\RequirePackage{amssymb}
        \\RequirePackage{xcolor}

        % TLA module environment
        \\newenvironment{tla}{%
            \\par\\noindent%
            \\ttfamily%
        }{%
            \\par%
        }

        % Module delimiters
        \\newcommand{\\tlamodule}[1]{%
            \\noindent\\rule{\\textwidth}{1.5pt}\\\\
            \\textsc{module} \\textbf{#1}\\\\
            \\rule{\\textwidth}{0.5pt}%
        }

        \\newcommand{\\tlaendmodule}{%
            \\\\\\rule{\\textwidth}{1.5pt}%
        }

        % Theorem style
        \\newcommand{\\tlatheorem}[2]{%
            \\textsc{theorem} #1 $\\triangleq$ #2%
        }

        \\endinput
        """
    }
}
