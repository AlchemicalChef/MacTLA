import Foundation

/// Translates PlusCal algorithms to TLA+ specifications
final class PlusCalTranslator {

    struct TranslationResult {
        let tlaSpec: String
        let warnings: [String]
        let errors: [TranslationError]

        var isSuccess: Bool { errors.isEmpty }
    }

    struct TranslationError: Error, CustomStringConvertible {
        let message: String
        let line: Int
        let column: Int

        var description: String {
            "Line \(line), column \(column): \(message)"
        }
    }

    struct TranslationErrors: Error {
        let errors: [TranslationError]
    }

    // MARK: - PlusCal AST

    struct PlusCalAlgorithm {
        let name: String
        let variables: [VariableDecl]
        let procedures: [Procedure]
        let processes: [Process]
        let isFair: Bool
    }

    struct VariableDecl {
        let name: String
        let initialValue: String
    }

    struct Procedure {
        let name: String
        let parameters: [String]
        let variables: [VariableDecl]
        let body: [Statement]
    }

    struct Process {
        let name: String
        let id: String
        let isFair: Bool
        let variables: [VariableDecl]
        let body: [Statement]
    }

    indirect enum Statement {
        case assignment(variable: String, expression: String)
        case `if`(condition: String, thenBranch: [Statement], elseBranch: [Statement]?)
        case `while`(condition: String, body: [Statement])
        case either(branches: [[Statement]])
        case with(variable: String, set: String, body: [Statement])
        case await(condition: String)
        case skip
        case `return`
        case goto(label: String)
        case call(procedure: String, arguments: [String])
        case print(expression: String)
        case assert(condition: String)
        case labeled(label: String, statements: [Statement])
    }

    // MARK: - Translation

    func translate(_ source: String) -> TranslationResult {
        var warnings: [String] = []
        var errors: [TranslationError] = []

        // Extract PlusCal block from TLA+ module
        guard let plusCalBlock = extractPlusCalBlock(from: source) else {
            return TranslationResult(
                tlaSpec: source,
                warnings: ["No PlusCal algorithm found"],
                errors: []
            )
        }

        // Parse PlusCal
        let parseResult = parsePlusCal(plusCalBlock)

        switch parseResult {
        case .failure(let parseErrors):
            errors.append(contentsOf: parseErrors.errors)
            return TranslationResult(tlaSpec: source, warnings: warnings, errors: errors)

        case .success(let algorithm):
            // Generate TLA+
            let tlaCode = generateTLA(from: algorithm)

            // Add warnings for complex constructs
            if algorithm.processes.contains(where: { !$0.body.isEmpty }) {
                for process in algorithm.processes {
                    for stmt in process.body {
                        if case .call = stmt {
                            warnings.append("Procedure calls generate simplified TLA+")
                        }
                    }
                }
            }

            // Insert generated TLA+ after PlusCal block
            let result = insertGeneratedTLA(tlaCode, into: source, after: plusCalBlock)
            return TranslationResult(tlaSpec: result, warnings: warnings, errors: errors)
        }
    }

    private func extractPlusCalBlock(from source: String) -> String? {
        // Look for (*--algorithm ... end algorithm; *)
        let pattern = #"\(\*\s*--algorithm[\s\S]*?end\s+algorithm\s*;\s*\*\)"#

        guard let regex = try? NSRegularExpression(pattern: pattern, options: []),
              let match = regex.firstMatch(
                in: source,
                options: [],
                range: NSRange(source.startIndex..., in: source)
              ),
              let range = Range(match.range, in: source) else {
            return nil
        }

        return String(source[range])
    }

    private func parsePlusCal(_ block: String) -> Result<PlusCalAlgorithm, TranslationErrors> {
        var variables: [VariableDecl] = []
        var processes: [Process] = []
        var procedures: [Procedure] = []
        var algorithmName = "Algorithm"
        var isFair = false
        var mainBody: [Statement] = []

        let lines = block.components(separatedBy: "\n")
        var lineIndex = 0

        // Extract algorithm name and fairness
        for line in lines {
            let trimmed = line.trimmingCharacters(in: .whitespaces)

            if trimmed.contains("--algorithm") {
                if trimmed.contains("fair") {
                    isFair = true
                }
                if let regex = try? NSRegularExpression(pattern: #"algorithm\s+(\w+)"#, options: []) {
                    let nsString = trimmed as NSString
                    if let match = regex.firstMatch(in: trimmed, options: [], range: NSRange(location: 0, length: nsString.length)),
                       match.numberOfRanges >= 2 {
                        let nameRange = match.range(at: 1)
                        if nameRange.location != NSNotFound {
                            algorithmName = nsString.substring(with: nameRange)
                        }
                    }
                }
            }
        }

        // Second pass: parse variables, procedures, processes, and statements
        lineIndex = 0
        while lineIndex < lines.count {
            let line = lines[lineIndex]
            let trimmed = line.trimmingCharacters(in: .whitespaces)

            // Parse global variables
            if trimmed.hasPrefix("variables") || trimmed.hasPrefix("variable") {
                var varLine = trimmed
                // Handle multi-line variable declarations
                while !varLine.contains(";") && lineIndex + 1 < lines.count {
                    lineIndex += 1
                    varLine += " " + lines[lineIndex].trimmingCharacters(in: .whitespaces)
                }
                let varDecls = parseVariableDeclarations(varLine)
                variables.append(contentsOf: varDecls)
            }

            // Parse procedures
            if trimmed.hasPrefix("procedure") {
                let (procedure, newIndex) = parseProcedure(lines: lines, startIndex: lineIndex)
                if let proc = procedure {
                    procedures.append(proc)
                }
                lineIndex = newIndex
            }

            // Parse processes
            if trimmed.hasPrefix("process") || trimmed.hasPrefix("fair process") {
                let (process, newIndex) = parseProcess(lines: lines, startIndex: lineIndex)
                if let proc = process {
                    processes.append(proc)
                }
                lineIndex = newIndex
            }

            // Parse main body (begin ... end algorithm)
            if trimmed == "begin" {
                let (body, newIndex) = parseStatementBlock(lines: lines, startIndex: lineIndex + 1, endKeywords: ["end"])
                mainBody = body
                lineIndex = newIndex
            }

            lineIndex += 1
        }

        // If no processes defined, create a single implicit process from main body
        if processes.isEmpty && !mainBody.isEmpty {
            processes.append(Process(
                name: "Main",
                id: "self",
                isFair: false,
                variables: [],
                body: mainBody
            ))
        }

        let algorithm = PlusCalAlgorithm(
            name: algorithmName,
            variables: variables,
            procedures: procedures,
            processes: processes,
            isFair: isFair
        )

        return .success(algorithm)
    }

    private func parseProcedure(lines: [String], startIndex: Int) -> (Procedure?, Int) {
        var lineIndex = startIndex
        let line = lines[lineIndex]

        // Extract procedure name and parameters
        guard let regex = try? NSRegularExpression(pattern: #"procedure\s+(\w+)\s*\((.*?)\)"#, options: []),
              let match = regex.firstMatch(in: line, options: [], range: NSRange(location: 0, length: line.utf16.count)) else {
            return (nil, lineIndex)
        }

        let nsLine = line as NSString
        let name = nsLine.substring(with: match.range(at: 1))
        let paramsStr = match.numberOfRanges > 2 ? nsLine.substring(with: match.range(at: 2)) : ""
        let parameters = paramsStr.components(separatedBy: ",").map { $0.trimmingCharacters(in: .whitespaces) }.filter { !$0.isEmpty }

        var localVars: [VariableDecl] = []
        var body: [Statement] = []

        lineIndex += 1
        while lineIndex < lines.count {
            let trimmed = lines[lineIndex].trimmingCharacters(in: .whitespaces)

            if trimmed.hasPrefix("variables") || trimmed.hasPrefix("variable") {
                localVars = parseVariableDeclarations(trimmed)
            } else if trimmed == "begin" {
                let (stmts, newIndex) = parseStatementBlock(lines: lines, startIndex: lineIndex + 1, endKeywords: ["end procedure"])
                body = stmts
                lineIndex = newIndex
                break
            } else if trimmed.hasPrefix("end procedure") {
                break
            }

            lineIndex += 1
        }

        return (Procedure(name: name, parameters: parameters, variables: localVars, body: body), lineIndex)
    }

    private func parseProcess(lines: [String], startIndex: Int) -> (Process?, Int) {
        var lineIndex = startIndex
        let line = lines[lineIndex]

        let isFair = line.contains("fair process")
        let pattern = isFair ? #"fair\s+process\s+(\w+)\s*(?:=|\\in)\s*(.+)"# : #"process\s+(\w+)\s*(?:=|\\in)\s*(.+)"#

        guard let regex = try? NSRegularExpression(pattern: pattern, options: []),
              let match = regex.firstMatch(in: line, options: [], range: NSRange(location: 0, length: line.utf16.count)) else {
            return (nil, lineIndex)
        }

        let nsLine = line as NSString
        let name = nsLine.substring(with: match.range(at: 1))
        var id = nsLine.substring(with: match.range(at: 2)).trimmingCharacters(in: .whitespaces)
        // Remove trailing "do" if present
        if id.hasSuffix(" do") {
            let trimmedId = String(id.dropLast(3)).trimmingCharacters(in: .whitespaces)
            // Only use trimmed result if non-empty
            if !trimmedId.isEmpty {
                id = trimmedId
            }
        }
        // Ensure id is never empty - use process name as fallback
        if id.isEmpty {
            id = name
        }

        var localVars: [VariableDecl] = []
        var body: [Statement] = []

        lineIndex += 1
        while lineIndex < lines.count {
            let trimmed = lines[lineIndex].trimmingCharacters(in: .whitespaces)

            if trimmed.hasPrefix("variables") || trimmed.hasPrefix("variable") {
                localVars = parseVariableDeclarations(trimmed)
            } else if trimmed == "begin" {
                let (stmts, newIndex) = parseStatementBlock(lines: lines, startIndex: lineIndex + 1, endKeywords: ["end process"])
                body = stmts
                lineIndex = newIndex
                break
            } else if trimmed.hasPrefix("end process") {
                break
            }

            lineIndex += 1
        }

        return (Process(name: name, id: id, isFair: isFair, variables: localVars, body: body), lineIndex)
    }

    private func parseStatementBlock(lines: [String], startIndex: Int, endKeywords: [String]) -> ([Statement], Int) {
        var statements: [Statement] = []
        var lineIndex = startIndex

        while lineIndex < lines.count {
            let line = lines[lineIndex]
            let trimmed = line.trimmingCharacters(in: .whitespaces)

            // Check for end keywords
            for keyword in endKeywords {
                if trimmed.hasPrefix(keyword) || trimmed == keyword {
                    return (statements, lineIndex)
                }
            }

            // Skip empty lines and comments
            if trimmed.isEmpty || trimmed.hasPrefix("\\*") {
                lineIndex += 1
                continue
            }

            // Parse labeled statement
            if let labelMatch = try? NSRegularExpression(pattern: #"^(\w+):\s*(.*)$"#, options: []),
               let match = labelMatch.firstMatch(in: trimmed, options: [], range: NSRange(location: 0, length: trimmed.utf16.count)) {
                let nsLine = trimmed as NSString
                let label = nsLine.substring(with: match.range(at: 1))
                let rest = nsLine.substring(with: match.range(at: 2)).trimmingCharacters(in: .whitespaces)

                // Parse statements following the label
                var labeledStmts: [Statement] = []
                if !rest.isEmpty {
                    if let stmt = parseStatement(rest) {
                        labeledStmts.append(stmt)
                    }
                }

                // Continue parsing until next label or end
                lineIndex += 1
                while lineIndex < lines.count {
                    let nextLine = lines[lineIndex].trimmingCharacters(in: .whitespaces)

                    // Check for end or next label
                    for keyword in endKeywords {
                        if nextLine.hasPrefix(keyword) {
                            statements.append(.labeled(label: label, statements: labeledStmts))
                            return (statements, lineIndex)
                        }
                    }

                    // Check for next label
                    if let _ = try? NSRegularExpression(pattern: #"^(\w+):\s*"#, options: []).firstMatch(in: nextLine, options: [], range: NSRange(location: 0, length: nextLine.utf16.count)) {
                        statements.append(.labeled(label: label, statements: labeledStmts))
                        break
                    }

                    if !nextLine.isEmpty && !nextLine.hasPrefix("\\*") {
                        if let stmt = parseStatement(nextLine) {
                            labeledStmts.append(stmt)
                        }
                    }

                    lineIndex += 1
                }

                if lineIndex >= lines.count {
                    statements.append(.labeled(label: label, statements: labeledStmts))
                }
                continue
            }

            // Parse regular statement
            if let stmt = parseStatement(trimmed) {
                statements.append(stmt)
            }

            lineIndex += 1
        }

        return (statements, lineIndex)
    }

    private func parseStatement(_ line: String) -> Statement? {
        let trimmed = line.trimmingCharacters(in: .whitespaces)
            .trimmingCharacters(in: CharacterSet(charactersIn: ";"))

        // Skip
        if trimmed == "skip" {
            return .skip
        }

        // Return
        if trimmed == "return" {
            return .return
        }

        // Goto
        if trimmed.hasPrefix("goto") {
            let label = trimmed.replacingOccurrences(of: "goto", with: "").trimmingCharacters(in: .whitespaces)
            return .goto(label: label)
        }

        // Print
        if trimmed.hasPrefix("print") {
            let expr = trimmed.replacingOccurrences(of: "print", with: "").trimmingCharacters(in: .whitespaces)
            return .print(expression: expr)
        }

        // Assert
        if trimmed.hasPrefix("assert") {
            let cond = trimmed.replacingOccurrences(of: "assert", with: "").trimmingCharacters(in: .whitespaces)
            return .assert(condition: cond)
        }

        // Await
        if trimmed.hasPrefix("await") {
            let cond = trimmed.replacingOccurrences(of: "await", with: "").trimmingCharacters(in: .whitespaces)
            return .await(condition: cond)
        }

        // Call
        if trimmed.hasPrefix("call") {
            let rest = trimmed.replacingOccurrences(of: "call", with: "").trimmingCharacters(in: .whitespaces)
            if let parenIndex = rest.firstIndex(of: "("),
               let endIndex = rest.lastIndex(of: ")") {
                let procName = String(rest[..<parenIndex]).trimmingCharacters(in: .whitespaces)
                let argsStr = String(rest[rest.index(after: parenIndex)..<endIndex])
                let args = argsStr.components(separatedBy: ",").map { $0.trimmingCharacters(in: .whitespaces) }
                return .call(procedure: procName, arguments: args)
            }
        }

        // If statement (simplified - single line)
        if trimmed.hasPrefix("if ") || trimmed == "if" {
            // Extract condition between "if" and "then"
            if let thenRange = trimmed.range(of: " then"), trimmed.count > 3 {
                let startIndex = trimmed.index(trimmed.startIndex, offsetBy: 3)
                let cond = String(trimmed[startIndex..<thenRange.lowerBound])
                    .trimmingCharacters(in: .whitespaces)
                return .if(condition: cond, thenBranch: [], elseBranch: nil)
            } else {
                // Bare "if" without condition - return empty condition
                return .if(condition: "", thenBranch: [], elseBranch: nil)
            }
        }

        // While statement (simplified)
        if trimmed.hasPrefix("while ") || trimmed == "while" {
            if let doRange = trimmed.range(of: " do"), trimmed.count > 6 {
                let startIndex = trimmed.index(trimmed.startIndex, offsetBy: 6)
                let cond = String(trimmed[startIndex..<doRange.lowerBound])
                    .trimmingCharacters(in: .whitespaces)
                return .while(condition: cond, body: [])
            } else {
                // Bare "while" without condition - return empty condition
                return .while(condition: "", body: [])
            }
        }

        // Either statement
        if trimmed == "either" {
            return .either(branches: [[]])
        }

        // With statement
        if trimmed.hasPrefix("with") {
            if let regex = try? NSRegularExpression(pattern: #"with\s+(\w+)\s*\\in\s*(.+?)\s+do"#, options: []),
               let match = regex.firstMatch(in: trimmed, options: [], range: NSRange(location: 0, length: trimmed.utf16.count)) {
                let nsLine = trimmed as NSString
                let varName = nsLine.substring(with: match.range(at: 1))
                let setExpr = nsLine.substring(with: match.range(at: 2))
                return .with(variable: varName, set: setExpr, body: [])
            }
        }

        // Assignment (must be last to avoid matching other statements)
        if trimmed.contains(":=") {
            let parts = trimmed.components(separatedBy: ":=")
            if parts.count == 2 {
                let varName = parts[0].trimmingCharacters(in: .whitespaces)
                let expr = parts[1].trimmingCharacters(in: .whitespaces)
                return .assignment(variable: varName, expression: expr)
            }
        }

        return nil
    }

    private func parseVariableDeclarations(_ line: String) -> [VariableDecl] {
        var declarations: [VariableDecl] = []

        // Remove "variables" or "variable" prefix
        var content = line
        if let range = content.range(of: "variables") {
            content = String(content[range.upperBound...])
        } else if let range = content.range(of: "variable") {
            content = String(content[range.upperBound...])
        }

        // Split by comma and parse each declaration
        let parts = content.components(separatedBy: ",")
        for part in parts {
            let trimmed = part.trimmingCharacters(in: .whitespaces)
                .replacingOccurrences(of: ";", with: "")

            if let equalsRange = trimmed.range(of: "=") {
                let name = trimmed[..<equalsRange.lowerBound].trimmingCharacters(in: .whitespaces)
                let value = trimmed[equalsRange.upperBound...].trimmingCharacters(in: .whitespaces)
                declarations.append(VariableDecl(name: name, initialValue: value))
            } else if !trimmed.isEmpty {
                declarations.append(VariableDecl(name: trimmed, initialValue: ""))
            }
        }

        return declarations
    }

    private func generateTLA(from algorithm: PlusCalAlgorithm) -> String {
        var output = ""

        // Collect all labels for pc values
        var allLabels: [(process: String, label: String)] = []
        for process in algorithm.processes {
            let labels = extractLabels(from: process.body)
            if labels.isEmpty {
                allLabels.append((process.name, "\(process.name)_start"))
                allLabels.append((process.name, "\(process.name)_done"))
            } else {
                for label in labels {
                    allLabels.append((process.name, label))
                }
                allLabels.append((process.name, "Done"))
            }
        }

        // Collect all local variables from processes
        var localVars: [String] = []
        for process in algorithm.processes {
            for v in process.variables {
                if !localVars.contains(v.name) {
                    localVars.append(v.name)
                }
            }
        }

        // Add stack variable if there are procedures
        let hasProcedures = !algorithm.procedures.isEmpty
        var allVars = algorithm.variables.map(\.name) + localVars + ["pc"]
        if hasProcedures {
            allVars.append("stack")
        }

        if algorithm.processes.count > 1 {
            // For multiple processes, need ProcSet
            output += "ProcSet == {"
            output += algorithm.processes.map { $0.id }.joined(separator: ", ")
            output += "}\n\n"
        }
        output += "vars == <<\(allVars.joined(separator: ", "))>>\n\n"

        // Generate Init
        output += "Init ==\n"
        for variable in algorithm.variables {
            if !variable.initialValue.isEmpty {
                output += "    /\\ \(variable.name) = \(variable.initialValue)\n"
            }
        }
        for variable in localVars {
            output += "    /\\ \(variable) = {}\n" // Default initialization
        }
        // Initialize stack if we have procedures
        if hasProcedures {
            if algorithm.processes.count > 1 {
                output += "    /\\ stack = [self \\in ProcSet |-> <<>>]\n"
            } else {
                output += "    /\\ stack = <<>>\n"
            }
        }

        // Initialize pc
        if algorithm.processes.count > 1 {
            output += "    /\\ pc = [self \\in ProcSet |-> "
            let firstLabels = algorithm.processes.map { process -> String in
                let labels = extractLabels(from: process.body)
                return labels.first ?? "\(process.name)_start"
            }
            if Set(firstLabels).count == 1 {
                output += "\"\(firstLabels[0])\"]\n"
            } else {
                output += "CASE\n"
                for process in algorithm.processes {
                    let labels = extractLabels(from: process.body)
                    let firstLabel = labels.first ?? "\(process.name)_start"
                    output += "        [] self = \(process.id) -> \"\(firstLabel)\"\n"
                }
                output += "    ]\n"
            }
        } else if !algorithm.processes.isEmpty {
            let process = algorithm.processes[0]
            let labels = extractLabels(from: process.body)
            let firstLabel = labels.first ?? "\(process.name)_start"
            output += "    /\\ pc = \"\(firstLabel)\"\n"
        } else {
            output += "    /\\ pc = \"start\"\n"
        }
        output += "\n"

        // Generate actions for each label
        for process in algorithm.processes {
            let processVars = process.variables.map(\.name)
            let otherVars = algorithm.variables.map(\.name).filter { !processVars.contains($0) }

            if process.body.isEmpty {
                // Empty process - generate skeleton
                output += "\(process.name)Action ==\n"
                if algorithm.processes.count > 1 {
                    output += "    /\\ pc[self] = \"\(process.name)_start\"\n"
                    output += "    /\\ pc' = [pc EXCEPT ![self] = \"Done\"]\n"
                } else {
                    output += "    /\\ pc = \"\(process.name)_start\"\n"
                    output += "    /\\ pc' = \"Done\"\n"
                }
                output += "    /\\ UNCHANGED <<\(allVars.filter { $0 != "pc" }.joined(separator: ", "))>>\n\n"
            } else {
                // Generate actions for each labeled block
                for stmt in process.body {
                    if case .labeled(let label, let stmts) = stmt {
                        output += generateLabelAction(
                            label: label,
                            statements: stmts,
                            process: process,
                            algorithm: algorithm,
                            allVars: allVars
                        )
                    }
                }
            }
        }

        // Generate procedure actions
        for procedure in algorithm.procedures {
            output += "\\* Procedure \(procedure.name)\n"

            // Generate action for procedure entry
            output += "\(procedure.name)_startAction ==\n"
            if algorithm.processes.count > 1 {
                output += "    /\\ pc[self] = \"\(procedure.name)_start\"\n"
            } else {
                output += "    /\\ pc = \"\(procedure.name)_start\"\n"
            }

            // Generate actions for procedure body labels
            let labels = extractLabels(from: procedure.body)
            if labels.isEmpty {
                // No labels - just execute body and return
                var modifiedVars: Set<String> = []
                for stmt in procedure.body {
                    if case .assignment(let v, let e) = stmt {
                        output += "    /\\ \(v)' = \(e)\n"
                        modifiedVars.insert(v)
                    }
                }

                // Return via stack
                if algorithm.processes.count > 1 {
                    output += "    /\\ stack[self] # <<>>\n"
                    output += "    /\\ pc' = [pc EXCEPT ![self] = Head(stack[self])[2]]\n"
                    output += "    /\\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]\n"
                } else {
                    output += "    /\\ stack # <<>>\n"
                    output += "    /\\ pc' = Head(stack)[2]\n"
                    output += "    /\\ stack' = Tail(stack)\n"
                }
                let unchangedVars = allVars.filter { $0 != "pc" && $0 != "stack" && !modifiedVars.contains($0) }
                if !unchangedVars.isEmpty {
                    output += "    /\\ UNCHANGED <<\(unchangedVars.joined(separator: ", "))>>\n"
                }
            } else {
                // Has labels - set pc to first label
                let firstLabel = labels[0]
                if algorithm.processes.count > 1 {
                    output += "    /\\ pc' = [pc EXCEPT ![self] = \"\(firstLabel)\"]\n"
                } else {
                    output += "    /\\ pc' = \"\(firstLabel)\"\n"
                }
                let unchangedVars = allVars.filter { $0 != "pc" }
                if !unchangedVars.isEmpty {
                    output += "    /\\ UNCHANGED <<\(unchangedVars.joined(separator: ", "))>>\n"
                }

                // Generate action for each label in procedure
                for stmt in procedure.body {
                    if case .labeled(let label, let stmts) = stmt {
                        output += "\n\(label)Action ==\n"
                        if algorithm.processes.count > 1 {
                            output += "    /\\ pc[self] = \"\(label)\"\n"
                        } else {
                            output += "    /\\ pc = \"\(label)\"\n"
                        }

                        var labelModified: Set<String> = []
                        for s in stmts {
                            if case .assignment(let v, let e) = s {
                                output += "    /\\ \(v)' = \(e)\n"
                                labelModified.insert(v)
                            }
                        }

                        // Find next label or return
                        let currentIdx = labels.firstIndex(of: label) ?? 0
                        if currentIdx + 1 < labels.count {
                            let nextLabel = labels[currentIdx + 1]
                            if algorithm.processes.count > 1 {
                                output += "    /\\ pc' = [pc EXCEPT ![self] = \"\(nextLabel)\"]\n"
                            } else {
                                output += "    /\\ pc' = \"\(nextLabel)\"\n"
                            }
                        } else {
                            // Last label - return
                            if algorithm.processes.count > 1 {
                                output += "    /\\ stack[self] # <<>>\n"
                                output += "    /\\ pc' = [pc EXCEPT ![self] = Head(stack[self])[2]]\n"
                                output += "    /\\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]\n"
                            } else {
                                output += "    /\\ stack # <<>>\n"
                                output += "    /\\ pc' = Head(stack)[2]\n"
                                output += "    /\\ stack' = Tail(stack)\n"
                            }
                            labelModified.insert("stack")
                        }

                        let unchangedInLabel = allVars.filter { $0 != "pc" && !labelModified.contains($0) }
                        if !unchangedInLabel.isEmpty {
                            output += "    /\\ UNCHANGED <<\(unchangedInLabel.joined(separator: ", "))>>\n"
                        }
                    }
                }
            }
            output += "\n"
        }

        // Generate Next
        output += "Next ==\n"
        if algorithm.processes.isEmpty {
            output += "    UNCHANGED vars\n"
        } else {
            var actions: [String] = []
            for process in algorithm.processes {
                if process.body.isEmpty {
                    actions.append("\(process.name)Action")
                } else {
                    for stmt in process.body {
                        if case .labeled(let label, _) = stmt {
                            actions.append("\(label)Action")
                        }
                    }
                }
            }
            if actions.isEmpty {
                actions = algorithm.processes.map { "\($0.name)Action" }
            }
            output += "    \\/ " + actions.joined(separator: "\n    \\/ ") + "\n"
            output += "    \\/ (* Disjunct to prevent deadlock *)\n"
            if algorithm.processes.count > 1 {
                output += "       /\\ \\A self \\in ProcSet: pc[self] = \"Done\"\n"
            } else {
                output += "       /\\ pc = \"Done\"\n"
            }
            output += "       /\\ UNCHANGED vars\n"
        }
        output += "\n"

        // Generate Spec with fairness
        output += "Spec == Init /\\ [][Next]_vars"

        // Add fairness constraints
        var fairnessConstraints: [String] = []

        // Algorithm-level fairness
        if algorithm.isFair {
            fairnessConstraints.append("WF_vars(Next)")
        }

        // Process-level fairness
        for process in algorithm.processes {
            if process.isFair {
                // Get all actions for this process
                let labels = extractLabels(from: process.body)
                if labels.isEmpty {
                    // Single action process
                    fairnessConstraints.append("WF_vars(\(process.name)Action)")
                } else {
                    // Multiple actions - add fairness for each
                    for label in labels {
                        fairnessConstraints.append("WF_vars(\(label)Action)")
                    }
                }
            }
        }

        if !fairnessConstraints.isEmpty {
            output += "\n    /\\ " + fairnessConstraints.joined(separator: "\n    /\\ ")
        }
        output += "\n\n"

        // Generate Termination
        if !algorithm.processes.isEmpty {
            if algorithm.processes.count > 1 {
                output += "Termination == <>(\\A self \\in ProcSet: pc[self] = \"Done\")\n"
            } else {
                output += "Termination == <>(pc = \"Done\")\n"
            }
        }

        return output
    }

    private func extractLabels(from statements: [Statement]) -> [String] {
        var labels: [String] = []
        for stmt in statements {
            if case .labeled(let label, _) = stmt {
                labels.append(label)
            }
        }
        return labels
    }

    private func generateLabelAction(
        label: String,
        statements: [Statement],
        process: Process,
        algorithm: PlusCalAlgorithm,
        allVars: [String]
    ) -> String {
        var output = "\(label)Action ==\n"

        // PC guard
        if algorithm.processes.count > 1 {
            output += "    /\\ pc[self] = \"\(label)\"\n"
        } else {
            output += "    /\\ pc = \"\(label)\"\n"
        }

        // Find next label
        let labels = extractLabels(from: process.body)
        let currentIndex = labels.firstIndex(of: label) ?? 0
        let nextLabel = currentIndex + 1 < labels.count ? labels[currentIndex + 1] : "Done"

        // Generate statement effects
        var modifiedVars: Set<String> = []
        var conditions: [String] = []

        for stmt in statements {
            switch stmt {
            case .assignment(let variable, let expression):
                output += "    /\\ \(variable)' = \(expression)\n"
                modifiedVars.insert(variable)

            case .await(let condition):
                conditions.append(condition)

            case .assert(let condition):
                output += "    /\\ \(condition) \\* Assert\n"

            case .if(let condition, _, _):
                output += "    /\\ \(condition) \\* If condition\n"

            case .while(let condition, _):
                output += "    /\\ \(condition) \\* While condition\n"

            case .with(let variable, let setExpr, let body):
                // Generate existential quantification with body
                output += "    /\\ \\E \(variable) \\in \(setExpr):\n"
                if body.isEmpty {
                    output += "        TRUE\n"
                } else {
                    output += "        ("
                    // Generate body statements as conjunction
                    var bodyParts: [String] = []
                    for bodyStmt in body {
                        if case .assignment(let v, let e) = bodyStmt {
                            bodyParts.append("\(v)' = \(e)")
                            modifiedVars.insert(v)
                        }
                    }
                    output += bodyParts.joined(separator: " /\\ ")
                    output += ")\n"
                }

            case .goto(let targetLabel):
                // Override next label for goto
                if algorithm.processes.count > 1 {
                    output += "    /\\ pc' = [pc EXCEPT ![self] = \"\(targetLabel)\"]\n"
                } else {
                    output += "    /\\ pc' = \"\(targetLabel)\"\n"
                }
                output += "    /\\ UNCHANGED <<\(allVars.filter { $0 != "pc" && !modifiedVars.contains($0) }.joined(separator: ", "))>>\n\n"
                return output

            case .call(let procedure, let arguments):
                // Generate procedure call with stack push
                let returnLabel = nextLabel
                if algorithm.processes.count > 1 {
                    output += "    /\\ stack' = [stack EXCEPT ![self] = Append(stack[self], <<pc[self], \"\(returnLabel)\">>)]\n"
                    output += "    /\\ pc' = [pc EXCEPT ![self] = \"\(procedure)_start\"]\n"
                } else {
                    output += "    /\\ stack' = Append(stack, <<pc, \"\(returnLabel)\">>)\n"
                    output += "    /\\ pc' = \"\(procedure)_start\"\n"
                }
                // Store arguments if any
                for (i, arg) in arguments.enumerated() {
                    if i < algorithm.procedures.first(where: { $0.name == procedure })?.parameters.count ?? 0 {
                        let param = algorithm.procedures.first(where: { $0.name == procedure })?.parameters[i] ?? "arg\(i)"
                        output += "    /\\ \(param)' = \(arg)\n"
                        modifiedVars.insert(param)
                    }
                }
                modifiedVars.insert("stack")
                // Don't continue with normal pc update - call handles it
                output += "    /\\ UNCHANGED <<\(allVars.filter { $0 != "pc" && $0 != "stack" && !modifiedVars.contains($0) }.joined(separator: ", "))>>\n\n"
                return output

            case .return:
                // Generate return with stack pop
                if algorithm.processes.count > 1 {
                    output += "    /\\ stack[self] # <<>>\n"
                    output += "    /\\ pc' = [pc EXCEPT ![self] = Head(stack[self])[2]]\n"
                    output += "    /\\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]\n"
                } else {
                    output += "    /\\ stack # <<>>\n"
                    output += "    /\\ pc' = Head(stack)[2]\n"
                    output += "    /\\ stack' = Tail(stack)\n"
                }
                modifiedVars.insert("stack")
                output += "    /\\ UNCHANGED <<\(allVars.filter { $0 != "pc" && $0 != "stack" && !modifiedVars.contains($0) }.joined(separator: ", "))>>\n\n"
                return output

            case .print(let expression):
                // Print is a side effect - just document it
                output += "    \\* Print: \(expression)\n"

            case .skip, .either, .labeled:
                break
            }
        }

        // Add await conditions
        for cond in conditions {
            output += "    /\\ \(cond)\n"
        }

        // Update PC
        if algorithm.processes.count > 1 {
            output += "    /\\ pc' = [pc EXCEPT ![self] = \"\(nextLabel)\"]\n"
        } else {
            output += "    /\\ pc' = \"\(nextLabel)\"\n"
        }

        // UNCHANGED for unmodified variables
        let unchangedVars = allVars.filter { $0 != "pc" && !modifiedVars.contains($0) }
        if !unchangedVars.isEmpty {
            output += "    /\\ UNCHANGED <<\(unchangedVars.joined(separator: ", "))>>\n"
        }

        output += "\n"
        return output
    }

    private func insertGeneratedTLA(_ tlaCode: String, into source: String, after plusCalBlock: String) -> String {
        // Find the end of the PlusCal block and insert generated TLA+ after it
        guard let range = source.range(of: plusCalBlock) else {
            return source
        }

        let beforeBlock = source[..<range.lowerBound]
        let afterBlock = source[range.upperBound...]

        // Look for existing translation marker
        let translationMarker = "\\* BEGIN TRANSLATION"
        let endMarker = "\\* END TRANSLATION"

        var result = String(beforeBlock) + plusCalBlock + "\n\n"

        // Remove old translation if exists
        if let startRange = afterBlock.range(of: translationMarker),
           let endRange = afterBlock.range(of: endMarker) {
            result += String(afterBlock[..<startRange.lowerBound])
            result += translationMarker + "\n"
            result += tlaCode
            result += endMarker + "\n"
            result += String(afterBlock[endRange.upperBound...])
        } else {
            result += translationMarker + "\n"
            result += tlaCode
            result += endMarker + "\n"
            result += String(afterBlock)
        }

        return result
    }
}

