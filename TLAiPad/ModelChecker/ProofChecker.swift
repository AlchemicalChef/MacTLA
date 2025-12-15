import Foundation

/// TLAPS-style proof checker for TLA+ theorems
/// Note: Uses actor isolation to prevent race conditions in async proof checking
actor ProofChecker {

    // MARK: - Proof Structures

    /// A proof obligation that needs to be discharged
    struct ProofObligation: Identifiable {
        let id: UUID
        let name: String
        let goal: TLAExpression
        let hypotheses: [TLAExpression]
        let status: ProofStatus
        let location: SourceLocation

        init(
            id: UUID = UUID(),
            name: String,
            goal: TLAExpression,
            hypotheses: [TLAExpression] = [],
            status: ProofStatus = .pending,
            location: SourceLocation = .unknown
        ) {
            self.id = id
            self.name = name
            self.goal = goal
            self.hypotheses = hypotheses
            self.status = status
            self.location = location
        }
    }

    enum ProofStatus {
        case pending      // Not yet checked
        case checking     // Currently being verified
        case proved       // Successfully proved
        case failed       // Proof failed
        case trivial      // Trivially true
        case byDefinition // True by definition expansion
        case assumed      // Assumed without proof
    }

    /// Result of proof checking
    struct ProofResult {
        let theorem: String
        let obligations: [ProofObligation]
        let overallStatus: ProofStatus
        let messages: [ProofMessage]
        let duration: TimeInterval
    }

    struct ProofMessage {
        enum Level { case info, warning, error }
        let level: Level
        let message: String
        let location: SourceLocation?
    }

    // MARK: - Proof Checking

    private let interpreter: TLAInterpreter
    private var obligations: [ProofObligation] = []
    private var messages: [ProofMessage] = []

    init() {
        self.interpreter = TLAInterpreter()
    }

    /// Check all theorems in a module
    func checkModule(_ module: TLAModule) async -> [ProofResult] {
        var results: [ProofResult] = []

        for decl in module.declarations {
            if case .theorem(let theorem) = decl {
                let result = await checkTheorem(theorem, in: module)
                results.append(result)
            }
        }

        return results
    }

    /// Check a single theorem
    func checkTheorem(_ theorem: TheoremDeclaration, in module: TLAModule) async -> ProofResult {
        let startTime = Date()
        obligations = []
        messages = []

        let name = theorem.name ?? "Anonymous"

        // Create the main proof obligation
        let mainObligation = ProofObligation(
            name: name,
            goal: theorem.body,
            hypotheses: collectAssumptions(from: module),
            status: .pending,
            location: theorem.location
        )
        obligations.append(mainObligation)

        // Process the proof
        if let proof = theorem.proof {
            await processProof(proof, for: mainObligation, in: module)
        } else {
            // No proof provided - mark as assumed
            obligations[0] = ProofObligation(
                id: mainObligation.id,
                name: mainObligation.name,
                goal: mainObligation.goal,
                hypotheses: mainObligation.hypotheses,
                status: .assumed,
                location: mainObligation.location
            )
            messages.append(ProofMessage(
                level: .warning,
                message: "Theorem '\(name)' has no proof - assumed",
                location: theorem.location
            ))
        }

        // Calculate overall status
        let overallStatus = calculateOverallStatus()

        return ProofResult(
            theorem: name,
            obligations: obligations,
            overallStatus: overallStatus,
            messages: messages,
            duration: Date().timeIntervalSince(startTime)
        )
    }

    private let maxRecursionDepth = 100

    private func processProof(_ proof: TLAProof, for obligation: ProofObligation, in module: TLAModule, depth: Int = 0) async {
        // Prevent stack overflow from deeply nested proofs
        guard depth < maxRecursionDepth else {
            updateObligation(obligation.id, status: .failed)
            messages.append(ProofMessage(
                level: .error,
                message: "Proof nesting too deep (>\(maxRecursionDepth) levels)",
                location: obligation.location
            ))
            return
        }

        switch proof {
        case .by(let facts, let defs, _):
            // Simple proof by facts and definitions
            await checkByProof(obligation: obligation, facts: facts, definitions: defs, in: module)

        case .obvious(_):
            // OBVIOUS - try to prove automatically
            await checkObvious(obligation: obligation, in: module)

        case .omitted(_):
            // OMITTED - skip this proof
            updateObligation(obligation.id, status: .assumed)
            messages.append(ProofMessage(
                level: .warning,
                message: "Proof step '\(obligation.name)' was OMITTED",
                location: obligation.location
            ))

        case .steps(let steps, _):
            // Structured proof with steps
            await checkSteppedProof(obligation: obligation, steps: steps, in: module, depth: depth)
        }
    }

    private func checkByProof(
        obligation: ProofObligation,
        facts: [ProofFact],
        definitions: [String],
        in module: TLAModule
    ) async {
        // Collect fact expressions
        var factExprs: [TLAExpression] = obligation.hypotheses

        for fact in facts {
            switch fact.kind {
            case .identifier(let name):
                if let factExpr = findFact(named: name, in: module) {
                    factExprs.append(factExpr)
                }
            case .stepRef:
                // Step references refer to previous proof steps - skip for now
                break
            }
        }

        // Try to prove the goal using the facts
        let proved = await attemptProof(goal: obligation.goal, using: factExprs, definitions: definitions, in: module)

        updateObligation(obligation.id, status: proved ? .proved : .failed)

        if !proved {
            messages.append(ProofMessage(
                level: .error,
                message: "Could not prove '\(obligation.name)' from given facts",
                location: obligation.location
            ))
        }
    }

    private func checkObvious(obligation: ProofObligation, in module: TLAModule) async {
        // Try common proof strategies

        // 1. Check if goal is trivially true
        if isTriviallyTrue(obligation.goal) {
            updateObligation(obligation.id, status: .trivial)
            return
        }

        // 2. Check if goal follows directly from hypotheses
        for hyp in obligation.hypotheses {
            if expressionsEqual(hyp, obligation.goal) {
                updateObligation(obligation.id, status: .proved)
                return
            }
        }

        // 3. Try simple propositional reasoning
        if await tryPropositionalProof(obligation: obligation, in: module) {
            updateObligation(obligation.id, status: .proved)
            return
        }

        // Could not prove automatically
        updateObligation(obligation.id, status: .failed)
        messages.append(ProofMessage(
            level: .error,
            message: "Could not prove '\(obligation.name)' automatically",
            location: obligation.location
        ))
    }

    private func checkSteppedProof(
        obligation: ProofObligation,
        steps: [TLAProofStep],
        in module: TLAModule,
        depth: Int
    ) async {
        var currentHypotheses = obligation.hypotheses

        for step in steps {
            let stepLabel = step.number.map { "Step \($0)" } ?? "Step"

            switch step.content {
            case .have(let expr, let proof):
                // HAVE introduces a new fact that must be proved
                let stepObligation = ProofObligation(
                    name: stepLabel,
                    goal: expr,
                    hypotheses: currentHypotheses,
                    status: .pending,
                    location: step.location
                )
                obligations.append(stepObligation)

                if let proof = proof {
                    await processProof(proof, for: stepObligation, in: module, depth: depth + 1)
                }

                currentHypotheses.append(expr)

            case .take(let vars):
                // TAKE introduces universally quantified variables
                let varNames = vars.map { $0.name }
                messages.append(ProofMessage(
                    level: .info,
                    message: "TAKE: \(varNames.joined(separator: ", "))",
                    location: step.location
                ))

            case .witness(let exprs, _):
                // WITNESS provides existential witnesses
                messages.append(ProofMessage(
                    level: .info,
                    message: "WITNESS: \(exprs.count) expression(s)",
                    location: step.location
                ))

            case .pick(let vars, let condition, _):
                // PICK introduces variables satisfying a condition
                currentHypotheses.append(condition)
                let varNames = vars.map { $0.name }
                messages.append(ProofMessage(
                    level: .info,
                    message: "PICK: \(varNames.joined(separator: ", "))",
                    location: step.location
                ))

            case .assertion(let expr, let proof):
                // Assertion introduces a new fact to prove
                let stepObligation = ProofObligation(
                    name: stepLabel,
                    goal: expr,
                    hypotheses: currentHypotheses,
                    status: .pending,
                    location: step.location
                )
                obligations.append(stepObligation)

                if let proof = proof {
                    await processProof(proof, for: stepObligation, in: module, depth: depth + 1)
                }

                currentHypotheses.append(expr)

            case .suffices(let assume, let prove, let proof):
                // SUFFICES changes the goal
                var newHypotheses = currentHypotheses
                if let assumeExpr = assume {
                    newHypotheses.append(assumeExpr)
                }
                let stepObligation = ProofObligation(
                    name: "Suffices",
                    goal: prove,
                    hypotheses: newHypotheses,
                    status: .pending,
                    location: step.location
                )
                obligations.append(stepObligation)

                if let proof = proof {
                    await processProof(proof, for: stepObligation, in: module, depth: depth + 1)
                }

            case .caseStep(let expr, let proof):
                // CASE proof by cases
                let caseObligation = ProofObligation(
                    name: "Case \(stepLabel)",
                    goal: obligation.goal,
                    hypotheses: currentHypotheses + [expr],
                    status: .pending,
                    location: step.location
                )
                obligations.append(caseObligation)

                if let proof = proof {
                    await processProof(proof, for: caseObligation, in: module, depth: depth + 1)
                }

            case .qed(let proof):
                // QED - final step proving the goal
                let qedObligation = ProofObligation(
                    name: "QED",
                    goal: obligation.goal,
                    hypotheses: currentHypotheses,
                    status: .pending,
                    location: step.location
                )
                obligations.append(qedObligation)

                if let proof = proof {
                    await processProof(proof, for: qedObligation, in: module, depth: depth + 1)
                }

            case .use, .hide, .define:
                // These modify the proof context but don't create obligations
                messages.append(ProofMessage(
                    level: .info,
                    message: "Context modification step",
                    location: step.location
                ))
            }
        }

        // Update main obligation status based on steps
        let stepsToCheck = Array(obligations.dropFirst())
        // Only consider it proved if there are actual steps AND all are proved
        let allStepsProved = !stepsToCheck.isEmpty && stepsToCheck.allSatisfy {
            $0.status == .proved || $0.status == .trivial || $0.status == .byDefinition
        }
        updateObligation(obligation.id, status: allStepsProved ? .proved : .failed)
    }

    // MARK: - Proof Helpers

    private func attemptProof(
        goal: TLAExpression,
        using facts: [TLAExpression],
        definitions: [String],
        in module: TLAModule
    ) async -> Bool {
        // Simple proof attempt - check if goal matches any fact
        for fact in facts {
            if expressionsEqual(fact, goal) {
                return true
            }
        }

        // Try to evaluate the goal with facts as context
        let env = TLAInterpreter.Environment.from(module: module)

        // Try to evaluate the goal
        do {
            let result = try interpreter.evaluate(goal, in: env)
            if case .boolean(true) = result {
                return true
            }
        } catch {
            // Evaluation failed - not provable this way
        }

        return false
    }

    private func tryPropositionalProof(obligation: ProofObligation, in module: TLAModule) async -> Bool {
        // Check common propositional patterns

        // P /\ Q => P
        // P /\ Q => Q
        // P => P \/ Q
        // etc.

        // For now, just try to evaluate
        let env = TLAInterpreter.Environment.from(module: module)

        do {
            let result = try interpreter.evaluate(obligation.goal, in: env)
            return result == .boolean(true)
        } catch {
            return false
        }
    }

    private func isTriviallyTrue(_ expr: TLAExpression) -> Bool {
        switch expr {
        case .boolean(true, _):
            return true
        case .binary(let left, .eq, let right, _):
            return expressionsEqual(left, right)
        default:
            return false
        }
    }

    private func expressionsEqual(_ lhs: TLAExpression, _ rhs: TLAExpression) -> Bool {
        // Structural equality check
        switch (lhs, rhs) {
        case (.identifier(let a, _), .identifier(let b, _)):
            return a == b
        case (.number(let a, _), .number(let b, _)):
            return a == b
        case (.string(let a, _), .string(let b, _)):
            return a == b
        case (.boolean(let a, _), .boolean(let b, _)):
            return a == b
        case (.binary(let l1, let op1, let r1, _), .binary(let l2, let op2, let r2, _)):
            return op1 == op2 && expressionsEqual(l1, l2) && expressionsEqual(r1, r2)
        default:
            return false
        }
    }

    private func collectAssumptions(from module: TLAModule) -> [TLAExpression] {
        var assumptions: [TLAExpression] = []
        for decl in module.declarations {
            if case .assumption(let assume) = decl {
                assumptions.append(assume.body)
            }
        }
        return assumptions
    }

    private func findFact(named name: String, in module: TLAModule) -> TLAExpression? {
        // Look for the fact in module declarations
        for decl in module.declarations {
            switch decl {
            case .theorem(let theorem) where theorem.name == name:
                return theorem.body
            case .assumption(let assume) where assume.name == name:
                return assume.body
            case .operatorDef(let def) where def.name == name:
                return def.body
            default:
                continue
            }
        }
        return nil
    }

    private func updateObligation(_ id: UUID, status: ProofStatus) {
        if let index = obligations.firstIndex(where: { $0.id == id }) {
            let old = obligations[index]
            obligations[index] = ProofObligation(
                id: old.id,
                name: old.name,
                goal: old.goal,
                hypotheses: old.hypotheses,
                status: status,
                location: old.location
            )
        }
    }

    private func calculateOverallStatus() -> ProofStatus {
        if obligations.isEmpty { return .pending }

        let hasFailures = obligations.contains { $0.status == .failed }
        let hasPending = obligations.contains { $0.status == .pending }
        let hasAssumed = obligations.contains { $0.status == .assumed }

        if hasFailures { return .failed }
        if hasPending { return .pending }
        if hasAssumed { return .assumed }
        return .proved
    }
}
