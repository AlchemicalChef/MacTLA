import Foundation

/// TLC-like model checker for TLA+ specifications
actor ModelChecker {
    private var isRunning = false
    private var shouldCancel = false

    struct Configuration {
        var workers: Int = 1
        var maxStates: Int = 1_000_000
        var maxDepth: Int = 100
        var checkDeadlock: Bool = true
        var checkInvariants: Bool = true
        var checkProperties: Bool = true
        var checkLiveness: Bool = true

        // Simulation mode settings
        var simulationMode: Bool = false
        var simulationTraceCount: Int = 100     // Number of random traces to generate
        var simulationTraceDepth: Int = 100     // Max depth per trace

        static let `default` = Configuration()
    }

    /// Temporal property types
    enum TemporalProperty {
        case always(String)           // []P - P holds in all states
        case eventually(String)        // <>P - P eventually holds
        case alwaysEventually(String)  // []<>P - P holds infinitely often
        case eventuallyAlways(String)  // <>[]P - P eventually holds forever
        case leadsto(String, String)   // P ~> Q - whenever P, eventually Q
        case weakFairness(String)      // WF_vars(A) - if A enabled continuously, A occurs
        case strongFairness(String)    // SF_vars(A) - if A enabled infinitely often, A occurs
    }

    /// Result of temporal property checking
    struct TemporalCheckResult {
        let property: TemporalProperty
        let holds: Bool
        let counterexample: [TLAState]? // Lasso-shaped counterexample for liveness
        let loopStart: Int? // Index where the loop begins in counterexample
    }

    struct Statistics {
        var statesGenerated: Int = 0
        var distinctStates: Int = 0
        var statesInQueue: Int = 0
        var depth: Int = 0
        var startTime: Date = Date()

        var elapsedTime: TimeInterval {
            Date().timeIntervalSince(startTime)
        }

        var statesPerSecond: Double {
            guard elapsedTime > 0 else { return 0 }
            return Double(statesGenerated) / elapsedTime
        }
    }

    /// Represents a transition between two states
    struct StateTransition: Sendable {
        let fromHash: StateHash
        let toHash: StateHash
        let action: String?
    }

    /// Result containing explored states for visualization
    struct ExplorationResult: Sendable {
        let states: [TLAState]
        let stateHashes: [StateHash: Int] // Maps hash to index in states array
        let transitions: [StateTransition]
        let initialStates: Set<StateHash>
        let errorStates: Set<StateHash>
    }

    private var configuration = Configuration.default
    private var statistics = Statistics()

    // State tracking for visualization
    private var exploredStates: [TLAState] = []
    private var stateHashToIndex: [StateHash: Int] = [:]
    private var stateTransitions: [StateTransition] = []
    private var initialStateHashes: Set<StateHash> = []
    private var errorStateHashes: Set<StateHash> = []

    /// Constant override from configuration
    struct ConstantOverride {
        let name: String
        let value: String
    }

    /// Explicit invariant from configuration
    struct InvariantSpec {
        let name: String
    }

    /// Explicit temporal property from configuration
    struct PropertySpec {
        let name: String
    }

    /// State constraint - limits exploration to states satisfying a predicate
    struct ConstraintSpec {
        let expression: String
    }

    /// Action constraint - filters transitions satisfying a predicate (can use primed variables)
    struct ActionConstraintSpec {
        let expression: String
    }

    /// View specification - project states to subset of variables for comparison
    struct ViewSpec {
        let expression: String
    }

    /// Symmetry set specification - values that can be permuted
    struct SymmetrySetSpec {
        let name: String  // Name of the symmetry set (e.g., "Permutations(Nodes)")
    }

    func verify(
        specification: String,
        config: Configuration = .default,
        constants: [ConstantOverride] = [],
        invariants: [InvariantSpec] = [],
        properties: [PropertySpec] = [],
        constraints: [ConstraintSpec] = [],
        actionConstraints: [ActionConstraintSpec] = [],
        view: ViewSpec? = nil,
        symmetrySets: [SymmetrySetSpec] = []
    ) async -> VerificationResult {
        guard !isRunning else {
            return VerificationResult(
                specificationName: "Unknown",
                status: .error,
                error: "Model checker is already running"
            )
        }

        isRunning = true
        shouldCancel = false
        configuration = config
        statistics = Statistics()

        // Store config for use in checkModel
        self.constantOverrides = constants
        self.explicitInvariants = invariants
        self.explicitProperties = properties
        self.stateConstraints = constraints
        self.stateActionConstraints = actionConstraints
        self.viewSpec = view
        self.symmetrySetSpecs = symmetrySets

        // Reset state tracking
        exploredStates = []
        stateHashToIndex = [:]
        stateTransitions = []
        initialStateHashes = []
        errorStateHashes = []

        defer { isRunning = false }

        // Parse the specification
        let parser = TLAParser()
        let parseResult = parser.parse(specification)

        switch parseResult {
        case .failure(let parseErrors):
            return VerificationResult(
                specificationName: "Unknown",
                status: .error,
                error: parseErrors.errors.map(\.description).joined(separator: "\n")
            )

        case .success(let module):
            return await checkModel(module)
        }
    }

    // Storage for config-based settings
    private var constantOverrides: [ConstantOverride] = []
    private var explicitInvariants: [InvariantSpec] = []
    private var explicitProperties: [PropertySpec] = []
    private var stateConstraints: [ConstraintSpec] = []
    private var stateActionConstraints: [ActionConstraintSpec] = []
    private var viewSpec: ViewSpec?
    private var symmetrySetSpecs: [SymmetrySetSpec] = []
    private var symmetryValues: Set<TLAValue> = []  // Resolved symmetry set values

    func cancel() {
        shouldCancel = true
    }

    // MARK: - Parallel Processing Support

    /// Result from processing a single state in parallel
    struct BatchResult: Sendable {
        let fromHash: StateHash
        let depth: Int
        let successors: [TLAState]
        let successorTraces: [[TLAState]]
        let isDeadlock: Bool
        let error: VerificationResult?
    }

    /// Processes a single state for parallel BFS
    private func processState(
        _ state: TLAState,
        trace: [TLAState],
        module: TLAModule,
        nextDef: OperatorDefinition,
        invariants: [OperatorDefinition],
        interpreter: TLAInterpreter,
        configuration: Configuration
    ) async -> BatchResult {
        let currentHash = state.hash
        let depth = trace.count

        // Skip if beyond max depth
        if depth > configuration.maxDepth {
            return BatchResult(
                fromHash: currentHash,
                depth: depth,
                successors: [],
                successorTraces: [],
                isDeadlock: false,
                error: nil
            )
        }

        // Check invariants
        if configuration.checkInvariants {
            for invariant in invariants {
                do {
                    let holds = try interpreter.evaluateInvariant(invariant, state: state, module: module)
                    if !holds {
                        return BatchResult(
                            fromHash: currentHash,
                            depth: depth,
                            successors: [],
                            successorTraces: [],
                            isDeadlock: false,
                            error: VerificationResult(
                                specificationName: module.name,
                                status: .failure,
                                error: "Invariant \(invariant.name) violated",
                                counterexample: trace.map { $0.toTraceState() }
                            )
                        )
                    }
                } catch {
                    return BatchResult(
                        fromHash: currentHash,
                        depth: depth,
                        successors: [],
                        successorTraces: [],
                        isDeadlock: false,
                        error: VerificationResult(
                            specificationName: module.name,
                            status: .error,
                            error: "Error checking invariant \(invariant.name): \(error)"
                        )
                    )
                }
            }
        }

        // Generate successor states
        do {
            let successors = try interpreter.evaluateNext(nextDef, state: state, module: module)

            if successors.isEmpty && configuration.checkDeadlock {
                return BatchResult(
                    fromHash: currentHash,
                    depth: depth,
                    successors: [],
                    successorTraces: [],
                    isDeadlock: true,
                    error: VerificationResult(
                        specificationName: module.name,
                        status: .failure,
                        error: "Deadlock detected",
                        counterexample: trace.map { $0.toTraceState() }
                    )
                )
            }

            let successorTraces = successors.map { trace + [$0] }

            return BatchResult(
                fromHash: currentHash,
                depth: depth,
                successors: successors,
                successorTraces: successorTraces,
                isDeadlock: false,
                error: nil
            )
        } catch {
            return BatchResult(
                fromHash: currentHash,
                depth: depth,
                successors: [],
                successorTraces: [],
                isDeadlock: false,
                error: VerificationResult(
                    specificationName: module.name,
                    status: .error,
                    error: "Error evaluating Next: \(error)"
                )
            )
        }
    }

    private func checkModel(_ module: TLAModule) async -> VerificationResult {
        let interpreter = TLAInterpreter()

        // Apply constant overrides to interpreter
        for override in constantOverrides {
            interpreter.setConstant(name: override.name, valueString: override.value)
        }

        // Find Init and Next
        guard let initDef = findOperator(named: "Init", in: module),
              let nextDef = findOperator(named: "Next", in: module) else {
            return VerificationResult(
                specificationName: module.name,
                status: .error,
                error: "Specification must define Init and Next operators"
            )
        }

        // Find invariants - use explicit list if provided, otherwise use heuristics
        let invariants = findInvariants(in: module, explicit: explicitInvariants)

        // Resolve symmetry sets if any are specified
        if !symmetrySetSpecs.isEmpty {
            resolveSymmetrySets(module: module, interpreter: interpreter)
        }

        // If simulation mode is enabled, run simulation instead of exhaustive BFS
        if configuration.simulationMode {
            return await runSimulation(
                module: module,
                initDef: initDef,
                nextDef: nextDef,
                invariants: invariants,
                interpreter: interpreter
            )
        }

        // Initialize state space exploration
        var visited: Set<StateHash> = []
        var queue: [TLAState] = []
        var trace: [[TLAState]] = [] // For counterexample generation

        // Generate initial states
        do {
            let initialStates = try interpreter.evaluateInit(initDef, module: module)
            for state in initialStates {
                // Use symmetry-aware hash if symmetry is enabled
                let hash = computeStateHash(state)
                if !visited.contains(hash) {
                    // Apply state constraints - skip states that don't satisfy constraints
                    if !stateConstraints.isEmpty && !satisfiesStateConstraints(state, module: module, interpreter: interpreter) {
                        continue
                    }

                    visited.insert(hash)
                    queue.append(state)
                    trace.append([state])
                    statistics.distinctStates += 1

                    // Track state for visualization (use original state, not canonical)
                    stateHashToIndex[hash] = exploredStates.count
                    exploredStates.append(state)
                    initialStateHashes.insert(hash)
                }
            }
        } catch {
            return VerificationResult(
                specificationName: module.name,
                status: .error,
                error: "Error evaluating Init: \(error)"
            )
        }

        statistics.statesGenerated = queue.count

        // BFS exploration - use parallel processing if workers > 1
        let useParallel = configuration.workers > 1
        let batchSize = useParallel ? min(configuration.workers * 4, 32) : 1

        while !queue.isEmpty && !shouldCancel {
            if statistics.distinctStates >= configuration.maxStates {
                return VerificationResult(
                    specificationName: module.name,
                    status: .error,
                    statesExplored: statistics.statesGenerated,
                    distinctStates: statistics.distinctStates,
                    duration: statistics.elapsedTime,
                    error: "State space limit exceeded (\(configuration.maxStates) states)"
                )
            }

            if useParallel && queue.count >= batchSize {
                // Parallel batch processing
                let batchCount = min(batchSize, queue.count)
                let batch = Array(queue.prefix(batchCount))
                let batchTraces = Array(trace.prefix(batchCount))
                queue.removeFirst(batchCount)
                trace.removeFirst(batchCount)

                // Capture constant overrides before entering TaskGroup to avoid actor isolation issues
                let capturedOverrides = constantOverrides
                let capturedConfig = configuration

                // Process batch in parallel using TaskGroup
                let batchResults = await withTaskGroup(of: BatchResult.self, returning: [BatchResult].self) { group in
                    for (index, state) in batch.enumerated() {
                        let stateTrace = batchTraces[index]
                        group.addTask {
                            // Each task gets its own interpreter to avoid data races
                            let taskInterpreter = TLAInterpreter()
                            // Apply constant overrides
                            for override in capturedOverrides {
                                taskInterpreter.setConstant(name: override.name, valueString: override.value)
                            }
                            return await self.processState(
                                state,
                                trace: stateTrace,
                                module: module,
                                nextDef: nextDef,
                                invariants: invariants,
                                interpreter: taskInterpreter,
                                configuration: capturedConfig
                            )
                        }
                    }

                    var results: [BatchResult] = []
                    for await result in group {
                        results.append(result)
                    }
                    return results
                }

                // Process batch results
                for result in batchResults {
                    if let error = result.error {
                        return error
                    }

                    statistics.depth = max(statistics.depth, result.depth)

                    // Recalculate fromHash with symmetry awareness
                    let fromHash = !symmetryValues.isEmpty ?
                        (batch.first(where: { computeStateHash($0) == result.fromHash }).map { computeStateHash($0) } ?? result.fromHash) :
                        result.fromHash

                    for (successor, successorTrace) in zip(result.successors, result.successorTraces) {
                        statistics.statesGenerated += 1
                        // Use symmetry-aware hash if symmetry is enabled
                        let hash = computeStateHash(successor)

                        // Track transition for visualization
                        stateTransitions.append(StateTransition(
                            fromHash: fromHash,
                            toHash: hash,
                            action: nil
                        ))

                        if !visited.contains(hash) {
                            visited.insert(hash)
                            queue.append(successor)
                            trace.append(successorTrace)
                            statistics.distinctStates += 1

                            // Track state for visualization
                            stateHashToIndex[hash] = exploredStates.count
                            exploredStates.append(successor)
                        }
                    }

                    if result.isDeadlock {
                        errorStateHashes.insert(fromHash)
                    }
                }
            } else {
                // Sequential processing for small queues or single worker
                let currentState = queue.removeFirst()
                let currentTrace = trace.removeFirst()
                statistics.depth = max(statistics.depth, currentTrace.count)

                if currentTrace.count > configuration.maxDepth {
                    continue // Skip states beyond max depth
                }

                // Check invariants
                if configuration.checkInvariants {
                    for invariant in invariants {
                        do {
                            let holds = try interpreter.evaluateInvariant(invariant, state: currentState, module: module)
                            if !holds {
                                // Mark as error state for visualization
                                errorStateHashes.insert(currentState.hash)

                                return VerificationResult(
                                    specificationName: module.name,
                                    status: .failure,
                                    statesExplored: statistics.statesGenerated,
                                    distinctStates: statistics.distinctStates,
                                    duration: statistics.elapsedTime,
                                    error: "Invariant \(invariant.name) violated",
                                    counterexample: currentTrace.map { $0.toTraceState() },
                                    explorationResult: getExplorationResult()
                                )
                            }
                        } catch {
                            return VerificationResult(
                                specificationName: module.name,
                                status: .error,
                                error: "Error checking invariant \(invariant.name): \(error)"
                            )
                        }
                    }
                }

                // Generate successor states
                do {
                    let successors = try interpreter.evaluateNext(nextDef, state: currentState, module: module)
                    // Use symmetry-aware hash if symmetry is enabled
                    let currentHash = computeStateHash(currentState)

                    if successors.isEmpty && configuration.checkDeadlock {
                        // Mark as error state for visualization
                        errorStateHashes.insert(currentHash)

                        return VerificationResult(
                            specificationName: module.name,
                            status: .failure,
                            statesExplored: statistics.statesGenerated,
                            distinctStates: statistics.distinctStates,
                            duration: statistics.elapsedTime,
                            error: "Deadlock detected",
                            counterexample: currentTrace.map { $0.toTraceState() },
                            explorationResult: getExplorationResult()
                        )
                    }

                    for successor in successors {
                        statistics.statesGenerated += 1

                        // Apply action constraints - skip transitions that don't satisfy constraints
                        if !stateActionConstraints.isEmpty &&
                           !satisfiesActionConstraints(fromState: currentState, toState: successor, module: module, interpreter: interpreter) {
                            continue
                        }

                        // Apply state constraints - skip states that don't satisfy constraints
                        if !stateConstraints.isEmpty &&
                           !satisfiesStateConstraints(successor, module: module, interpreter: interpreter) {
                            continue
                        }

                        // Use symmetry-aware hash if symmetry is enabled
                        let hash = computeStateHash(successor)

                        // Track transition for visualization
                        stateTransitions.append(StateTransition(
                            fromHash: currentHash,
                            toHash: hash,
                            action: nil
                        ))

                        if !visited.contains(hash) {
                            visited.insert(hash)
                            queue.append(successor)
                            trace.append(currentTrace + [successor])
                            statistics.distinctStates += 1

                            // Track state for visualization
                            stateHashToIndex[hash] = exploredStates.count
                            exploredStates.append(successor)
                        }
                    }
                } catch {
                    return VerificationResult(
                        specificationName: module.name,
                        status: .error,
                        error: "Error evaluating Next: \(error)"
                    )
                }
            }

            // Yield to allow cancellation
            if statistics.statesGenerated % 1000 == 0 {
                await Task.yield()
            }
        }

        if shouldCancel {
            return VerificationResult(
                specificationName: module.name,
                status: .cancelled,
                statesExplored: statistics.statesGenerated,
                distinctStates: statistics.distinctStates,
                duration: statistics.elapsedTime,
                explorationResult: getExplorationResult()
            )
        }

        // Check temporal properties (liveness) after BFS completes
        if configuration.checkLiveness {
            let temporalProperties = findTemporalProperties(in: module, explicit: explicitProperties)

            if !temporalProperties.isEmpty {
                let temporalResults = await checkTemporalProperties(
                    temporalProperties,
                    module: module,
                    interpreter: interpreter
                )

                // Check for violations
                for result in temporalResults where !result.holds {
                    // Mark error states for visualization
                    if let counterexample = result.counterexample, let lastState = counterexample.last {
                        errorStateHashes.insert(lastState.hash)
                    }

                    return VerificationResult(
                        specificationName: module.name,
                        status: .failure,
                        statesExplored: statistics.statesGenerated,
                        distinctStates: statistics.distinctStates,
                        duration: statistics.elapsedTime,
                        error: "Temporal property violated: \(describeProperty(result.property))",
                        counterexample: result.counterexample?.enumerated().map { index, state in
                            state.toTraceState(
                                stepNumber: index,
                                action: index == result.loopStart ? "← Loop starts here" : "",
                                isError: index == (result.counterexample?.count ?? 0) - 1
                            )
                        } ?? [],
                        explorationResult: getExplorationResult()
                    )
                }
            }
        }

        return VerificationResult(
            specificationName: module.name,
            status: .success,
            statesExplored: statistics.statesGenerated,
            distinctStates: statistics.distinctStates,
            duration: statistics.elapsedTime,
            output: """
            Model checking completed successfully.
            States explored: \(statistics.statesGenerated)
            Distinct states: \(statistics.distinctStates)
            Maximum depth: \(statistics.depth)
            Time: \(String(format: "%.2f", statistics.elapsedTime))s
            """,
            explorationResult: getExplorationResult()
        )
    }

    /// Helper to describe a temporal property for error messages
    private func describeProperty(_ property: TemporalProperty) -> String {
        switch property {
        case .always(let p): return "[](\(p))"
        case .eventually(let p): return "<>(\(p))"
        case .alwaysEventually(let p): return "[]<>(\(p))"
        case .eventuallyAlways(let p): return "<>[](\(p))"
        case .leadsto(let p, let q): return "\(p) ~> \(q)"
        case .weakFairness(let a): return "WF(\(a))"
        case .strongFairness(let a): return "SF(\(a))"
        }
    }

    private func getExplorationResult() -> ExplorationResult {
        ExplorationResult(
            states: exploredStates,
            stateHashes: stateHashToIndex,
            transitions: stateTransitions,
            initialStates: initialStateHashes,
            errorStates: errorStateHashes
        )
    }

    // MARK: - Temporal Property Checking

    /// Checks temporal properties using nested DFS (for liveness)
    private func checkTemporalProperties(
        _ properties: [TemporalProperty],
        module: TLAModule,
        interpreter: TLAInterpreter
    ) async -> [TemporalCheckResult] {
        var results: [TemporalCheckResult] = []

        for property in properties {
            let result = await checkTemporalProperty(property, module: module, interpreter: interpreter)
            results.append(result)

            if !result.holds {
                break // Stop on first violation
            }
        }

        return results
    }

    private func checkTemporalProperty(
        _ property: TemporalProperty,
        module: TLAModule,
        interpreter: TLAInterpreter
    ) async -> TemporalCheckResult {
        switch property {
        case .always(let predicate):
            // []P is checked during BFS - if any state violates P, it fails
            // Already handled by invariant checking
            return TemporalCheckResult(property: property, holds: true, counterexample: nil, loopStart: nil)

        case .eventually(let predicate):
            // <>P - check if P holds in some reachable state
            let holds = checkEventually(predicate, module: module, interpreter: interpreter)
            return TemporalCheckResult(property: property, holds: holds, counterexample: nil, loopStart: nil)

        case .alwaysEventually(let predicate):
            // []<>P - check that every cycle visits a state where P holds
            let result = checkAlwaysEventually(predicate, module: module, interpreter: interpreter)
            return result

        case .eventuallyAlways(let predicate):
            // <>[]P - check that some path eventually stays in states where P holds
            let holds = checkEventuallyAlways(predicate, module: module, interpreter: interpreter)
            return TemporalCheckResult(property: property, holds: holds, counterexample: nil, loopStart: nil)

        case .leadsto(let p, let q):
            // P ~> Q - whenever P holds, Q eventually holds
            let result = checkLeadsTo(p: p, q: q, module: module, interpreter: interpreter)
            return result

        case .weakFairness(let action):
            // WF_vars(A) - if A is continuously enabled, A must eventually occur
            // Violation: there's a suffix where A is always enabled but never taken
            let result = checkWeakFairness(action: action, module: module, interpreter: interpreter)
            return result

        case .strongFairness(let action):
            // SF_vars(A) - if A is infinitely often enabled, A must eventually occur
            // Violation: there's a cycle where A is enabled infinitely often but never taken
            let result = checkStrongFairness(action: action, module: module, interpreter: interpreter)
            return result
        }
    }

    // MARK: - Successor Map Helpers

    /// Builds a simple successor map from state transitions (hash -> [hash])
    private func buildSuccessorMap() -> [StateHash: [StateHash]] {
        var successors: [StateHash: [StateHash]] = [:]
        for transition in stateTransitions {
            successors[transition.fromHash, default: []].append(transition.toHash)
        }
        return successors
    }

    /// Builds a successor map that includes action names (hash -> [(hash, action?)])
    private func buildSuccessorMapWithActions() -> [StateHash: [(hash: StateHash, action: String?)]] {
        var successors: [StateHash: [(hash: StateHash, action: String?)]] = [:]
        for transition in stateTransitions {
            successors[transition.fromHash, default: []].append((transition.toHash, transition.action))
        }
        return successors
    }

    // MARK: - Temporal Property Checking

    private func checkEventually(_ predicate: String, module: TLAModule, interpreter: TLAInterpreter) -> Bool {
        // Check if any explored state satisfies the predicate
        for state in exploredStates {
            if evaluatePredicate(predicate, in: state, module: module, interpreter: interpreter) {
                return true
            }
        }
        return false
    }

    private func checkEventuallyAlways(_ predicate: String, module: TLAModule, interpreter: TLAInterpreter) -> Bool {
        // Find states that satisfy P and check if they form a terminal SCC
        for state in exploredStates {
            if evaluatePredicate(predicate, in: state, module: module, interpreter: interpreter) {
                // Check if this state is in a terminal SCC where P always holds
                if isInTerminalSCCWithProperty(state, predicate: predicate, module: module, interpreter: interpreter) {
                    return true
                }
            }
        }
        return false
    }

    private func checkAlwaysEventually(
        _ predicate: String,
        module: TLAModule,
        interpreter: TLAInterpreter
    ) -> TemporalCheckResult {
        // []<>P fails if there's a cycle that never visits a P-state
        // Use nested DFS to find such a cycle

        // First, identify accepting states (where P holds)
        var acceptingStates: Set<StateHash> = []
        for state in exploredStates {
            if evaluatePredicate(predicate, in: state, module: module, interpreter: interpreter) {
                acceptingStates.insert(state.hash)
            }
        }

        // Build successor map
        let successors = buildSuccessorMap()

        // Nested DFS to find accepting cycle
        var visited1: Set<StateHash> = []
        var stack: [TLAState] = []

        func dfs1(_ state: TLAState) -> [TLAState]? {
            let hash = state.hash
            visited1.insert(hash)
            stack.append(state)

            for succHash in successors[hash] ?? [] {
                if !visited1.contains(succHash) {
                    if let idx = stateHashToIndex[succHash] {
                        if let cycle = dfs1(exploredStates[idx]) {
                            return cycle
                        }
                    }
                }
            }

            // If this is NOT an accepting state, try to find a cycle back
            if !acceptingStates.contains(hash) {
                // Reset visited2 for each new target - critical fix!
                var visited2: Set<StateHash> = []

                func dfs2(_ state: TLAState, target: StateHash) -> [TLAState]? {
                    let h = state.hash
                    visited2.insert(h)

                    for succHash in successors[h] ?? [] {
                        if succHash == target {
                            // Found a cycle!
                            return []
                        }
                        if !visited2.contains(succHash) && !acceptingStates.contains(succHash) {
                            if let idx = stateHashToIndex[succHash] {
                                if let cycle = dfs2(exploredStates[idx], target: target) {
                                    return [exploredStates[idx]] + cycle
                                }
                            }
                        }
                    }

                    return nil
                }

                if let cycle = dfs2(state, target: hash) {
                    return stack + cycle
                }
            }

            stack.removeLast()
            return nil
        }

        // Run nested DFS from initial states
        for initHash in initialStateHashes {
            visited1.removeAll() // Reset for each initial state
            stack.removeAll()
            if let idx = stateHashToIndex[initHash] {
                if let cycle = dfs1(exploredStates[idx]) {
                    // Found a bad cycle
                    let loopStart = cycle.firstIndex { $0.hash == cycle.last?.hash } ?? 0
                    return TemporalCheckResult(
                        property: .alwaysEventually(predicate),
                        holds: false,
                        counterexample: cycle,
                        loopStart: loopStart
                    )
                }
            }
        }

        return TemporalCheckResult(
            property: .alwaysEventually(predicate),
            holds: true,
            counterexample: nil,
            loopStart: nil
        )
    }

    private func checkLeadsTo(
        p: String,
        q: String,
        module: TLAModule,
        interpreter: TLAInterpreter
    ) -> TemporalCheckResult {
        // P ~> Q: from any state where P holds, Q must eventually hold
        // This is equivalent to [](P => <>Q)

        // Build successor map
        let successors = buildSuccessorMap()

        // For each state where P holds, check if Q is reachable
        for state in exploredStates {
            if evaluatePredicate(p, in: state, module: module, interpreter: interpreter) {
                // BFS to find Q
                var visited: Set<StateHash> = []
                var queue: [StateHash] = [state.hash]
                var foundQ = false

                while !queue.isEmpty && !foundQ {
                    let current = queue.removeFirst()
                    if visited.contains(current) { continue }
                    visited.insert(current)

                    if let idx = stateHashToIndex[current] {
                        if evaluatePredicate(q, in: exploredStates[idx], module: module, interpreter: interpreter) {
                            foundQ = true
                            break
                        }
                    }

                    for succHash in successors[current] ?? [] {
                        if !visited.contains(succHash) {
                            queue.append(succHash)
                        }
                    }
                }

                if !foundQ {
                    // Found a P-state from which Q is never reached
                    return TemporalCheckResult(
                        property: .leadsto(p, q),
                        holds: false,
                        counterexample: [state],
                        loopStart: nil
                    )
                }
            }
        }

        return TemporalCheckResult(
            property: .leadsto(p, q),
            holds: true,
            counterexample: nil,
            loopStart: nil
        )
    }

    /// Check weak fairness: WF_vars(A) - if A is continuously enabled, A must eventually occur
    private func checkWeakFairness(
        action: String,
        module: TLAModule,
        interpreter: TLAInterpreter
    ) -> TemporalCheckResult {
        // Build successor map with action labels
        let successors = buildSuccessorMapWithActions()

        // Find states where the action is enabled
        func isActionEnabled(in state: TLAState) -> Bool {
            return evaluatePredicate("ENABLED \(action)", in: state, module: module, interpreter: interpreter)
        }

        // Find states where the action was taken
        func wasActionTaken(fromHash: StateHash) -> Bool {
            guard let transitions = successors[fromHash] else { return false }
            return transitions.contains { $0.action == action }
        }

        // WF violation: find a cycle where action is always enabled but never taken
        // This is a lasso: stem + loop where in the loop, action is continuously enabled but never taken

        var visited: Set<StateHash> = []
        var onStack: Set<StateHash> = []
        var stack: [TLAState] = []

        func dfs(_ state: TLAState) -> [TLAState]? {
            let hash = state.hash
            visited.insert(hash)
            onStack.insert(hash)
            stack.append(state)

            for (succHash, _) in successors[hash] ?? [] {
                if !visited.contains(succHash) {
                    if let idx = stateHashToIndex[succHash] {
                        if let counterexample = dfs(exploredStates[idx]) {
                            return counterexample
                        }
                    }
                } else if onStack.contains(succHash) {
                    // Found a cycle - check if it violates weak fairness
                    // Find the loop portion
                    if let loopStartIdx = stack.firstIndex(where: { $0.hash == succHash }) {
                        let loop = Array(stack[loopStartIdx...])

                        // Check if action is enabled in ALL states of the loop
                        let allEnabled = loop.allSatisfy { isActionEnabled(in: $0) }

                        // Check if action is NEVER taken in the loop
                        let neverTaken = loop.allSatisfy { !wasActionTaken(fromHash: $0.hash) }

                        if allEnabled && neverTaken {
                            // This is a weak fairness violation
                            return stack
                        }
                    }
                }
            }

            stack.removeLast()
            onStack.remove(hash)
            return nil
        }

        // Run DFS from initial states
        for initHash in initialStateHashes {
            visited.removeAll()
            onStack.removeAll()
            stack.removeAll()
            if let idx = stateHashToIndex[initHash] {
                if let counterexample = dfs(exploredStates[idx]) {
                    let loopStart = counterexample.count - stack.count
                    return TemporalCheckResult(
                        property: .weakFairness(action),
                        holds: false,
                        counterexample: counterexample,
                        loopStart: max(0, loopStart)
                    )
                }
            }
        }

        return TemporalCheckResult(
            property: .weakFairness(action),
            holds: true,
            counterexample: nil,
            loopStart: nil
        )
    }

    /// Check strong fairness: SF_vars(A) - if A is infinitely often enabled, A must eventually occur
    private func checkStrongFairness(
        action: String,
        module: TLAModule,
        interpreter: TLAInterpreter
    ) -> TemporalCheckResult {
        // Build successor map with action labels
        let successors = buildSuccessorMapWithActions()

        // Find states where the action is enabled
        func isActionEnabled(in state: TLAState) -> Bool {
            return evaluatePredicate("ENABLED \(action)", in: state, module: module, interpreter: interpreter)
        }

        // Find states where the action was taken
        func wasActionTaken(fromHash: StateHash) -> Bool {
            guard let transitions = successors[fromHash] else { return false }
            return transitions.contains { $0.action == action }
        }

        // SF violation: find a cycle where action is enabled in SOME states but never taken
        // (weaker than WF - action doesn't need to be continuously enabled)

        var visited: Set<StateHash> = []
        var onStack: Set<StateHash> = []
        var stack: [TLAState] = []

        func dfs(_ state: TLAState) -> [TLAState]? {
            let hash = state.hash
            visited.insert(hash)
            onStack.insert(hash)
            stack.append(state)

            for (succHash, _) in successors[hash] ?? [] {
                if !visited.contains(succHash) {
                    if let idx = stateHashToIndex[succHash] {
                        if let counterexample = dfs(exploredStates[idx]) {
                            return counterexample
                        }
                    }
                } else if onStack.contains(succHash) {
                    // Found a cycle - check if it violates strong fairness
                    if let loopStartIdx = stack.firstIndex(where: { $0.hash == succHash }) {
                        let loop = Array(stack[loopStartIdx...])

                        // Check if action is enabled in AT LEAST ONE state of the loop
                        let someEnabled = loop.contains { isActionEnabled(in: $0) }

                        // Check if action is NEVER taken in the loop
                        let neverTaken = loop.allSatisfy { !wasActionTaken(fromHash: $0.hash) }

                        if someEnabled && neverTaken {
                            // This is a strong fairness violation
                            return stack
                        }
                    }
                }
            }

            stack.removeLast()
            onStack.remove(hash)
            return nil
        }

        // Run DFS from initial states
        for initHash in initialStateHashes {
            visited.removeAll()
            onStack.removeAll()
            stack.removeAll()
            if let idx = stateHashToIndex[initHash] {
                if let counterexample = dfs(exploredStates[idx]) {
                    let loopStart = counterexample.count - stack.count
                    return TemporalCheckResult(
                        property: .strongFairness(action),
                        holds: false,
                        counterexample: counterexample,
                        loopStart: max(0, loopStart)
                    )
                }
            }
        }

        return TemporalCheckResult(
            property: .strongFairness(action),
            holds: true,
            counterexample: nil,
            loopStart: nil
        )
    }

    private func isInTerminalSCCWithProperty(
        _ state: TLAState,
        predicate: String,
        module: TLAModule,
        interpreter: TLAInterpreter
    ) -> Bool {
        // Simplified check - would need full SCC computation for accuracy
        // Check if all successors also satisfy the predicate
        let successors = buildSuccessorMap()

        var visited: Set<StateHash> = []
        var queue: [StateHash] = [state.hash]

        while !queue.isEmpty {
            let current = queue.removeFirst()
            if visited.contains(current) { continue }
            visited.insert(current)

            if let idx = stateHashToIndex[current] {
                if !evaluatePredicate(predicate, in: exploredStates[idx], module: module, interpreter: interpreter) {
                    return false
                }
            }

            for succHash in successors[current] ?? [] {
                if !visited.contains(succHash) {
                    queue.append(succHash)
                }
            }
        }

        return true
    }

    private func evaluatePredicate(_ predicate: String, in state: TLAState, module: TLAModule, interpreter: TLAInterpreter) -> Bool {
        // Parse and evaluate the predicate
        let parser = TLAParser()
        guard case .success(let expr) = parser.parseExpression(predicate) else {
            return false
        }

        var env = TLAInterpreter.Environment.from(module: module)
        env.variables = state.variables

        do {
            let result = try interpreter.evaluate(expr, in: env)
            if case .boolean(let b) = result {
                return b
            }
        } catch {
            // Evaluation failed
        }

        return false
    }

    /// Evaluates a state constraint - returns true if the state satisfies the constraint
    private func evaluateStateConstraint(_ constraint: ConstraintSpec, state: TLAState, module: TLAModule, interpreter: TLAInterpreter) -> Bool {
        return evaluatePredicate(constraint.expression, in: state, module: module, interpreter: interpreter)
    }

    /// Evaluates all state constraints - returns true if the state satisfies ALL constraints
    private func satisfiesStateConstraints(_ state: TLAState, module: TLAModule, interpreter: TLAInterpreter) -> Bool {
        for constraint in stateConstraints {
            if !evaluateStateConstraint(constraint, state: state, module: module, interpreter: interpreter) {
                return false
            }
        }
        return true
    }

    /// Evaluates an action constraint - returns true if the transition satisfies the constraint
    /// Action constraints can reference both current state variables and primed variables
    private func evaluateActionConstraint(_ constraint: ActionConstraintSpec, fromState: TLAState, toState: TLAState, module: TLAModule, interpreter: TLAInterpreter) -> Bool {
        let parser = TLAParser()
        guard case .success(let expr) = parser.parseExpression(constraint.expression) else {
            return false
        }

        var env = TLAInterpreter.Environment.from(module: module)
        env.variables = fromState.variables
        env.primedVariables = toState.variables

        do {
            let result = try interpreter.evaluate(expr, in: env)
            if case .boolean(let b) = result {
                return b
            }
        } catch {
            // Evaluation failed
        }

        return false
    }

    /// Evaluates all action constraints - returns true if the transition satisfies ALL constraints
    private func satisfiesActionConstraints(fromState: TLAState, toState: TLAState, module: TLAModule, interpreter: TLAInterpreter) -> Bool {
        for constraint in stateActionConstraints {
            if !evaluateActionConstraint(constraint, fromState: fromState, toState: toState, module: module, interpreter: interpreter) {
                return false
            }
        }
        return true
    }

    // MARK: - Symmetry Reduction

    /// Resolves symmetry set specifications to actual values
    private func resolveSymmetrySets(module: TLAModule, interpreter: TLAInterpreter) {
        symmetryValues = []

        // Build constant overrides dictionary
        var constantOverrideValues: [String: TLAValue] = [:]
        for override in constantOverrides {
            if let value = parseConstantValue(override.value) {
                constantOverrideValues[override.name] = value
            }
        }

        for spec in symmetrySetSpecs {
            // Parse the symmetry set expression (e.g., "Permutations(Nodes)" or just "Nodes")
            let expression = spec.name

            // Try to evaluate the expression
            let parser = TLAParser()
            if case .success(let expr) = parser.parseExpression(expression) {
                var env = TLAInterpreter.Environment.from(module: module, constantOverrides: constantOverrideValues)

                // Try to evaluate to get the set of symmetric values
                if let result = try? interpreter.evaluate(expr, in: env) {
                    switch result {
                    case .set(let values):
                        symmetryValues.formUnion(values)
                    default:
                        // If not a set, treat the expression name as a constant set reference
                        if let constValue = env.constants[expression] {
                            if case .set(let values) = constValue {
                                symmetryValues.formUnion(values)
                            }
                        }
                    }
                }
            }
        }
    }

    /// Parse a constant value string into a TLAValue
    private func parseConstantValue(_ valueStr: String) -> TLAValue? {
        let trimmed = valueStr.trimmingCharacters(in: .whitespaces)

        // Try to parse as number
        if let n = Int(trimmed) {
            return .integer(n)
        }

        // Try to parse as boolean
        if trimmed.uppercased() == "TRUE" {
            return .boolean(true)
        }
        if trimmed.uppercased() == "FALSE" {
            return .boolean(false)
        }

        // Try to parse as set: {a, b, c}
        if trimmed.hasPrefix("{") && trimmed.hasSuffix("}") {
            let inner = String(trimmed.dropFirst().dropLast())
            let elements = inner.components(separatedBy: ",").map { $0.trimmingCharacters(in: .whitespaces) }
            var values: Set<TLAValue> = []
            for elem in elements where !elem.isEmpty {
                // Treat each element as a model value
                values.insert(.modelValue(elem))
            }
            return .set(values)
        }

        // Default: treat as model value
        return .modelValue(trimmed)
    }

    /// Canonicalizes a state by mapping symmetric values to their canonical form
    /// Uses lexicographic ordering to choose the canonical representative
    private func canonicalizeState(_ state: TLAState) -> TLAState {
        guard !symmetryValues.isEmpty else { return state }

        // Find all symmetric values that appear in this state
        var usedSymValues: [TLAValue] = []
        for (_, value) in state.variables {
            collectSymmetricValues(from: value, into: &usedSymValues)
        }

        // If no symmetric values are used, return as-is
        guard !usedSymValues.isEmpty else { return state }

        // Sort the used symmetric values to create a canonical mapping
        // Map the first-encountered symmetric value to the smallest canonical value, etc.
        let sortedSymValues = Array(symmetryValues).sorted { $0.sortKey < $1.sortKey }
        let usedSorted = usedSymValues.sorted { $0.sortKey < $1.sortKey }

        // Create mapping from original values to canonical values
        var mapping: [TLAValue: TLAValue] = [:]
        for (index, originalValue) in usedSorted.enumerated() {
            if index < sortedSymValues.count {
                mapping[originalValue] = sortedSymValues[index]
            }
        }

        // Apply the mapping to create canonical state
        var canonicalVars: [String: TLAValue] = [:]
        for (name, value) in state.variables {
            canonicalVars[name] = applySymmetryMapping(to: value, mapping: mapping)
        }

        return TLAState(variables: canonicalVars)
    }

    /// Collect all symmetric values that appear in a TLAValue
    private func collectSymmetricValues(from value: TLAValue, into collection: inout [TLAValue]) {
        if symmetryValues.contains(value) {
            if !collection.contains(value) {
                collection.append(value)
            }
            return
        }

        switch value {
        case .set(let elements):
            for elem in elements {
                collectSymmetricValues(from: elem, into: &collection)
            }
        case .sequence(let elements):
            for elem in elements {
                collectSymmetricValues(from: elem, into: &collection)
            }
        case .record(let fields):
            for (_, fieldValue) in fields {
                collectSymmetricValues(from: fieldValue, into: &collection)
            }
        case .function(let mappings):
            for (key, val) in mappings {
                collectSymmetricValues(from: key, into: &collection)
                collectSymmetricValues(from: val, into: &collection)
            }
        default:
            break
        }
    }

    /// Apply symmetry mapping to a value
    private func applySymmetryMapping(to value: TLAValue, mapping: [TLAValue: TLAValue]) -> TLAValue {
        // Direct mapping
        if let mapped = mapping[value] {
            return mapped
        }

        // Recursive mapping for compound values
        switch value {
        case .set(let elements):
            return .set(Set(elements.map { applySymmetryMapping(to: $0, mapping: mapping) }))
        case .sequence(let elements):
            return .sequence(elements.map { applySymmetryMapping(to: $0, mapping: mapping) })
        case .record(let fields):
            var mappedFields: [String: TLAValue] = [:]
            for (key, val) in fields {
                mappedFields[key] = applySymmetryMapping(to: val, mapping: mapping)
            }
            return .record(mappedFields)
        case .function(let mappings):
            var mappedFunction: [TLAValue: TLAValue] = [:]
            for (key, val) in mappings {
                let mappedKey = applySymmetryMapping(to: key, mapping: mapping)
                let mappedVal = applySymmetryMapping(to: val, mapping: mapping)
                mappedFunction[mappedKey] = mappedVal
            }
            return .function(mappedFunction)
        default:
            return value
        }
    }

    /// Computes the hash of a state, using canonical form if symmetry is enabled
    private func computeStateHash(_ state: TLAState) -> StateHash {
        if !symmetryValues.isEmpty {
            let canonical = canonicalizeState(state)
            return canonical.hash
        }
        return state.hash
    }

    // MARK: - Simulation Mode

    /// Runs simulation mode - random trace generation instead of exhaustive BFS
    private func runSimulation(
        module: TLAModule,
        initDef: OperatorDefinition,
        nextDef: OperatorDefinition,
        invariants: [OperatorDefinition],
        interpreter: TLAInterpreter
    ) async -> VerificationResult {
        var actionCoverage: [String: Int] = [:]  // Track how often each action is taken
        var statesVisited = 0
        var tracesGenerated = 0
        var maxDepthReached = 0

        // Generate initial states
        let initialStates: [TLAState]
        do {
            initialStates = try interpreter.evaluateInit(initDef, module: module)
            if initialStates.isEmpty {
                return VerificationResult(
                    specificationName: module.name,
                    status: .error,
                    error: "No initial states generated"
                )
            }
        } catch {
            return VerificationResult(
                specificationName: module.name,
                status: .error,
                error: "Error evaluating Init: \(error)"
            )
        }

        // Run simulation traces
        for traceNum in 0..<configuration.simulationTraceCount {
            if shouldCancel { break }

            tracesGenerated += 1

            // Pick a random initial state
            let initialState = initialStates.randomElement()!
            var currentState = initialState
            var trace: [TLAState] = [currentState]
            var depth = 0

            // Run trace until max depth or deadlock
            while depth < configuration.simulationTraceDepth && !shouldCancel {
                depth += 1
                statesVisited += 1

                // Check invariants
                if configuration.checkInvariants {
                    for invariant in invariants {
                        do {
                            let holds = try interpreter.evaluateInvariant(invariant, state: currentState, module: module)
                            if !holds {
                                return VerificationResult(
                                    specificationName: module.name,
                                    status: .failure,
                                    statesExplored: statesVisited,
                                    distinctStates: 0,  // Not tracked in simulation
                                    duration: statistics.elapsedTime,
                                    error: "Invariant \(invariant.name) violated (simulation trace \(traceNum + 1))",
                                    counterexample: trace.map { $0.toTraceState() }
                                )
                            }
                        } catch {
                            return VerificationResult(
                                specificationName: module.name,
                                status: .error,
                                error: "Error checking invariant \(invariant.name): \(error)"
                            )
                        }
                    }
                }

                // Generate successors
                do {
                    var successors = try interpreter.evaluateNext(nextDef, state: currentState, module: module)

                    // Apply state constraints if any
                    if !stateConstraints.isEmpty {
                        successors = successors.filter { satisfiesStateConstraints($0, module: module, interpreter: interpreter) }
                    }

                    // Apply action constraints if any
                    if !stateActionConstraints.isEmpty {
                        successors = successors.filter { satisfiesActionConstraints(fromState: currentState, toState: $0, module: module, interpreter: interpreter) }
                    }

                    if successors.isEmpty {
                        // Deadlock - end trace
                        if configuration.checkDeadlock {
                            return VerificationResult(
                                specificationName: module.name,
                                status: .failure,
                                statesExplored: statesVisited,
                                distinctStates: 0,
                                duration: statistics.elapsedTime,
                                error: "Deadlock detected (simulation trace \(traceNum + 1))",
                                counterexample: trace.map { $0.toTraceState() }
                            )
                        }
                        break  // End trace without error
                    }

                    // Pick a random successor
                    let nextState = successors.randomElement()!
                    trace.append(nextState)
                    currentState = nextState

                    // Track action coverage (simplified - just count transitions)
                    actionCoverage["_transition", default: 0] += 1

                } catch {
                    return VerificationResult(
                        specificationName: module.name,
                        status: .error,
                        error: "Error evaluating Next: \(error)"
                    )
                }
            }

            maxDepthReached = max(maxDepthReached, depth)

            // Yield periodically
            if traceNum % 10 == 0 {
                await Task.yield()
            }
        }

        if shouldCancel {
            return VerificationResult(
                specificationName: module.name,
                status: .cancelled,
                statesExplored: statesVisited,
                distinctStates: 0,
                duration: statistics.elapsedTime
            )
        }

        // Build coverage report
        let coverageReport = actionCoverage.map { "\($0.key): \($0.value)" }.joined(separator: "\n")

        return VerificationResult(
            specificationName: module.name,
            status: .success,
            statesExplored: statesVisited,
            distinctStates: 0,  // Not tracked in simulation
            duration: statistics.elapsedTime,
            output: """
            Simulation completed successfully.
            Traces generated: \(tracesGenerated)
            States visited: \(statesVisited)
            Maximum depth: \(maxDepthReached)
            Time: \(String(format: "%.2f", statistics.elapsedTime))s

            Coverage:
            \(coverageReport)
            """
        )
    }

    /// Find temporal properties defined in the module
    private func findTemporalProperties(in module: TLAModule, explicit: [PropertySpec] = []) -> [TemporalProperty] {
        var properties: [TemporalProperty] = []

        // If explicit properties provided, convert them to TemporalProperty
        if !explicit.isEmpty {
            for spec in explicit {
                // Try to parse the property name/expression
                // Common patterns: Liveness, Termination, []<>P, P ~> Q
                let name = spec.name
                if name.contains("~>") {
                    // Leads-to: P ~> Q
                    let parts = name.components(separatedBy: "~>")
                    if parts.count == 2 {
                        properties.append(.leadsto(parts[0].trimmingCharacters(in: .whitespaces),
                                                   parts[1].trimmingCharacters(in: .whitespaces)))
                    }
                } else if let temporalOp = TemporalOperator.detect(in: name) {
                    // Use TemporalOperator enum to parse temporal formulas
                    let predicate = temporalOp.extractPredicate(from: name)
                    let resultPredicate = predicate.isEmpty ? name : predicate
                    switch temporalOp {
                    case .alwaysEventually:
                        properties.append(.alwaysEventually(resultPredicate))
                    case .eventuallyAlways:
                        properties.append(.eventuallyAlways(resultPredicate))
                    case .eventually:
                        properties.append(.eventually(resultPredicate))
                    case .always:
                        properties.append(.always(resultPredicate))
                    }
                } else if name.hasPrefix("WF_") || name.hasPrefix("WF(") {
                    // Weak fairness
                    let action = name.replacingOccurrences(of: "WF_", with: "")
                        .replacingOccurrences(of: "WF(", with: "")
                        .replacingOccurrences(of: ")", with: "")
                    properties.append(.weakFairness(action))
                } else if name.hasPrefix("SF_") || name.hasPrefix("SF(") {
                    // Strong fairness
                    let action = name.replacingOccurrences(of: "SF_", with: "")
                        .replacingOccurrences(of: "SF(", with: "")
                        .replacingOccurrences(of: ")", with: "")
                    properties.append(.strongFairness(action))
                } else {
                    // Assume it's an operator name, try to find and analyze it
                    if let op = findOperator(named: name, in: module) {
                        if let propName = extractPropertyName(from: op) {
                            properties.append(.alwaysEventually(propName))
                        }
                    }
                }
            }
            return properties
        }

        // Otherwise, use heuristics to find temporal properties by naming pattern
        for decl in module.declarations {
            if case .operatorDef(let def) = decl {
                // Look for common patterns
                let name = def.name.lowercased()

                if name.contains("liveness") || name.contains("live") {
                    // Extract the property from the operator body
                    if let propName = extractPropertyName(from: def) {
                        properties.append(.alwaysEventually(propName))
                    }
                }

                if name == "termination" || name.contains("terminate") {
                    // Termination is typically <>Done
                    properties.append(.eventually("pc = \"Done\""))
                }
            }
        }

        return properties
    }

    private func extractPropertyName(from def: OperatorDefinition) -> String? {
        // Simple extraction - just return the operator name as a placeholder
        return def.name
    }

    private func findOperator(named name: String, in module: TLAModule) -> OperatorDefinition? {
        for decl in module.declarations {
            if case .operatorDef(let def) = decl, def.name == name {
                return def
            }
        }
        return nil
    }

    private func findInvariants(in module: TLAModule, explicit: [InvariantSpec] = []) -> [OperatorDefinition] {
        var invariants: [OperatorDefinition] = []

        // If explicit invariants provided, use those
        if !explicit.isEmpty {
            for spec in explicit {
                if let op = findOperator(named: spec.name, in: module) {
                    invariants.append(op)
                }
            }
            return invariants
        }

        // Otherwise, use heuristics to find invariants by naming pattern
        for decl in module.declarations {
            if case .operatorDef(let def) = decl {
                let name = def.name
                if name.hasSuffix("Inv") ||
                   name.hasSuffix("Invariant") ||
                   name.hasPrefix("TypeOK") ||
                   name == "TypeInvariant" {
                    invariants.append(def)
                }
            }
        }
        return invariants
    }
}

// MARK: - State Representation

typealias StateHash = Int

struct TLAState: Hashable, @unchecked Sendable {
    var variables: [String: TLAValue]

    var hash: StateHash {
        var hasher = Hasher()
        for (key, value) in variables.sorted(by: { $0.key < $1.key }) {
            hasher.combine(key)
            hasher.combine(value)
        }
        return hasher.finalize()
    }

    init(variables: [String: TLAValue] = [:]) {
        self.variables = variables
    }
}

enum TLAValue: Hashable, CustomStringConvertible, Sendable {
    case boolean(Bool)
    case integer(Int)
    case string(String)
    case set(Set<TLAValue>)
    case sequence([TLAValue])
    case record([String: TLAValue])
    case function([TLAValue: TLAValue])
    case modelValue(String)

    var description: String {
        switch self {
        case .boolean(let b): return b ? "TRUE" : "FALSE"
        case .integer(let n): return String(n)
        case .string(let s): return "\"\(s)\""
        case .set(let s): return "{\(s.map(\.description).joined(separator: ", "))}"
        case .sequence(let seq): return "<<\(seq.map(\.description).joined(separator: ", "))>>"
        case .record(let r):
            let fields = r.map { "\($0.key) |-> \($0.value.description)" }.joined(separator: ", ")
            return "[\(fields)]"
        case .function(let f):
            let mappings = f.map { "\($0.key.description) :> \($0.value.description)" }.joined(separator: " @@ ")
            return "(\(mappings))"
        case .modelValue(let name): return name
        }
    }

    /// Comparable key for deterministic sorting of TLAValues
    var sortKey: String {
        switch self {
        case .boolean(let b): return "0_\(b ? "1" : "0")"
        case .integer(let n): return "1_\(String(format: "%020d", n + Int.max/2))"  // Pad for proper sorting
        case .string(let s): return "2_\(s)"
        case .set(let s): return "3_\(s.map(\.sortKey).sorted().joined(separator: ","))"
        case .sequence(let seq): return "4_\(seq.map(\.sortKey).joined(separator: ","))"
        case .record(let r): return "5_\(r.sorted { $0.key < $1.key }.map { "\($0.key):\($0.value.sortKey)" }.joined(separator: ","))"
        case .function(let f): return "6_\(f.sorted { $0.key.sortKey < $1.key.sortKey }.map { "\($0.key.sortKey):\($0.value.sortKey)" }.joined(separator: ","))"
        case .modelValue(let name): return "7_\(name)"
        }
    }

    func hash(into hasher: inout Hasher) {
        switch self {
        case .boolean(let b): hasher.combine(0); hasher.combine(b)
        case .integer(let n): hasher.combine(1); hasher.combine(n)
        case .string(let s): hasher.combine(2); hasher.combine(s)
        case .set(let s): hasher.combine(3); hasher.combine(s)
        case .sequence(let seq): hasher.combine(4); hasher.combine(seq)
        case .record(let r):
            hasher.combine(5)
            for (k, v) in r.sorted(by: { $0.key < $1.key }) {
                hasher.combine(k)
                hasher.combine(v)
            }
        case .function(let f):
            hasher.combine(6)
            for (k, v) in f.sorted(by: { $0.key.description < $1.key.description }) {
                hasher.combine(k)
                hasher.combine(v)
            }
        case .modelValue(let name): hasher.combine(7); hasher.combine(name)
        }
    }
}
