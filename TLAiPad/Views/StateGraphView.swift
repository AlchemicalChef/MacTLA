import SwiftUI

/// Visualizes the state space as an interactive graph
struct StateGraphView: View {
    let states: [GraphState]
    let transitions: [GraphTransition]
    @State private var selectedState: GraphState?
    @State private var scale: CGFloat = 1.0
    @State private var offset: CGSize = .zero
    @GestureState private var dragOffset: CGSize = .zero

    var body: some View {
        GeometryReader { geometry in
            ZStack {
                // Background
                #if os(macOS)
                Color(NSColor.windowBackgroundColor)
                #else
                Color(.systemBackground)
                #endif

                // Graph canvas
                Canvas { context, size in
                    let center = CGPoint(x: size.width / 2, y: size.height / 2)

                    // Draw transitions (edges)
                    for transition in transitions {
                        guard let fromState = states.first(where: { $0.id == transition.fromId }),
                              let toState = states.first(where: { $0.id == transition.toId }) else {
                            continue
                        }

                        let fromPos = position(for: fromState, center: center, scale: scale, offset: totalOffset)
                        let toPos = position(for: toState, center: center, scale: scale, offset: totalOffset)

                        var path = Path()
                        path.move(to: fromPos)
                        path.addLine(to: toPos)

                        context.stroke(
                            path,
                            with: .color(.secondary.opacity(0.5)),
                            lineWidth: 1
                        )

                        // Draw arrow head
                        drawArrowHead(context: context, from: fromPos, to: toPos)
                    }

                    // Draw states (nodes)
                    for state in states {
                        let pos = position(for: state, center: center, scale: scale, offset: totalOffset)
                        let isSelected = selectedState?.id == state.id

                        // Node circle
                        let radius: CGFloat = isSelected ? 25 : 20
                        let rect = CGRect(
                            x: pos.x - radius,
                            y: pos.y - radius,
                            width: radius * 2,
                            height: radius * 2
                        )

                        let color: Color = state.isInitial ? .green :
                                           state.isError ? .red :
                                           isSelected ? .blue : .gray

                        context.fill(Circle().path(in: rect), with: .color(color))
                        context.stroke(Circle().path(in: rect), with: .color(.primary), lineWidth: isSelected ? 2 : 1)

                        // State label
                        let text = Text(state.label).font(.caption2)
                        context.draw(text, at: CGPoint(x: pos.x, y: pos.y + radius + 10))
                    }
                }
                .gesture(
                    MagnificationGesture()
                        .onChanged { value in
                            scale = max(0.5, min(3.0, value))
                        }
                )
                .gesture(
                    DragGesture()
                        .updating($dragOffset) { value, state, _ in
                            state = value.translation
                        }
                        .onEnded { value in
                            offset = CGSize(
                                width: offset.width + value.translation.width,
                                height: offset.height + value.translation.height
                            )
                        }
                )
                .onTapGesture { location in
                    let center = CGPoint(x: geometry.size.width / 2, y: geometry.size.height / 2)
                    selectedState = findState(at: location, center: center)
                }

                // State details panel
                if let state = selectedState {
                    VStack {
                        Spacer()
                        StateDetailPanel(state: state) {
                            selectedState = nil
                        }
                    }
                    .transition(.move(edge: .bottom))
                }

                // Controls overlay
                VStack {
                    HStack {
                        Spacer()
                        VStack(spacing: 8) {
                            Button(action: { scale = min(3.0, scale * 1.2) }) {
                                Image(systemName: "plus.magnifyingglass")
                                    .padding(8)
                                    .background(.ultraThinMaterial)
                                    .clipShape(Circle())
                            }
                            Button(action: { scale = max(0.5, scale / 1.2) }) {
                                Image(systemName: "minus.magnifyingglass")
                                    .padding(8)
                                    .background(.ultraThinMaterial)
                                    .clipShape(Circle())
                            }
                            Button(action: resetView) {
                                Image(systemName: "arrow.counterclockwise")
                                    .padding(8)
                                    .background(.ultraThinMaterial)
                                    .clipShape(Circle())
                            }
                        }
                        .padding()
                    }
                    Spacer()
                }

                // Legend
                VStack {
                    HStack {
                        LegendItem(color: .green, label: "Initial")
                        LegendItem(color: .red, label: "Error")
                        LegendItem(color: .gray, label: "Normal")
                    }
                    .padding(8)
                    .background(.ultraThinMaterial)
                    .clipShape(RoundedRectangle(cornerRadius: 8))
                    .padding()
                    Spacer()
                }
            }
        }
        .navigationTitle("State Graph")
    }

    private var totalOffset: CGSize {
        CGSize(
            width: offset.width + dragOffset.width,
            height: offset.height + dragOffset.height
        )
    }

    private func position(for state: GraphState, center: CGPoint, scale: CGFloat, offset: CGSize) -> CGPoint {
        CGPoint(
            x: center.x + (state.x * scale) + offset.width,
            y: center.y + (state.y * scale) + offset.height
        )
    }

    private func findState(at location: CGPoint, center: CGPoint) -> GraphState? {
        for state in states {
            let pos = position(for: state, center: center, scale: scale, offset: totalOffset)
            let distance = hypot(location.x - pos.x, location.y - pos.y)
            if distance < 25 {
                return state
            }
        }
        return nil
    }

    private func drawArrowHead(context: GraphicsContext, from: CGPoint, to: CGPoint) {
        let angle = atan2(to.y - from.y, to.x - from.x)
        let arrowLength: CGFloat = 10
        let arrowAngle: CGFloat = .pi / 6

        // Calculate the point where arrow meets the circle (radius 20)
        let distance = hypot(to.x - from.x, to.y - from.y)

        // Guard against division by zero (overlapping states)
        guard distance > 20 else { return }

        let ratio = (distance - 20) / distance
        let arrowTip = CGPoint(
            x: from.x + (to.x - from.x) * ratio,
            y: from.y + (to.y - from.y) * ratio
        )

        let point1 = CGPoint(
            x: arrowTip.x - arrowLength * cos(angle - arrowAngle),
            y: arrowTip.y - arrowLength * sin(angle - arrowAngle)
        )
        let point2 = CGPoint(
            x: arrowTip.x - arrowLength * cos(angle + arrowAngle),
            y: arrowTip.y - arrowLength * sin(angle + arrowAngle)
        )

        var path = Path()
        path.move(to: arrowTip)
        path.addLine(to: point1)
        path.move(to: arrowTip)
        path.addLine(to: point2)

        context.stroke(path, with: .color(.secondary), lineWidth: 1)
    }

    private func resetView() {
        withAnimation {
            scale = 1.0
            offset = .zero
        }
    }
}

struct LegendItem: View {
    let color: Color
    let label: String

    var body: some View {
        HStack(spacing: 4) {
            Circle()
                .fill(color)
                .frame(width: 10, height: 10)
            Text(label)
                .font(.caption)
        }
    }
}

struct StateDetailPanel: View {
    let state: GraphState
    let onDismiss: () -> Void

    var body: some View {
        VStack(alignment: .leading, spacing: 12) {
            HStack {
                Text("State \(state.label)")
                    .font(.headline)
                Spacer()
                Button(action: onDismiss) {
                    Image(systemName: "xmark.circle.fill")
                        .foregroundStyle(.secondary)
                }
            }

            Divider()

            ForEach(state.variables.sorted(by: { $0.key < $1.key }), id: \.key) { key, value in
                HStack {
                    Text(key)
                        .font(.system(.body, design: .monospaced))
                        .foregroundStyle(.secondary)
                    Spacer()
                    Text(value)
                        .font(.system(.body, design: .monospaced))
                }
            }

            if state.isInitial {
                Label("Initial State", systemImage: "flag.fill")
                    .foregroundStyle(.green)
            }
            if state.isError {
                Label("Error State", systemImage: "exclamationmark.triangle.fill")
                    .foregroundStyle(.red)
            }
        }
        .padding()
        .background(.ultraThickMaterial)
        .clipShape(RoundedRectangle(cornerRadius: 16))
        .padding()
    }
}

// MARK: - Graph Data Models

struct GraphState: Identifiable {
    let id: UUID
    let label: String
    let variables: [String: String]
    let isInitial: Bool
    let isError: Bool
    var x: CGFloat
    var y: CGFloat

    init(
        id: UUID = UUID(),
        label: String,
        variables: [String: String],
        isInitial: Bool = false,
        isError: Bool = false,
        x: CGFloat = 0,
        y: CGFloat = 0
    ) {
        self.id = id
        self.label = label
        self.variables = variables
        self.isInitial = isInitial
        self.isError = isError
        self.x = x
        self.y = y
    }
}

struct GraphTransition: Identifiable {
    let id: UUID
    let fromId: UUID
    let toId: UUID
    let action: String?

    init(id: UUID = UUID(), fromId: UUID, toId: UUID, action: String? = nil) {
        self.id = id
        self.fromId = fromId
        self.toId = toId
        self.action = action
    }
}

// MARK: - Graph Layout

final class GraphLayoutEngine {
    /// Arranges states in a force-directed layout
    static func layout(states: inout [GraphState], transitions: [GraphTransition]) {
        guard states.count > 1 else {
            if let index = states.indices.first {
                states[index].x = 0
                states[index].y = 0
            }
            return
        }

        // Initialize positions in a circle
        let radius: CGFloat = CGFloat(states.count) * 30
        for (index, _) in states.enumerated() {
            let angle = CGFloat(index) / CGFloat(states.count) * 2 * .pi
            states[index].x = radius * cos(angle)
            states[index].y = radius * sin(angle)
        }

        // Apply force-directed algorithm
        let iterations = 50
        let repulsion: CGFloat = 5000
        let attraction: CGFloat = 0.01
        let damping: CGFloat = 0.85

        var velocities = Array(repeating: CGSize.zero, count: states.count)

        for _ in 0..<iterations {
            // Calculate repulsion forces between all pairs
            for i in 0..<states.count {
                for j in (i + 1)..<states.count {
                    let dx = states[j].x - states[i].x
                    let dy = states[j].y - states[i].y
                    let distance = max(1, hypot(dx, dy))
                    let force = repulsion / (distance * distance)

                    let fx = force * dx / distance
                    let fy = force * dy / distance

                    velocities[i].width -= fx
                    velocities[i].height -= fy
                    velocities[j].width += fx
                    velocities[j].height += fy
                }
            }

            // Calculate attraction forces along edges
            for transition in transitions {
                guard let fromIndex = states.firstIndex(where: { $0.id == transition.fromId }),
                      let toIndex = states.firstIndex(where: { $0.id == transition.toId }) else {
                    continue
                }

                let dx = states[toIndex].x - states[fromIndex].x
                let dy = states[toIndex].y - states[fromIndex].y
                let distance = hypot(dx, dy)

                let fx = attraction * dx
                let fy = attraction * dy

                velocities[fromIndex].width += fx
                velocities[fromIndex].height += fy
                velocities[toIndex].width -= fx
                velocities[toIndex].height -= fy
            }

            // Apply velocities with damping
            for i in 0..<states.count {
                states[i].x += velocities[i].width
                states[i].y += velocities[i].height
                velocities[i].width *= damping
                velocities[i].height *= damping
            }
        }

        // Center the graph
        let centerX = states.map(\.x).reduce(0, +) / CGFloat(states.count)
        let centerY = states.map(\.y).reduce(0, +) / CGFloat(states.count)

        for i in 0..<states.count {
            states[i].x -= centerX
            states[i].y -= centerY
        }
    }
}

// MARK: - Graph Builder

extension ModelChecker {
    /// Builds a graph representation from verification results
    static func buildGraph(from result: VerificationResult, states: [TLAState]) -> (states: [GraphState], transitions: [GraphTransition]) {
        var graphStates: [GraphState] = []
        var transitions: [GraphTransition] = []
        var stateMap: [StateHash: UUID] = [:]

        // Create graph states
        for (index, state) in states.enumerated() {
            let graphState = GraphState(
                label: "S\(index)",
                variables: state.variables.mapValues { $0.description },
                isInitial: index == 0,
                isError: result.status == .failure && index == states.count - 1
            )
            graphStates.append(graphState)
            stateMap[state.hash] = graphState.id
        }

        // Create transitions (simplified - actual implementation would track transitions during verification)
        for i in 0..<(states.count - 1) {
            if let fromId = stateMap[states[i].hash],
               let toId = stateMap[states[i + 1].hash] {
                transitions.append(GraphTransition(fromId: fromId, toId: toId))
            }
        }

        // Layout the graph
        GraphLayoutEngine.layout(states: &graphStates, transitions: transitions)

        return (graphStates, transitions)
    }
}

#Preview {
    let state1 = GraphState(label: "S0", variables: ["x": "0"], isInitial: true, x: -100, y: 0)
    let state2 = GraphState(label: "S1", variables: ["x": "1"], x: 0, y: -80)
    let state3 = GraphState(label: "S2", variables: ["x": "2"], x: 100, y: 0)
    let state4 = GraphState(label: "S3", variables: ["x": "3"], isError: true, x: 0, y: 80)

    let transitions = [
        GraphTransition(fromId: state1.id, toId: state2.id),
        GraphTransition(fromId: state2.id, toId: state3.id),
        GraphTransition(fromId: state3.id, toId: state4.id),
        GraphTransition(fromId: state4.id, toId: state1.id),
    ]

    return StateGraphView(states: [state1, state2, state3, state4], transitions: transitions)
}
