import SwiftUI

// MARK: - Variable Display Components

/// Displays a key-value pair with monospaced font
struct VariablePairView: View {
    let key: String
    let value: String
    var keyColor: Color = .secondary
    var valueColor: Color = .primary
    var showEquals: Bool = true

    var body: some View {
        HStack(alignment: .top) {
            Text(key)
                .tlaMonospaced()
                .foregroundStyle(keyColor)

            if showEquals {
                Text("=")
                    .tlaMonospaced()
                    .foregroundStyle(.secondary)
            }

            Spacer()

            Text(value)
                .tlaMonospaced()
                .foregroundStyle(valueColor)
                .textSelection(.enabled)
        }
    }
}

// MARK: - Empty State Components

/// A customizable empty state view
struct TLAEmptyStateView: View {
    let icon: String
    let title: String
    let description: String

    var body: some View {
        ContentUnavailableView(
            title,
            systemImage: icon,
            description: Text(description)
        )
    }
}

// MARK: - Panel Components

/// A detail panel with header, divider, and content
struct DetailPanel<Content: View>: View {
    let title: String
    let onDismiss: (() -> Void)?
    @ViewBuilder let content: () -> Content

    init(title: String, onDismiss: (() -> Void)? = nil, @ViewBuilder content: @escaping () -> Content) {
        self.title = title
        self.onDismiss = onDismiss
        self.content = content
    }

    var body: some View {
        VStack(alignment: .leading, spacing: 12) {
            HStack {
                Text(title)
                    .font(.headline)
                Spacer()
                if let onDismiss {
                    Button(action: onDismiss) {
                        Image(systemName: "xmark.circle.fill")
                            .foregroundStyle(.secondary)
                    }
                    .buttonStyle(.plain)
                }
            }

            Divider()

            content()
        }
        .tlaCard()
    }
}

// MARK: - File Row Components

/// A file row with icon, name, unsaved indicator, and close button
struct OpenFileRowView: View {
    let file: TLAFile
    let isSelected: Bool
    let onClose: () -> Void

    var body: some View {
        HStack {
            Image(systemName: file.type.iconName)
                .foregroundStyle(file.type.color)

            Text(file.name)

            Spacer()

            if file.hasUnsavedChanges {
                Circle()
                    .fill(.orange)
                    .frame(width: 6, height: 6)
            }

            Button(action: onClose) {
                Image(systemName: "xmark")
                    .font(.caption)
                    .foregroundStyle(.secondary)
            }
            .buttonStyle(.plain)
        }
    }
}

// MARK: - Badge Components

/// A status badge with icon, label, and color (capsule style)
struct TLABadge: View {
    let icon: String
    let label: String
    let color: Color

    var body: some View {
        HStack(spacing: 4) {
            Image(systemName: icon)
            Text(label)
        }
        .font(.caption)
        .padding(.horizontal, 8)
        .padding(.vertical, 4)
        .background(color.opacity(0.2))
        .foregroundStyle(color)
        .clipShape(Capsule())
    }
}

/// A filter chip button
struct FilterChipView: View {
    let title: String
    var icon: String? = nil
    var color: Color = .accentColor
    let isSelected: Bool
    let action: () -> Void

    var body: some View {
        Button(action: action) {
            HStack(spacing: 4) {
                if let icon {
                    Image(systemName: icon)
                        .font(.caption)
                }
                Text(title)
                    .font(.caption)
            }
            .padding(.horizontal, 10)
            .padding(.vertical, 6)
            .background(isSelected ? color.opacity(0.2) : Color.clear)
            .foregroundStyle(isSelected ? color : .secondary)
            .clipShape(Capsule())
            .overlay(
                Capsule()
                    .stroke(isSelected ? color : Color.secondary.opacity(0.3), lineWidth: 1)
            )
        }
        .buttonStyle(.plain)
    }
}

// MARK: - Previews

#Preview("Variable Pair") {
    VStack {
        VariablePairView(key: "x", value: "42")
        VariablePairView(key: "counter", value: "100", keyColor: .blue)
    }
    .padding()
}

#Preview("Detail Panel") {
    DetailPanel(title: "State Details", onDismiss: {}) {
        VStack(alignment: .leading) {
            VariablePairView(key: "x", value: "1")
            VariablePairView(key: "y", value: "2")
        }
    }
    .padding()
}

#Preview("Badges") {
    VStack(spacing: 12) {
        TLABadge(icon: "checkmark.circle", label: "Success", color: .green)
        TLABadge(icon: "xmark.circle", label: "Error", color: .red)
        TLABadge(icon: "clock", label: "Running", color: .orange)
    }
}

#Preview("Filter Chips") {
    HStack {
        FilterChipView(title: "All", isSelected: true, action: {})
        FilterChipView(title: "Errors", icon: "exclamationmark.triangle", color: .red, isSelected: false, action: {})
    }
    .padding()
}
