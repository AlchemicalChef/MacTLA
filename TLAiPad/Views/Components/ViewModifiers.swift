import SwiftUI

// MARK: - Text Field Modifiers

/// Applies TLA+ code input styling (no autocapitalization, no autocorrection)
struct TLACodeTextFieldModifier: ViewModifier {
    func body(content: Content) -> some View {
        content
            #if os(iOS)
            .textInputAutocapitalization(.never)
            #endif
            .autocorrectionDisabled()
    }
}

extension View {
    /// Applies TLA+ code input styling to a TextField
    func tlaCodeTextField() -> some View {
        modifier(TLACodeTextFieldModifier())
    }
}

// MARK: - Typography Modifiers

/// Applies caption styling with secondary color
struct TLACaptionModifier: ViewModifier {
    func body(content: Content) -> some View {
        content
            .font(.caption)
            .foregroundStyle(.secondary)
    }
}

/// Applies monospaced font styling
struct TLAMonospacedModifier: ViewModifier {
    let size: Font.TextStyle

    func body(content: Content) -> some View {
        content
            .font(.system(size, design: .monospaced))
    }
}

extension View {
    /// Applies caption + secondary styling
    func tlaCaption() -> some View {
        modifier(TLACaptionModifier())
    }

    /// Applies monospaced font
    func tlaMonospaced(_ size: Font.TextStyle = .body) -> some View {
        modifier(TLAMonospacedModifier(size: size))
    }
}

// MARK: - Card Modifiers

/// Applies card styling with rounded corners and material background
struct TLACardModifier: ViewModifier {
    let cornerRadius: CGFloat
    let material: Material

    func body(content: Content) -> some View {
        content
            .padding()
            .background(material)
            .clipShape(RoundedRectangle(cornerRadius: cornerRadius))
    }
}

/// Applies card styling with border
struct TLABorderedCardModifier: ViewModifier {
    let cornerRadius: CGFloat
    let fillColor: Color
    let borderColor: Color
    let borderWidth: CGFloat

    func body(content: Content) -> some View {
        content
            .background(
                RoundedRectangle(cornerRadius: cornerRadius)
                    .fill(fillColor)
            )
            .overlay(
                RoundedRectangle(cornerRadius: cornerRadius)
                    .stroke(borderColor, lineWidth: borderWidth)
            )
    }
}

extension View {
    /// Applies card styling with material background
    func tlaCard(cornerRadius: CGFloat = 12, material: Material = .ultraThickMaterial) -> some View {
        modifier(TLACardModifier(cornerRadius: cornerRadius, material: material))
    }

    /// Applies card styling with border
    func tlaBorderedCard(
        cornerRadius: CGFloat = 8,
        fillColor: Color = .clear,
        borderColor: Color = .secondary.opacity(0.3),
        borderWidth: CGFloat = 1
    ) -> some View {
        modifier(TLABorderedCardModifier(
            cornerRadius: cornerRadius,
            fillColor: fillColor,
            borderColor: borderColor,
            borderWidth: borderWidth
        ))
    }
}
