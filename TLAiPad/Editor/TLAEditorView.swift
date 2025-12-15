import SwiftUI

struct TLAEditorView: View {
    @Binding var file: TLAFile
    @ObservedObject private var settings = AppSettings.shared

    var body: some View {
        #if os(macOS)
        macOSEditor
        #else
        iOSEditor
        #endif
    }

    // MARK: - macOS Editor (Native NSTextView)

    #if os(macOS)
    private var macOSEditor: some View {
        NativeTextEditor(
            text: $file.content,
            font: editorFont,
            onTextChange: { _ in
                file.hasUnsavedChanges = true
            }
        )
    }

    private var editorFont: NSFont {
        let size = CGFloat(settings.fontSize)
        switch settings.fontFamily {
        case "Menlo":
            return NSFont(name: "Menlo", size: size) ?? .monospacedSystemFont(ofSize: size, weight: .regular)
        case "Monaco":
            return NSFont(name: "Monaco", size: size) ?? .monospacedSystemFont(ofSize: size, weight: .regular)
        case "Courier New":
            return NSFont(name: "Courier New", size: size) ?? .monospacedSystemFont(ofSize: size, weight: .regular)
        default:
            return .monospacedSystemFont(ofSize: size, weight: .regular)
        }
    }
    #endif

    // MARK: - iOS Editor (Native UITextView with syntax highlighting)

    #if os(iOS)
    @FocusState private var isFocused: Bool

    private var iOSEditor: some View {
        iOSTextEditor(
            text: $file.content,
            fontSize: CGFloat(settings.fontSize),
            fontFamily: settings.fontFamily,
            showLineNumbers: settings.showLineNumbers,
            onChange: { _ in
                file.hasUnsavedChanges = true
            }
        )
        .toolbar {
            ToolbarItemGroup(placement: .keyboard) {
                ScrollView(.horizontal, showsIndicators: false) {
                    HStack(spacing: 12) {
                        Button(action: { insertTemplate(.conjunction) }) {
                            Text("/\\").font(.system(.body, design: .monospaced))
                        }
                        Button(action: { insertTemplate(.disjunction) }) {
                            Text("\\/").font(.system(.body, design: .monospaced))
                        }
                        Button(action: { insertTemplate(.forall) }) {
                            Text("\\A").font(.system(.body, design: .monospaced))
                        }
                        Button(action: { insertTemplate(.exists) }) {
                            Text("\\E").font(.system(.body, design: .monospaced))
                        }
                        Button(action: { insertTemplate(.elementOf) }) {
                            Text("\\in").font(.system(.body, design: .monospaced))
                        }
                        Button(action: { insertTemplate(.mapsto) }) {
                            Text("|->").font(.system(.body, design: .monospaced))
                        }
                        Button(action: { insertTemplate(.prime) }) {
                            Text("'").font(.system(.body, design: .monospaced))
                        }
                        Button(action: { insertTemplate(.implies) }) {
                            Text("=>").font(.system(.body, design: .monospaced))
                        }
                        Button(action: { insertTemplate(.always) }) {
                            Text("[]").font(.system(.body, design: .monospaced))
                        }
                        Button(action: { insertTemplate(.eventually) }) {
                            Text("<>").font(.system(.body, design: .monospaced))
                        }
                    }
                }
                Spacer()
                Button("Done") {
                    UIApplication.shared.sendAction(#selector(UIResponder.resignFirstResponder), to: nil, from: nil, for: nil)
                }
            }
        }
    }

    private func insertTemplate(_ template: TLATemplate) {
        file.content += template.text
    }
    #endif
}

// MARK: - TLA+ Templates

enum TLATemplate {
    case conjunction
    case disjunction
    case forall
    case exists
    case elementOf
    case mapsto
    case prime
    case implies
    case equivalence
    case always
    case eventually

    var text: String {
        switch self {
        case .conjunction: return " /\\ "
        case .disjunction: return " \\/ "
        case .forall: return "\\A "
        case .exists: return "\\E "
        case .elementOf: return " \\in "
        case .mapsto: return " |-> "
        case .prime: return "'"
        case .implies: return " => "
        case .equivalence: return " <=> "
        case .always: return "[]"
        case .eventually: return "<>"
        }
    }
}

#Preview {
    TLAEditorView(file: .constant(TLAFile(
        name: "Test.tla",
        type: .specification,
        content: TLATemplates.twoPhaseCommit
    )))
}
