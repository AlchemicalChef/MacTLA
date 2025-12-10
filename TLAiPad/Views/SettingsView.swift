import SwiftUI

/// User settings for the TLA+ toolbox
final class AppSettings: ObservableObject {
    static let shared = AppSettings()

    // Editor settings
    @AppStorage("editor.fontSize") var fontSize: Double = 14
    @AppStorage("editor.fontFamily") var fontFamily: String = "SF Mono"
    @AppStorage("editor.showLineNumbers") var showLineNumbers: Bool = true
    @AppStorage("editor.wordWrap") var wordWrap: Bool = false
    @AppStorage("editor.tabWidth") var tabWidth: Int = 4
    @AppStorage("editor.insertSpaces") var insertSpaces: Bool = true
    @AppStorage("editor.autoIndent") var autoIndent: Bool = true
    @AppStorage("editor.highlightCurrentLine") var highlightCurrentLine: Bool = true
    @AppStorage("editor.matchBrackets") var matchBrackets: Bool = true

    // Theme settings
    @AppStorage("theme.colorScheme") var colorScheme: String = "system"
    @AppStorage("theme.syntaxTheme") var syntaxTheme: String = "default"

    // Model checker settings
    @AppStorage("modelchecker.maxStates") var maxStates: Int = 100000
    @AppStorage("modelchecker.maxDepth") var maxDepth: Int = 100
    @AppStorage("modelchecker.workers") var workers: Int = 4
    @AppStorage("modelchecker.checkDeadlock") var checkDeadlock: Bool = true
    @AppStorage("modelchecker.checkLiveness") var checkLiveness: Bool = true

    // General settings
    @AppStorage("general.autoSave") var autoSave: Bool = true
    @AppStorage("general.autoSaveInterval") var autoSaveInterval: Int = 30
    @AppStorage("general.showWelcome") var showWelcome: Bool = true
    @AppStorage("general.recentFilesLimit") var recentFilesLimit: Int = 10

    private init() {}
}

struct SettingsView: View {
    @ObservedObject private var settings = AppSettings.shared
    @Environment(\.dismiss) private var dismiss

    var body: some View {
        #if os(macOS)
        TabView {
            editorTab
                .tabItem {
                    Label("Editor", systemImage: "pencil")
                }

            themeTab
                .tabItem {
                    Label("Appearance", systemImage: "paintbrush")
                }

            modelCheckerTab
                .tabItem {
                    Label("Model Checker", systemImage: "checkmark.shield")
                }

            generalTab
                .tabItem {
                    Label("General", systemImage: "gear")
                }
        }
        .frame(width: 450, height: 350)
        .padding()
        #else
        NavigationStack {
            Form {
                editorSection
                themeSection
                modelCheckerSection
                generalSection
            }
            .navigationTitle("Settings")
            .toolbar {
                ToolbarItem(placement: .confirmationAction) {
                    Button("Done") {
                        dismiss()
                    }
                }
            }
        }
        #endif
    }

    // MARK: - macOS Tabs

    #if os(macOS)
    private var editorTab: some View {
        Form {
            editorSection
        }
        .formStyle(.grouped)
    }

    private var themeTab: some View {
        Form {
            themeSection
        }
        .formStyle(.grouped)
    }

    private var modelCheckerTab: some View {
        Form {
            modelCheckerSection
        }
        .formStyle(.grouped)
    }

    private var generalTab: some View {
        Form {
            generalSection
        }
        .formStyle(.grouped)
    }
    #endif

    // MARK: - Editor Section

    private var editorSection: some View {
        Section("Editor") {
            HStack {
                Text("Font Size")
                Spacer()
                Stepper("\(Int(settings.fontSize)) pt", value: $settings.fontSize, in: 10...32, step: 1)
            }

            Picker("Font Family", selection: $settings.fontFamily) {
                Text("SF Mono").tag("SF Mono")
                Text("Menlo").tag("Menlo")
                Text("Monaco").tag("Monaco")
                Text("Courier New").tag("Courier New")
            }

            Toggle("Show Line Numbers", isOn: $settings.showLineNumbers)
            Toggle("Word Wrap", isOn: $settings.wordWrap)
            Toggle("Highlight Current Line", isOn: $settings.highlightCurrentLine)
            Toggle("Match Brackets", isOn: $settings.matchBrackets)
            Toggle("Auto Indent", isOn: $settings.autoIndent)

            HStack {
                Text("Tab Width")
                Spacer()
                Picker("", selection: $settings.tabWidth) {
                    Text("2").tag(2)
                    Text("4").tag(4)
                    Text("8").tag(8)
                }
                .pickerStyle(.segmented)
                .frame(width: 150)
            }

            Toggle("Insert Spaces", isOn: $settings.insertSpaces)
        }
    }

    // MARK: - Theme Section

    private var themeSection: some View {
        Section("Appearance") {
            Picker("Color Scheme", selection: $settings.colorScheme) {
                Text("System").tag("system")
                Text("Light").tag("light")
                Text("Dark").tag("dark")
            }

            Picker("Syntax Theme", selection: $settings.syntaxTheme) {
                Text("Default").tag("default")
                Text("Xcode").tag("xcode")
                Text("VS Code").tag("vscode")
                Text("Dracula").tag("dracula")
                Text("Solarized Light").tag("solarized-light")
                Text("Solarized Dark").tag("solarized-dark")
            }
        }
    }

    // MARK: - Model Checker Section

    private var modelCheckerSection: some View {
        Section("Model Checker") {
            HStack {
                Text("Max States")
                Spacer()
                TextField("", value: $settings.maxStates, format: .number)
                    .textFieldStyle(.roundedBorder)
                    .frame(width: 120)
            }

            HStack {
                Text("Max Depth")
                Spacer()
                TextField("", value: $settings.maxDepth, format: .number)
                    .textFieldStyle(.roundedBorder)
                    .frame(width: 120)
            }

            HStack {
                Text("Worker Threads")
                Spacer()
                Stepper("\(settings.workers)", value: $settings.workers, in: 1...16)
            }

            Toggle("Check for Deadlock", isOn: $settings.checkDeadlock)
            Toggle("Check Liveness Properties", isOn: $settings.checkLiveness)
        }
    }

    // MARK: - General Section

    private var generalSection: some View {
        Section("General") {
            Toggle("Auto Save", isOn: $settings.autoSave)

            if settings.autoSave {
                HStack {
                    Text("Auto Save Interval")
                    Spacer()
                    Picker("", selection: $settings.autoSaveInterval) {
                        Text("15 sec").tag(15)
                        Text("30 sec").tag(30)
                        Text("1 min").tag(60)
                        Text("5 min").tag(300)
                    }
                    .pickerStyle(.menu)
                    .frame(width: 100)
                }
            }

            Toggle("Show Welcome Screen", isOn: $settings.showWelcome)

            HStack {
                Text("Recent Files Limit")
                Spacer()
                Stepper("\(settings.recentFilesLimit)", value: $settings.recentFilesLimit, in: 5...50, step: 5)
            }
        }
    }
}

// MARK: - Syntax Theme Colors

struct SyntaxTheme {
    let name: String
    let background: Color
    let foreground: Color
    let keyword: Color
    let string: Color
    let comment: Color
    let number: Color
    let operator_: Color
    let identifier: Color
    let type: Color

    static let `default` = SyntaxTheme(
        name: "Default",
        background: Color(white: 0.98),
        foreground: .primary,
        keyword: .purple,
        string: .red,
        comment: Color.gray,
        number: .blue,
        operator_: .primary,
        identifier: .primary,
        type: .cyan
    )

    static let xcode = SyntaxTheme(
        name: "Xcode",
        background: .white,
        foreground: .black,
        keyword: Color(red: 0.6, green: 0.2, blue: 0.6),
        string: Color(red: 0.8, green: 0.2, blue: 0.1),
        comment: Color(red: 0.4, green: 0.5, blue: 0.4),
        number: Color(red: 0.1, green: 0.2, blue: 0.8),
        operator_: .black,
        identifier: .black,
        type: Color(red: 0.3, green: 0.5, blue: 0.6)
    )

    static let dracula = SyntaxTheme(
        name: "Dracula",
        background: Color(red: 0.16, green: 0.16, blue: 0.21),
        foreground: Color(red: 0.97, green: 0.97, blue: 0.95),
        keyword: Color(red: 1.0, green: 0.47, blue: 0.66),
        string: Color(red: 0.95, green: 0.98, blue: 0.48),
        comment: Color(red: 0.38, green: 0.45, blue: 0.53),
        number: Color(red: 0.74, green: 0.58, blue: 0.98),
        operator_: Color(red: 1.0, green: 0.47, blue: 0.66),
        identifier: Color(red: 0.97, green: 0.97, blue: 0.95),
        type: Color(red: 0.55, green: 0.93, blue: 0.99)
    )

    static func theme(named name: String) -> SyntaxTheme {
        switch name {
        case "xcode": return .xcode
        case "dracula": return .dracula
        default: return .default
        }
    }
}

// MARK: - Preview

#Preview {
    SettingsView()
}
