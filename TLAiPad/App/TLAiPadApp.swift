import SwiftUI

@main
struct MacTLAApp: App {
    @StateObject private var appState = AppState()
    @StateObject private var documentManager = DocumentManager()
    @ObservedObject private var settings = AppSettings.shared
    @ObservedObject private var fileStorage = FileStorage.shared

    @State private var showWelcome = false

    var body: some Scene {
        WindowGroup {
            ContentView()
                .environmentObject(appState)
                .environmentObject(documentManager)
                .sheet(isPresented: $showWelcome) {
                    WelcomeView(isPresented: $showWelcome)
                        .environmentObject(appState)
                        .environmentObject(documentManager)
                }
                .task {
                    // Small delay ensures view is ready before presenting sheet
                    if settings.showWelcome {
                        try? await Task.sleep(nanoseconds: 200_000_000) // 0.2s
                        showWelcome = true
                    }
                    fileStorage.startAutoSave(for: appState)
                }
                .onDisappear {
                    fileStorage.stopAutoSave()
                }
                .onReceive(NotificationCenter.default.publisher(for: .saveFile)) { notification in
                    if let file = notification.object as? TLAFile,
                       let project = appState.currentProject {
                        Task {
                            try? await fileStorage.saveFile(file, in: project)
                        }
                    }
                }
                .preferredColorScheme(colorScheme)
        }
        .commands {
            TLACommands(appState: appState)
        }

        #if os(macOS)
        Settings {
            SettingsView()
        }
        #endif
    }

    private var colorScheme: ColorScheme? {
        switch settings.colorScheme {
        case "light": return .light
        case "dark": return .dark
        default: return nil
        }
    }
}
