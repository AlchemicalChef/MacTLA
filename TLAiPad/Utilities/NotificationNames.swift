import Foundation

// MARK: - Notification Names
// Consolidated from KeyboardShortcuts.swift, ContentView.swift, and SearchReplaceView.swift

extension Notification.Name {
    // Editor actions
    static let toggleSearch = Notification.Name("toggleSearch")
    static let showGoToLine = Notification.Name("showGoToLine")
    static let toggleComment = Notification.Name("toggleComment")
    static let saveFile = Notification.Name("saveFile")
    static let showNewFileDialog = Notification.Name("showNewFileDialog")

    // Navigation
    static let navigateToLine = Notification.Name("navigateToLine")
    static let jumpToDefinition = Notification.Name("jumpToDefinition")
    static let showSymbolNavigator = Notification.Name("showSymbolNavigator")
    static let scrollToMatch = Notification.Name("scrollToMatch")

    // Diagnostics
    static let nextDiagnostic = Notification.Name("nextDiagnostic")
    static let previousDiagnostic = Notification.Name("previousDiagnostic")

    // Verification
    static let runVerification = Notification.Name("runVerification")
    static let stopVerification = Notification.Name("stopVerification")

    // PlusCal
    static let translatePlusCal = Notification.Name("translatePlusCal")
}
