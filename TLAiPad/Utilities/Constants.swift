import Foundation
import SwiftUI

// MARK: - Application Constants

/// Centralized constants for the TLA+ application
enum AppConstants {
    // MARK: - Timing

    /// Delay before showing welcome sheet (nanoseconds)
    static let welcomeSheetDelay: UInt64 = 200_000_000  // 0.2 seconds

    /// Default auto-save interval in seconds
    static let defaultAutoSaveInterval: TimeInterval = 30

    // MARK: - Model Checker

    enum ModelChecker {
        /// Maximum recursion depth for expression evaluation
        static let maxRecursionDepth = 1000

        /// Default maximum states to explore
        static let defaultMaxStates = 1_000_000

        /// Default maximum depth for BFS exploration
        static let defaultMaxDepth = 100

        /// Progress update interval (states)
        static let progressUpdateInterval = 1000

        // MARK: - Simulation Mode

        /// Default number of random traces in simulation mode
        static let defaultSimulationTraceCount = 100

        /// Default max depth per trace in simulation mode
        static let defaultSimulationTraceDepth = 100

        // MARK: - Bounds for Nat/Int

        /// Upper bound for Nat set (0..natUpperBound)
        static let natUpperBound = 1000

        /// Bounds for Int set (-intBound..intBound)
        static let intBound = 1000
    }

    // MARK: - UI Configuration

    enum UI {
        /// Minimum value for max states slider
        static let minMaxStates = 1000

        /// Maximum value for max states slider
        static let maxMaxStatesSlider = 100_000_000

        /// Step size for max states slider
        static let maxStatesStep = 100_000

        /// Minimum value for max depth slider
        static let minMaxDepth = 1

        /// Maximum value for max depth slider
        static let maxMaxDepth = 10000

        /// Minimum simulation trace count
        static let minSimulationTraces = 1

        /// Maximum simulation trace count
        static let maxSimulationTraces = 10000

        /// Minimum simulation trace depth
        static let minSimulationDepth = 10

        /// Maximum simulation trace depth
        static let maxSimulationDepth = 10000

        /// Settings window size
        static let settingsWindowSize = CGSize(width: 450, height: 350)

        /// Default editor font size
        static let defaultEditorFontSize: CGFloat = 14
    }

    // MARK: - File System

    enum FileSystem {
        /// Default specification file extension
        static let specificationExtension = "tla"

        /// Configuration file extension
        static let configExtension = "cfg"

        /// Project file extension
        static let projectExtension = "tlaproject"
    }
}

// MARK: - AppStorage Keys

/// Centralized keys for UserDefaults/AppStorage
enum StorageKeys {
    static let maxStates = "modelchecker.maxStates"
    static let maxDepth = "modelchecker.maxDepth"
    static let checkDeadlock = "modelchecker.checkDeadlock"
    static let checkInvariants = "modelchecker.checkInvariants"
    static let checkProperties = "modelchecker.checkProperties"
    static let autoSave = "general.autoSave"
    static let autoSaveInterval = "general.autoSaveInterval"
    static let editorFontSize = "editor.fontSize"
    static let showLineNumbers = "editor.showLineNumbers"
    static let colorScheme = "general.colorScheme"
}
