# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands

```bash
# Install XcodeGen (required for project generation)
brew install xcodegen

# Generate the Xcode project (run after cloning or modifying project.yml)
xcodegen generate

# Build for macOS
xcodebuild -scheme MacTLA -destination 'platform=macOS' build

# Build for iOS (iPad)
xcodebuild -scheme TLAiPad -destination 'platform=iOS Simulator,name=iPad Pro' build

# Run all tests
xcodebuild test -scheme MacTLA -destination 'platform=macOS'

# Run a specific test class
xcodebuild test -scheme MacTLA -destination 'platform=macOS' -only-testing:MacTLATests/TLALexerTests

# Open in Xcode
open MacTLA.xcodeproj
```

## Architecture

MacTLA is a native TLA+ verification toolbox built with SwiftUI/AppKit. It follows MVVM with a clear separation between the parser/model-checker core and the UI layer.

### Core Pipeline

```
TLA+ Source → TLALexer → TLAParser → TLAModule (AST) → TLAInterpreter → ModelChecker
```

- **TLALexer** (`Parser/TLALexer.swift`): Tokenizes TLA+ source into `TLAToken` array. Handles TLA+ operators (`/\`, `\/`, `\A`, `\E`, `[]`, `<>`), module delimiters, and comments.
- **TLAParser** (`Parser/TLAParser.swift`): Recursive descent parser producing `TLAModule` AST with `TLADeclaration` and `TLAExpression` nodes. All AST types defined in this file.
- **TLAInterpreter** (`ModelChecker/TLAInterpreter.swift`): Evaluates `TLAExpression` nodes against an `Environment` containing variable bindings, constants, and operator definitions. Returns `TLAValue` (integer, boolean, set, sequence, record, function, model value).
- **ModelChecker** (`ModelChecker/ModelChecker.swift`): Swift actor performing BFS state exploration. Checks invariants, deadlock, and temporal properties (WF/SF fairness). Produces `ExplorationResult` for visualization.

### State Management

- **AppState** (`App/AppState.swift`): `@MainActor` `ObservableObject` holding `currentProject`, `openFiles`, `selectedFileId`, and `verificationResults`. Injected via `@EnvironmentObject`.
- **TLAProject/TLAFile** (`Models/`): Data models for projects and files (`.tla`, `.cfg`).
- **FileStorage** (`App/FileStorage.swift`): Handles file persistence and auto-save.

### Editor Components

- **NativeTextEditor** (`Editor/NativeTextEditor.swift`): NSTextView wrapper with syntax highlighting via `TLASyntaxHighlighter`.
- **TLASyntaxHighlighter** (`Parser/TLASyntaxHighlighter.swift`): Token-based syntax coloring.
- **TLACodeCompletion** (`Editor/TLACodeCompletion.swift`): Context-aware completions.
- **TLADiagnostics** (`Editor/TLADiagnostics.swift`): Real-time error/warning reporting.

### Platform Support

The codebase targets both macOS and iOS (iPad) from shared source in `TLAiPad/`:
- macOS: Uses `NativeTextEditor` (NSTextView-based)
- iOS: Uses `iOSTextEditor` (UITextView-based)
- Platform conditionals via `#if os(macOS)` / `#if os(iOS)`

### Project Configuration

The Xcode project is generated from `project.yml` via XcodeGen. Three targets:
- **MacTLA**: macOS app
- **TLAiPad**: iOS (iPad) app
- **MacTLATests**: Unit tests for macOS

## Testing

Test files are in `TLAiPadTests/`:
- `TLALexerTests.swift`: Tokenization tests
- `TLAParserTests.swift`: AST generation tests
- `TLAInterpreterTests.swift`: Expression evaluation tests

Tests import `@testable import MacTLA` and use XCTest framework.

## TLA+ Language Notes

When working with TLA+ parsing/evaluation:
- TLA+ uses backslash operators: `\A` (forall), `\E` (exists), `\in` (element of)
- Conjunction is `/\`, disjunction is `\/`
- Temporal operators: `[]` (always), `<>` (eventually)
- Module delimiters: `----` (start), `====` (end)
- Primed variables (`x'`) represent next-state values in actions
