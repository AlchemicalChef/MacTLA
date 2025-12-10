# MacTLA

A feature-complete TLA+ verification toolbox for macOS, built natively in Swift.

## Overview

MacTLA brings the full TLA+ specification and model checking experience to macOS. Write, verify, and explore TLA+ specifications with a native, optimized interface.

## Features

### Model Checker
- TLC-like BFS state space exploration
- Invariant checking and deadlock detection
- Counterexample trace generation
- Weak and strong fairness checking (WF/SF)
- Async verification with cancellation support
- Detailed error reporting with suggestions

### Parser & Language Support
- Complete TLA+ lexer and recursive descent parser
- Full AST generation for modules, declarations, and expressions
- PlusCal algorithm translation to pure TLA+
- Support for all TLA+ operators (`/\`, `\/`, `\A`, `\E`, `[]`, `<>`, etc.)
- Standard library functions (Len, Head, Tail, Append, Seq, etc.)

### Editor
- Native NSTextView-based editor with syntax highlighting
- Bracket matching with visual highlighting
- Auto-indentation for TLA+ constructs
- Context-aware code completion
- Real-time diagnostics (errors and warnings)
- Symbol navigator with Cmd+Click go-to-definition
- Search and replace with regex support
- Line numbers gutter

### Visualization
- Interactive force-directed state graph
- Pan and zoom gestures
- State inspection with variable values
- Color-coded initial and error states
- Counterexample trace viewer

### File Management
- Native macOS file dialogs (NSOpenPanel/NSSavePanel)
- Auto-save with file persistence
- Project organization with multiple files
- Support for `.tla`, `.cfg`, and `.tlaps` files
- Built-in templates (Basic, Mutex, Producer-Consumer, Two-Phase Commit, Raft)

## Screenshots

<p align="center">
  <img src="docs/screenshots/editor.png" width="800" alt="MacTLA Editor">
</p>

## Requirements

- macOS 14.0+
- Xcode 15+ (for building)
- Swift 5.9+
- XcodeGen (for project generation)

```bash
# Install XcodeGen via Homebrew
brew install xcodegen
```

## Building

```bash
# Generate the Xcode project
xcodegen generate

# Build the project
xcodebuild -scheme MacTLA -destination 'platform=macOS' build

# Build for release
xcodebuild -scheme MacTLA -configuration Release -destination 'platform=macOS'

# Open in Xcode
open MacTLA.xcodeproj
```

## Architecture

The app follows MVVM architecture with clear separation between UI and core logic:

```
TLAiPad/
├── App/                 # Entry point, state management, file I/O
├── Models/              # Data structures (Project, File, VerificationResult)
├── Parser/              # Lexer, parser, syntax highlighter, PlusCal translator
├── ModelChecker/        # State explorer and expression evaluator
├── Editor/              # Code editor, completion, diagnostics, search
├── Views/               # SwiftUI views and components
└── Utilities/           # Templates and helpers
```

### Key Components

| Component | Description |
|-----------|-------------|
| `TLALexer` | Tokenizes TLA+ source code |
| `TLAParser` | Recursive descent parser producing AST |
| `ModelChecker` | Swift actor for async state exploration |
| `TLAInterpreter` | Evaluates TLA+ expressions |
| `PlusCalTranslator` | Translates PlusCal to pure TLA+ |
| `NativeTextEditor` | NSTextView wrapper with syntax highlighting |
| `TLASyntaxHighlighter` | Token-based syntax coloring |
| `StateGraphView` | Force-directed graph visualization |

## Testing

```bash
# Run all tests
xcodebuild test -scheme MacTLA -destination 'platform=macOS'

# Run specific test suite
xcodebuild test -scheme MacTLA -destination 'platform=macOS' \
  -only-testing:MacTLATests/TLALexerTests
```

Test coverage includes:
- `TLALexerTests` - Tokenization
- `TLAParserTests` - AST generation
- `TLAInterpreterTests` - Expression evaluation

## Keyboard Shortcuts

| Shortcut | Action |
|----------|--------|
| ⌘N | New Specification |
| ⌘O | Open File |
| ⌘S | Save File |
| ⌘W | Close File |
| ⌘F | Find |
| ⌘⌥F | Find and Replace |
| ⌘R | Run Model Checker |
| ⌘. | Stop Verification |
| ⌘G | Go to Line |
| ⌘/ | Toggle Comment |
| ⌘⇧O | Show Symbol Navigator |

## Contributing

Contributions are welcome! Please feel free to submit issues and pull requests.

## License

MIT License - see [LICENSE](LICENSE) for details.

## Acknowledgments

- Inspired by the [TLA+ Toolbox](https://lamport.azurewebsites.net/tla/toolbox.html) by Leslie Lamport
- Built with SwiftUI and AppKit for native macOS performance
