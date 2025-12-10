import Foundation
import SwiftUI

struct TLAFile: Identifiable, Codable, Equatable {
    let id: UUID
    var name: String
    var type: TLAFileType
    var content: String
    var hasUnsavedChanges: Bool

    init(
        id: UUID = UUID(),
        name: String,
        type: TLAFileType,
        content: String = "",
        hasUnsavedChanges: Bool = false
    ) {
        self.id = id
        self.name = name
        self.type = type
        self.content = content
        self.hasUnsavedChanges = hasUnsavedChanges
    }

    static func == (lhs: TLAFile, rhs: TLAFile) -> Bool {
        lhs.id == rhs.id
    }
}

enum TLAFileType: String, Codable, CaseIterable {
    case specification = "tla"
    case model = "cfg"
    case pluscal = "pluscal"
    case proof = "tlaps"

    var iconName: String {
        switch self {
        case .specification: return "doc.text"
        case .model: return "gearshape.2"
        case .pluscal: return "algorithm"
        case .proof: return "checkmark.seal"
        }
    }

    var color: Color {
        switch self {
        case .specification: return .blue
        case .model: return .orange
        case .pluscal: return .purple
        case .proof: return .green
        }
    }

    var fileExtension: String {
        switch self {
        case .specification, .pluscal: return "tla"
        case .model: return "cfg"
        case .proof: return "tla"
        }
    }
}
