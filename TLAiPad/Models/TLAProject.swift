import Foundation

struct TLAProject: Identifiable, Codable {
    let id: UUID
    var name: String
    var path: String
    var files: [TLAFile]
    var createdAt: Date
    var modifiedAt: Date

    init(
        id: UUID = UUID(),
        name: String,
        path: String,
        files: [TLAFile] = [],
        createdAt: Date = Date(),
        modifiedAt: Date = Date()
    ) {
        self.id = id
        self.name = name
        self.path = path
        self.files = files
        self.createdAt = createdAt
        self.modifiedAt = modifiedAt
    }
}
