import XCTest
@testable import MacTLA

/// Tests for TLAValue.sortKey to ensure deterministic CHOOSE behavior
final class TLAValueSortKeyTests: XCTestCase {

    // MARK: - Boolean Sort Key Tests

    func testSortKeyBooleanFalseBeforeTrue() {
        let falseKey = TLAValue.boolean(false).sortKey
        let trueKey = TLAValue.boolean(true).sortKey

        XCTAssertTrue(falseKey < trueKey)
        XCTAssertEqual(falseKey, "0_0")
        XCTAssertEqual(trueKey, "0_1")
    }

    func testSortKeyBooleanDeterministic() {
        let key1 = TLAValue.boolean(true).sortKey
        let key2 = TLAValue.boolean(true).sortKey
        XCTAssertEqual(key1, key2)
    }

    // MARK: - Integer Sort Key Tests

    func testSortKeyIntegerPositive() {
        let key = TLAValue.integer(42).sortKey
        // Format: "1_<sign>_<20-digit padded abs value>"
        XCTAssertTrue(key.hasPrefix("1_1_"))
    }

    func testSortKeyIntegerNegative() {
        let key = TLAValue.integer(-42).sortKey
        // Negatives have sign prefix "0"
        XCTAssertTrue(key.hasPrefix("1_0_"))
    }

    func testSortKeyIntegerNegativeBeforePositive() {
        let negKey = TLAValue.integer(-1).sortKey
        let posKey = TLAValue.integer(1).sortKey

        XCTAssertTrue(negKey < posKey)
    }

    func testSortKeyIntegerOrdering() {
        let keys = [-100, -10, -1, 0, 1, 10, 100].map { TLAValue.integer($0).sortKey }

        // Verify sorted order is maintained
        let sortedKeys = keys.sorted()
        XCTAssertEqual(keys, sortedKeys)
    }

    func testSortKeyIntegerLargeValues() {
        // Test large values don't overflow
        let largePos = TLAValue.integer(Int.max - 1).sortKey
        let largeNeg = TLAValue.integer(Int.min + 1).sortKey

        XCTAssertNotNil(largePos)
        XCTAssertNotNil(largeNeg)
        XCTAssertTrue(largeNeg < largePos)
    }

    func testSortKeyIntegerEdgeCases() {
        // Test edge cases
        let minKey = TLAValue.integer(Int.min).sortKey
        let maxKey = TLAValue.integer(Int.max).sortKey
        let zeroKey = TLAValue.integer(0).sortKey

        // min < 0 < max
        XCTAssertTrue(minKey < zeroKey)
        XCTAssertTrue(zeroKey < maxKey)
    }

    func testSortKeyNoOverflow() {
        // This specifically tests the fix for integer overflow
        // Previously, n + Int.max/2 could overflow
        let values = [Int.min, Int.min + 1, -1, 0, 1, Int.max - 1, Int.max]

        // Should not crash and should produce valid keys
        let keys = values.map { TLAValue.integer($0).sortKey }

        XCTAssertEqual(keys.count, 7)

        // Verify ordering is correct
        let sortedKeys = keys.sorted()
        XCTAssertEqual(keys, sortedKeys)
    }

    // MARK: - String Sort Key Tests

    func testSortKeyString() {
        let key = TLAValue.string("hello").sortKey
        XCTAssertEqual(key, "2_hello")
    }

    func testSortKeyStringOrdering() {
        let aKey = TLAValue.string("a").sortKey
        let bKey = TLAValue.string("b").sortKey
        let zKey = TLAValue.string("z").sortKey

        XCTAssertTrue(aKey < bKey)
        XCTAssertTrue(bKey < zKey)
    }

    func testSortKeyEmptyString() {
        let key = TLAValue.string("").sortKey
        XCTAssertEqual(key, "2_")
    }

    // MARK: - Set Sort Key Tests

    func testSortKeySet() {
        let set = TLAValue.set([.integer(1), .integer(2), .integer(3)])
        let key = set.sortKey
        XCTAssertTrue(key.hasPrefix("3_"))
    }

    func testSortKeySetOrdering() {
        // Sets with different elements should have different keys
        let set1 = TLAValue.set([.integer(1)])
        let set2 = TLAValue.set([.integer(2)])

        XCTAssertNotEqual(set1.sortKey, set2.sortKey)
    }

    func testSortKeyEmptySet() {
        let key = TLAValue.set([]).sortKey
        XCTAssertEqual(key, "3_")
    }

    // MARK: - Sequence Sort Key Tests

    func testSortKeySequence() {
        let seq = TLAValue.sequence([.integer(1), .integer(2)])
        let key = seq.sortKey
        XCTAssertTrue(key.hasPrefix("4_"))
    }

    func testSortKeySequenceOrdering() {
        let seq1 = TLAValue.sequence([.integer(1)])
        let seq2 = TLAValue.sequence([.integer(2)])
        let seq3 = TLAValue.sequence([.integer(1), .integer(2)])

        // Different sequences have different keys
        XCTAssertNotEqual(seq1.sortKey, seq2.sortKey)
        XCTAssertNotEqual(seq1.sortKey, seq3.sortKey)
    }

    func testSortKeyEmptySequence() {
        let key = TLAValue.sequence([]).sortKey
        XCTAssertEqual(key, "4_")
    }

    // MARK: - Record Sort Key Tests

    func testSortKeyRecord() {
        let record = TLAValue.record(["a": .integer(1), "b": .integer(2)])
        let key = record.sortKey
        XCTAssertTrue(key.hasPrefix("5_"))
    }

    func testSortKeyRecordFieldOrdering() {
        // Records with same fields in different order should have same key
        let record1 = TLAValue.record(["a": .integer(1), "b": .integer(2)])
        let record2 = TLAValue.record(["b": .integer(2), "a": .integer(1)])

        XCTAssertEqual(record1.sortKey, record2.sortKey)
    }

    func testSortKeyEmptyRecord() {
        let key = TLAValue.record([:]).sortKey
        XCTAssertEqual(key, "5_")
    }

    // MARK: - Function Sort Key Tests

    func testSortKeyFunction() {
        let func_ = TLAValue.function([.integer(1): .string("a")])
        let key = func_.sortKey
        XCTAssertTrue(key.hasPrefix("6_"))
    }

    func testSortKeyFunctionMappingOrdering() {
        // Functions with same mappings in different order should have same key
        let func1 = TLAValue.function([.integer(1): .string("a"), .integer(2): .string("b")])
        let func2 = TLAValue.function([.integer(2): .string("b"), .integer(1): .string("a")])

        XCTAssertEqual(func1.sortKey, func2.sortKey)
    }

    func testSortKeyEmptyFunction() {
        let key = TLAValue.function([:]).sortKey
        XCTAssertEqual(key, "6_")
    }

    // MARK: - Model Value Sort Key Tests

    func testSortKeyModelValue() {
        let mv = TLAValue.modelValue("m1")
        let key = mv.sortKey
        XCTAssertEqual(key, "7_m1")
    }

    func testSortKeyModelValueOrdering() {
        let mv1 = TLAValue.modelValue("a").sortKey
        let mv2 = TLAValue.modelValue("b").sortKey

        XCTAssertTrue(mv1 < mv2)
    }

    // MARK: - Type Ordering Tests

    func testSortKeyTypePrecedence() {
        // Different types should sort in order: boolean < integer < string < set < sequence < record < function < modelValue
        let boolKey = TLAValue.boolean(true).sortKey
        let intKey = TLAValue.integer(0).sortKey
        let strKey = TLAValue.string("").sortKey
        let setKey = TLAValue.set([]).sortKey
        let seqKey = TLAValue.sequence([]).sortKey
        let recKey = TLAValue.record([:]).sortKey
        let funcKey = TLAValue.function([:]).sortKey
        let mvKey = TLAValue.modelValue("x").sortKey

        let keys = [boolKey, intKey, strKey, setKey, seqKey, recKey, funcKey, mvKey]
        let sortedKeys = keys.sorted()

        XCTAssertEqual(keys, sortedKeys)
    }

    // MARK: - CHOOSE Determinism Integration Test

    func testChooseDeterminismWithSortKey() throws {
        // Test that CHOOSE returns same result due to sortKey-based sorting
        let interpreter = TLAInterpreter()
        var env = TLAInterpreter.Environment()

        // Create a set with mixed types
        let set = TLAExpression.setEnumeration([
            .number(3, .unknown),
            .number(1, .unknown),
            .number(2, .unknown)
        ], .unknown)

        let choose = TLAExpression.choose(
            BoundVariable(pattern: .single("x"), domain: set),
            .boolean(true, .unknown),
            .unknown
        )

        // Run multiple times
        var results: [TLAValue] = []
        for _ in 0..<10 {
            let result = try interpreter.evaluate(choose, in: env)
            results.append(result)
        }

        // All results should be the same
        let firstResult = results[0]
        for result in results {
            XCTAssertEqual(result, firstResult, "CHOOSE should return deterministic result")
        }
    }
}
