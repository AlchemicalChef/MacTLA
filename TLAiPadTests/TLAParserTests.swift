import XCTest
@testable import MacTLA

final class TLAParserTests: XCTestCase {

    // MARK: - Module Structure Tests

    func testParseSimpleModule() {
        let source = """
        ---- MODULE Test ----
        VARIABLES x

        Init == x = 0

        Next == x' = x + 1

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            XCTAssertEqual(module.name, "Test")
            XCTAssertEqual(module.declarations.count, 3)
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseExtends() {
        let source = """
        ---- MODULE Test ----
        EXTENDS Naturals, Sequences

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            XCTAssertEqual(module.extends, ["Naturals", "Sequences"])
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseConstants() {
        let source = """
        ---- MODULE Test ----
        CONSTANTS N, M

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            let constantDecl = module.declarations.first { decl in
                if case .constant = decl { return true }
                return false
            }
            XCTAssertNotNil(constantDecl)
            if case .constant(let decl) = constantDecl {
                XCTAssertEqual(decl.names, ["N", "M"])
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    // MARK: - Operator Definition Tests

    func testParseOperatorWithParameters() {
        let source = """
        ---- MODULE Test ----

        Add(a, b) == a + b

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            let opDecl = module.declarations.first { decl in
                if case .operatorDef(let def) = decl {
                    return def.name == "Add"
                }
                return false
            }
            XCTAssertNotNil(opDecl)
            if case .operatorDef(let def) = opDecl {
                XCTAssertEqual(def.parameterNames, ["a", "b"])
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseHigherOrderOperator() {
        let source = """
        ---- MODULE Test ----

        Apply(F(_), x) == F(x)

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                XCTAssertEqual(def.name, "Apply")
                XCTAssertEqual(def.parameters.count, 2)
                // First param is operator with arity 1
                XCTAssertEqual(def.parameters[0].name, "F")
                XCTAssertEqual(def.parameters[0].arity, 1)
                XCTAssertTrue(def.parameters[0].isOperator)
                // Second param is value
                XCTAssertEqual(def.parameters[1].name, "x")
                XCTAssertNil(def.parameters[1].arity)
                XCTAssertFalse(def.parameters[1].isOperator)
            } else {
                XCTFail("Expected operator definition")
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseHigherOrderBinaryOperator() {
        let source = """
        ---- MODULE Test ----

        Combine(G(_, _), a, b) == G(a, b)

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                XCTAssertEqual(def.parameters[0].arity, 2)
            } else {
                XCTFail("Expected operator definition")
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    // MARK: - Quantifier Tests

    func testParseQuantifiers() {
        let source = """
        ---- MODULE Test ----

        AllPositive == \\A x \\in S : x > 0

        SomePositive == \\E x \\in S : x > 0

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            XCTAssertEqual(module.declarations.count, 2)
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseTuplePatternQuantifier() {
        let source = """
        ---- MODULE Test ----

        HasPair == \\E <<x, y>> \\in S : x + y = 10

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                if case .exists(let vars, _, _) = def.body {
                    XCTAssertEqual(vars.count, 1)
                    if case .tuple(let names) = vars[0].pattern {
                        XCTAssertEqual(names, ["x", "y"])
                    } else {
                        XCTFail("Expected tuple pattern")
                    }
                } else {
                    XCTFail("Expected exists expression")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    // MARK: - Set Tests

    func testParseSetEnumeration() {
        let source = """
        ---- MODULE Test ----

        S == {1, 2, 3}

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                if case .setEnumeration(let elements, _) = def.body {
                    XCTAssertEqual(elements.count, 3)
                } else {
                    XCTFail("Expected set enumeration")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseEmptySet() {
        let source = """
        ---- MODULE Test ----

        Empty == {}

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                if case .setEnumeration(let elements, _) = def.body {
                    XCTAssertEqual(elements.count, 0)
                } else {
                    XCTFail("Expected empty set")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseSetComprehension() {
        let source = """
        ---- MODULE Test ----

        Doubled == {x * 2 : x \\in Nat}

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                if case .setMap(_, let boundVar, _) = def.body {
                    XCTAssertEqual(boundVar.name, "x")
                } else {
                    XCTFail("Expected set map expression")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseSetRange() {
        let source = """
        ---- MODULE Test ----

        Range == 1..10

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                if case .setRange(let from, let to, _) = def.body {
                    // Verify the range bounds are correct
                    if case .number(let fromVal, _) = from {
                        XCTAssertEqual(fromVal, 1, "Expected range to start at 1")
                    } else {
                        XCTFail("Expected number for range start")
                    }
                    if case .number(let toVal, _) = to {
                        XCTAssertEqual(toVal, 10, "Expected range to end at 10")
                    } else {
                        XCTFail("Expected number for range end")
                    }
                } else {
                    XCTFail("Expected set range")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    // MARK: - Control Flow Tests

    func testParseIfThenElse() {
        let source = """
        ---- MODULE Test ----

        Max(a, b) == IF a > b THEN a ELSE b

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                XCTAssertEqual(def.name, "Max", "Expected operator name to be 'Max'")
                if case .ternary(let condition, let thenBranch, let elseBranch, _) = def.body {
                    // Verify condition is a comparison (a > b)
                    if case .binary(_, let op, _, _) = condition {
                        XCTAssertEqual(op, .gt, "Expected > operator in condition")
                    } else {
                        XCTFail("Expected binary comparison in condition")
                    }
                    // Verify then branch is identifier 'a'
                    if case .identifier(let thenName, _) = thenBranch {
                        XCTAssertEqual(thenName, "a", "Expected 'a' in then branch")
                    } else {
                        XCTFail("Expected identifier in then branch")
                    }
                    // Verify else branch is identifier 'b'
                    if case .identifier(let elseName, _) = elseBranch {
                        XCTAssertEqual(elseName, "b", "Expected 'b' in else branch")
                    } else {
                        XCTFail("Expected identifier in else branch")
                    }
                } else {
                    XCTFail("Expected IF-THEN-ELSE expression")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseCaseExpression() {
        let source = """
        ---- MODULE Test ----

        Grade(score) == CASE score >= 90 -> "A"
                          [] score >= 80 -> "B"
                          [] score >= 70 -> "C"
                          [] OTHER -> "F"

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                if case .caseExpr(let arms, let other, _) = def.body {
                    XCTAssertEqual(arms.count, 3)
                    XCTAssertNotNil(other)
                } else {
                    XCTFail("Expected CASE expression")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseCaseWithTemporalCondition() {
        // Test CASE with temporal operator in condition
        let source = """
        ---- MODULE Test ----

        Handler == CASE []P -> "always"
                     [] <>Q -> "eventually"
                     [] OTHER -> "default"

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                if case .caseExpr(let arms, let other, _) = def.body {
                    XCTAssertEqual(arms.count, 2)
                    XCTAssertNotNil(other)
                    // First arm should have always(P) as condition
                    if case .always = arms[0].condition {
                        // Success
                    } else {
                        XCTFail("Expected always expression in first arm")
                    }
                } else {
                    XCTFail("Expected CASE expression")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    // MARK: - Let-In Tests

    func testParseLetIn() {
        let source = """
        ---- MODULE Test ----

        Complex == LET x == 5
                       y == 10
                   IN x + y

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                if case .letIn(let defs, _, _) = def.body {
                    XCTAssertEqual(defs.count, 2)
                } else {
                    XCTFail("Expected LET-IN expression")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    // MARK: - Lambda Tests

    func testParseLambda() {
        let source = """
        ---- MODULE Test ----

        Inc == LAMBDA x : x + 1

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                if case .lambda(let params, _, _) = def.body {
                    XCTAssertEqual(params, ["x"])
                } else {
                    XCTFail("Expected LAMBDA expression")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseLambdaMultipleParams() {
        let source = """
        ---- MODULE Test ----

        Add == LAMBDA x, y : x + y

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                if case .lambda(let params, _, _) = def.body {
                    XCTAssertEqual(params, ["x", "y"])
                } else {
                    XCTFail("Expected LAMBDA expression")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    // MARK: - Function/Record Tests

    func testParseFunctionConstruction() {
        let source = """
        ---- MODULE Test ----

        Square == [x \\in 1..10 |-> x * x]

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                XCTAssertEqual(def.name, "Square", "Expected operator name to be 'Square'")
                if case .functionConstruction(let boundVars, let mapExpr, _) = def.body {
                    // Verify bound variable
                    XCTAssertEqual(boundVars.count, 1, "Expected 1 bound variable")
                    XCTAssertEqual(boundVars.first?.name, "x", "Expected bound variable 'x'")
                    // Verify domain is a set range
                    if let domain = boundVars.first?.domain {
                        if case .setRange = domain {
                            // Good - domain is a set range
                        } else {
                            XCTFail("Expected set range as domain")
                        }
                    } else {
                        XCTFail("Expected domain to be present")
                    }
                    // Verify mapping expression is multiplication
                    if case .binary(_, let op, _, _) = mapExpr {
                        XCTAssertEqual(op, .times, "Expected multiplication in mapping")
                    } else {
                        XCTFail("Expected binary expression in mapping")
                    }
                } else {
                    XCTFail("Expected function construction")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseRecordConstruction() {
        let source = """
        ---- MODULE Test ----

        Point == [x |-> 0, y |-> 0]

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                if case .recordConstruction(let fields, _) = def.body {
                    XCTAssertEqual(fields.count, 2)
                } else {
                    XCTFail("Expected record construction")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseRecordAccess() {
        let source = """
        ---- MODULE Test ----

        GetX(r) == r.x

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                if case .recordAccess(_, let field, _) = def.body {
                    XCTAssertEqual(field, "x")
                } else {
                    XCTFail("Expected record access")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    // MARK: - EXCEPT Tests

    func testParseExceptSimple() {
        let source = """
        ---- MODULE Test ----

        Updated == [f EXCEPT ![1] = 42]

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                if case .except(_, let clauses, _) = def.body {
                    XCTAssertEqual(clauses.count, 1)
                } else {
                    XCTFail("Expected EXCEPT expression")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseExceptMultipleClauses() {
        let source = """
        ---- MODULE Test ----

        Updated == [f EXCEPT ![1] = 42, ![2] = 43]

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                if case .except(_, let clauses, _) = def.body {
                    XCTAssertEqual(clauses.count, 2)
                } else {
                    XCTFail("Expected EXCEPT expression")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseExceptRecordField() {
        let source = """
        ---- MODULE Test ----

        Updated == [r EXCEPT !.name = "new"]

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                XCTAssertEqual(def.name, "Updated", "Expected operator name to be 'Updated'")
                if case .except(let base, let clauses, _) = def.body {
                    // Verify base is identifier 'r'
                    if case .identifier(let baseName, _) = base {
                        XCTAssertEqual(baseName, "r", "Expected base to be 'r'")
                    } else {
                        XCTFail("Expected identifier as EXCEPT base")
                    }
                    // Verify we have one clause
                    XCTAssertEqual(clauses.count, 1, "Expected 1 EXCEPT clause")
                    // Verify the new value is a string "new"
                    if case .string(let newValue, _) = clauses.first?.value {
                        XCTAssertEqual(newValue, "new", "Expected new value to be 'new'")
                    }
                } else {
                    XCTFail("Expected EXCEPT expression")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    // MARK: - Temporal Operator Tests

    func testParseAlways() {
        let source = """
        ---- MODULE Test ----

        Safety == []P

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                XCTAssertEqual(def.name, "Safety", "Expected operator name to be 'Safety'")
                if case .always(let inner, _) = def.body {
                    // Verify inner expression is identifier 'P'
                    if case .identifier(let innerName, _) = inner {
                        XCTAssertEqual(innerName, "P", "Expected inner expression to be 'P'")
                    } else {
                        XCTFail("Expected identifier inside always")
                    }
                } else {
                    XCTFail("Expected always expression")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseEventually() {
        let source = """
        ---- MODULE Test ----

        Liveness == <>Q

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                XCTAssertEqual(def.name, "Liveness", "Expected operator name to be 'Liveness'")
                if case .eventually(let inner, _) = def.body {
                    // Verify inner expression is identifier 'Q'
                    if case .identifier(let innerName, _) = inner {
                        XCTAssertEqual(innerName, "Q", "Expected inner expression to be 'Q'")
                    } else {
                        XCTFail("Expected identifier inside eventually")
                    }
                } else {
                    XCTFail("Expected eventually expression")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseLeadsto() {
        let source = """
        ---- MODULE Test ----

        Progress == P ~> Q

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                XCTAssertEqual(def.name, "Progress", "Expected operator name to be 'Progress'")
                if case .leadsto(let left, let right, _) = def.body {
                    // Verify left is identifier 'P'
                    if case .identifier(let leftName, _) = left {
                        XCTAssertEqual(leftName, "P", "Expected left side to be 'P'")
                    } else {
                        XCTFail("Expected identifier on left of leadsto")
                    }
                    // Verify right is identifier 'Q'
                    if case .identifier(let rightName, _) = right {
                        XCTAssertEqual(rightName, "Q", "Expected right side to be 'Q'")
                    } else {
                        XCTFail("Expected identifier on right of leadsto")
                    }
                } else {
                    XCTFail("Expected leadsto expression")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseStuttering() {
        let source = """
        ---- MODULE Test ----

        Spec == [Next]_vars

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                XCTAssertEqual(def.name, "Spec", "Expected operator name to be 'Spec'")
                if case .stuttering(let action, let subscriptExpr, _) = def.body {
                    // Verify action is identifier 'Next'
                    if case .identifier(let actionName, _) = action {
                        XCTAssertEqual(actionName, "Next", "Expected action to be 'Next'")
                    } else {
                        XCTFail("Expected identifier for action")
                    }
                    // Verify subscript is identifier 'vars'
                    if case .identifier(let subName, _) = subscriptExpr {
                        XCTAssertEqual(subName, "vars", "Expected subscript to be 'vars'")
                    } else {
                        XCTFail("Expected identifier for subscript")
                    }
                } else {
                    XCTFail("Expected stuttering expression")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseStutteringWithTupleSubscript() {
        let source = """
        ---- MODULE Test ----

        Spec == [Next]_<<x, y>>

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                if case .stuttering(_, let subscriptExpr, _) = def.body {
                    if case .tuple = subscriptExpr {
                        // Success
                    } else {
                        XCTFail("Expected tuple subscript")
                    }
                } else {
                    XCTFail("Expected stuttering expression")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseAction() {
        let source = """
        ---- MODULE Test ----

        StrongSpec == <<Next>>_vars

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                XCTAssertEqual(def.name, "StrongSpec", "Expected operator name to be 'StrongSpec'")
                if case .action(let actionExpr, let subscriptExpr, _) = def.body {
                    // Verify action is a tuple containing 'Next' (<<Next>> is parsed as tuple)
                    if case .tuple(let elements, _) = actionExpr {
                        XCTAssertEqual(elements.count, 1, "Expected tuple with one element")
                        if let first = elements.first, case .identifier(let actionName, _) = first {
                            XCTAssertEqual(actionName, "Next", "Expected action to be 'Next'")
                        } else {
                            XCTFail("Expected identifier 'Next' inside tuple")
                        }
                    } else {
                        XCTFail("Expected tuple for action expression (<<Next>> is a tuple)")
                    }
                    // Verify subscript is identifier 'vars'
                    if case .identifier(let subName, _) = subscriptExpr {
                        XCTAssertEqual(subName, "vars", "Expected subscript to be 'vars'")
                    } else {
                        XCTFail("Expected identifier for subscript")
                    }
                } else {
                    XCTFail("Expected action expression")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseWeakFairness() {
        let source = """
        ---- MODULE Test ----

        Fairness == WF_vars(Next)

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                XCTAssertEqual(def.name, "Fairness", "Expected operator name to be 'Fairness'")
                if case .weakFairness(let subscriptExpr, let action, _) = def.body {
                    // Verify subscript is identifier 'vars'
                    if case .identifier(let subName, _) = subscriptExpr {
                        XCTAssertEqual(subName, "vars", "Expected subscript to be 'vars'")
                    } else {
                        XCTFail("Expected identifier for subscript")
                    }
                    // Verify action is identifier 'Next'
                    if case .identifier(let actionName, _) = action {
                        XCTAssertEqual(actionName, "Next", "Expected action to be 'Next'")
                    } else {
                        XCTFail("Expected identifier for action")
                    }
                } else {
                    XCTFail("Expected weak fairness expression")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseStrongFairness() {
        let source = """
        ---- MODULE Test ----

        Fairness == SF_vars(Next)

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                XCTAssertEqual(def.name, "Fairness", "Expected operator name to be 'Fairness'")
                if case .strongFairness(let subscriptExpr, let action, _) = def.body {
                    // Verify subscript is identifier 'vars'
                    if case .identifier(let subName, _) = subscriptExpr {
                        XCTAssertEqual(subName, "vars", "Expected subscript to be 'vars'")
                    } else {
                        XCTFail("Expected identifier for subscript")
                    }
                    // Verify action is identifier 'Next'
                    if case .identifier(let actionName, _) = action {
                        XCTAssertEqual(actionName, "Next", "Expected action to be 'Next'")
                    } else {
                        XCTFail("Expected identifier for action")
                    }
                } else {
                    XCTFail("Expected strong fairness expression")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    // MARK: - CHOOSE Tests

    func testParseChoose() {
        let source = """
        ---- MODULE Test ----

        Min == CHOOSE x \\in S : \\A y \\in S : x <= y

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                if case .choose(let bound, _, _) = def.body {
                    XCTAssertEqual(bound.name, "x")
                } else {
                    XCTFail("Expected CHOOSE expression")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    // MARK: - Tuple Tests

    func testParseTuple() {
        let source = """
        ---- MODULE Test ----

        Point == <<1, 2, 3>>

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                if case .tuple(let elements, _) = def.body {
                    XCTAssertEqual(elements.count, 3)
                } else {
                    XCTFail("Expected tuple expression")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseEmptyTuple() {
        let source = """
        ---- MODULE Test ----

        Empty == <<>>

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                if case .tuple(let elements, _) = def.body {
                    XCTAssertEqual(elements.count, 0)
                } else {
                    XCTFail("Expected empty tuple")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    // MARK: - Error Recovery Tests

    func testParseSyntaxError() {
        let source = """
        ---- MODULE Test ----

        Incomplete ==

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success:
            XCTFail("Should have failed to parse")
        case .failure(let parseErrors):
            XCTAssertFalse(parseErrors.errors.isEmpty)
        }
    }

    func testParseMultipleErrors() {
        let source = """
        ---- MODULE Test ----

        Good == 1 + 1

        Bad ==

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success:
            XCTFail("Should have failed to parse")
        case .failure(let parseErrors):
            // Error recovery should collect at least one error
            XCTAssertGreaterThanOrEqual(parseErrors.errors.count, 1)
            // Should still have partial module
            XCTAssertNotNil(parseErrors.partialModule)
            // Partial module should have the good declaration
            if let partialModule = parseErrors.partialModule {
                let goodDecls = partialModule.declarations.filter {
                    if case .operatorDef(let def) = $0 {
                        return def.name == "Good"
                    }
                    return false
                }
                XCTAssertEqual(goodDecls.count, 1)
            }
        }
    }

    // MARK: - Unicode Operator Tests

    func testParseUnicodeOperators() {
        let source = """
        ---- MODULE Test ----

        Test == ∀ x ∈ S : x ≥ 0

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                XCTAssertEqual(def.name, "Test", "Expected operator name to be 'Test'")
                if case .forall(let boundVars, let predicate, _) = def.body {
                    // Verify bound variable is 'x'
                    XCTAssertEqual(boundVars.count, 1, "Expected 1 bound variable")
                    XCTAssertEqual(boundVars.first?.name, "x", "Expected bound variable 'x'")
                    // Verify domain is identifier 'S'
                    if let domain = boundVars.first?.domain {
                        if case .identifier(let domainName, _) = domain {
                            XCTAssertEqual(domainName, "S", "Expected domain to be 'S'")
                        } else {
                            XCTFail("Expected identifier as domain")
                        }
                    }
                    // Verify predicate is a comparison (x >= 0)
                    if case .binary(_, let op, _, _) = predicate {
                        XCTAssertEqual(op, .ge, "Expected >= operator in predicate")
                    } else {
                        XCTFail("Expected binary comparison in predicate")
                    }
                } else {
                    XCTFail("Expected forall expression")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    // MARK: - Proof Tests

    func testParseTheoremWithProof() {
        let source = """
        ---- MODULE Test ----

        THEOREM Simple == 1 + 1 = 2
        PROOF OBVIOUS

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .theorem(let decl) = module.declarations.first {
                XCTAssertNotNil(decl.proof)
            } else {
                XCTFail("Expected theorem")
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    // MARK: - Complex Expression Tests

    func testParseDeeplyNested() {
        let source = """
        ---- MODULE Test ----

        Deep == IF (IF a THEN b ELSE c) THEN (IF d THEN e ELSE f) ELSE (IF g THEN h ELSE i)

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            XCTAssertEqual(module.declarations.count, 1)
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseComplexSetComprehension() {
        let source = """
        ---- MODULE Test ----

        Complex == {<<x, y>> \\in S \\X T : x < y /\\ x + y < 10}

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            XCTAssertEqual(module.declarations.count, 1)
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    // MARK: - Operator Precedence Tests

    func testOperatorPrecedence() {
        // /\ has higher precedence than \/
        let source = """
        ---- MODULE Test ----

        Test == a \\/ b /\\ c

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                // Should parse as: a \/ (b /\ c)
                if case .binary(_, let op, _, _) = def.body {
                    XCTAssertEqual(op, .or)
                } else {
                    XCTFail("Expected binary expression")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testImplicationAssociativity() {
        // => is right-associative
        let source = """
        ---- MODULE Test ----

        Test == a => b => c

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            if case .operatorDef(let def) = module.declarations.first {
                // Should parse as: a => (b => c)
                if case .binary(_, let op, let right, _) = def.body {
                    XCTAssertEqual(op, .implies)
                    if case .binary(_, let op2, _, _) = right {
                        XCTAssertEqual(op2, .implies)
                    } else {
                        XCTFail("Expected nested implication")
                    }
                } else {
                    XCTFail("Expected binary expression")
                }
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    // MARK: - SPECIFICATION/INVARIANT/PROPERTY Tests

    func testParseSpecificationDeclaration() {
        let source = """
        ---- MODULE Test ----

        Init == x = 0
        Next == x' = x + 1
        Spec == Init /\\ [][Next]_x

        SPECIFICATION Spec

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            let specDecl = module.declarations.first { decl in
                if case .specification = decl { return true }
                return false
            }
            XCTAssertNotNil(specDecl)
            if case .specification(let decl) = specDecl {
                XCTAssertEqual(decl.name, "Spec")
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseInvariantDeclaration() {
        let source = """
        ---- MODULE Test ----

        TypeOK == x \\in Nat

        INVARIANT TypeOK

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            let invDecl = module.declarations.first { decl in
                if case .invariant = decl { return true }
                return false
            }
            XCTAssertNotNil(invDecl)
            if case .invariant(let decl) = invDecl {
                XCTAssertEqual(decl.names, ["TypeOK"])
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseMultipleInvariants() {
        let source = """
        ---- MODULE Test ----

        TypeOK == x \\in Nat
        StateOK == x >= 0

        INVARIANT TypeOK, StateOK

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            let invDecl = module.declarations.first { decl in
                if case .invariant = decl { return true }
                return false
            }
            XCTAssertNotNil(invDecl)
            if case .invariant(let decl) = invDecl {
                XCTAssertEqual(decl.names, ["TypeOK", "StateOK"])
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParsePropertyDeclaration() {
        let source = """
        ---- MODULE Test ----

        Liveness == <>done

        PROPERTY Liveness

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            let propDecl = module.declarations.first { decl in
                if case .property = decl { return true }
                return false
            }
            XCTAssertNotNil(propDecl)
            if case .property(let decl) = propDecl {
                XCTAssertEqual(decl.names, ["Liveness"])
            }
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }

    func testParseCompleteSpec() {
        // Test a complete specification with SPECIFICATION, INVARIANT, and PROPERTY
        let source = """
        ---- MODULE Counter ----
        VARIABLES x

        Init == x = 0
        Next == x' = x + 1

        TypeOK == x \\in Nat
        Liveness == <>(x > 10)

        Spec == Init /\\ [][Next]_x

        SPECIFICATION Spec
        INVARIANT TypeOK
        PROPERTY Liveness

        ====
        """

        let parser = TLAParser()
        let result = parser.parse(source)

        switch result {
        case .success(let module):
            XCTAssertEqual(module.name, "Counter", "Expected module name to be 'Counter'")

            // Find and verify SPECIFICATION declaration
            let specDecl = module.declarations.first { if case .specification = $0 { return true }; return false }
            XCTAssertNotNil(specDecl, "Should have SPECIFICATION declaration")
            if case .specification(let spec) = specDecl {
                XCTAssertEqual(spec.name, "Spec", "Expected specification name to be 'Spec'")
            }

            // Find and verify INVARIANT declaration
            let invDecl = module.declarations.first { if case .invariant = $0 { return true }; return false }
            XCTAssertNotNil(invDecl, "Should have INVARIANT declaration")
            if case .invariant(let inv) = invDecl {
                XCTAssertEqual(inv.names, ["TypeOK"], "Expected invariant name to be 'TypeOK'")
            }

            // Find and verify PROPERTY declaration
            let propDecl = module.declarations.first { if case .property = $0 { return true }; return false }
            XCTAssertNotNil(propDecl, "Should have PROPERTY declaration")
            if case .property(let prop) = propDecl {
                XCTAssertEqual(prop.names, ["Liveness"], "Expected property name to be 'Liveness'")
            }

            // Verify we have the expected operator definitions
            let operatorNames = module.declarations.compactMap { decl -> String? in
                if case .operatorDef(let def) = decl {
                    return def.name
                }
                return nil
            }
            XCTAssertTrue(operatorNames.contains("Init"), "Should have Init operator")
            XCTAssertTrue(operatorNames.contains("Next"), "Should have Next operator")
            XCTAssertTrue(operatorNames.contains("TypeOK"), "Should have TypeOK operator")
            XCTAssertTrue(operatorNames.contains("Liveness"), "Should have Liveness operator")
            XCTAssertTrue(operatorNames.contains("Spec"), "Should have Spec operator")
        case .failure(let parseErrors):
            XCTFail("Parse failed: \(parseErrors.errors)")
        }
    }
}
