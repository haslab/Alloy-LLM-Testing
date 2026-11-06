// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 2: Courses must have teachers
// All tests satisfy earlier requirements 0 through 1.
// Total wrong specifications in dataset: 65
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 63/65
// Detection ratio among parseable specifications: 0.969231 (96.92%)
// Maximum domain scope per test: 4
// Append to the courses declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Courses must have teachers
pred PositiveScenario1 {
    some disj p1, p2, p3, p4 : Person |
    some disj c1, c2, c3 : Course |
    some disj j1 : Project |
    some disj g1, g2 : Grade |
    {
        Person = p1 + p2 + p3 + p4
        Professor = p1 + p2 + p3 + p4
        Student = p1 + p2 + p4
        Course = c1 + c2 + c3
        Project = j1
        Grade = g1 + g2
        teaches = p1->c3 + p2->c2 + p2->c3 + p3->c1 + p3->c2 + p4->c3
        enrolled = none->none
        Person <: projects = none->none
        Course <: projects = none->none
        grades = c2->p1->g1 + c3->p1->g1
        Grade <: next = g2->g1
    }
}
run PositiveScenario1 for exactly 4 Person, exactly 3 Course, exactly 1 Project, exactly 2 Grade, 8 Int expect 1

// Violates the supplied oracle: Courses must have teachers
pred NegativeScenario1 {
    some disj p1, p2 : Person |
    some disj c1, c2 : Course |
    some disj j1 : Project |
    some disj g1 : Grade |
    {
        Person = p1 + p2
        Professor = p1 + p2
        Student = p1 + p2
        Course = c1 + c2
        Project = j1
        Grade = g1
        teaches = p1->c1 + p2->c1
        enrolled = p1->c1 + p2->c2
        Person <: projects = p2->j1
        Course <: projects = none->none
        grades = none->none->none
        Grade <: next = none->none
    }
}
run NegativeScenario1 for exactly 2 Person, exactly 2 Course, exactly 1 Project, exactly 1 Grade, 8 Int expect 0
