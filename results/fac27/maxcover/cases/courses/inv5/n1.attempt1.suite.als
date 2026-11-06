// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 4: Only students work on projects and projects must have someone working on them
// All tests satisfy earlier requirements 0 through 3.
// Total wrong specifications in dataset: 205
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 190/205
// Detection ratio among parseable specifications: 0.926829 (92.68%)
// Maximum domain scope per test: 4
// Append to the courses declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Only students work on projects and projects must have someone working on them
pred PositiveScenario1 {
    some disj p1, p2, p3, p4 : Person |
    some disj c1, c2 : Course |
    some disj j1, j2, j3 : Project |
    some disj g1, g2 : Grade |
    {
        Person = p1 + p2 + p3 + p4
        Professor = p4
        Student = p2 + p3 + p4
        Course = c1 + c2
        Project = j1 + j2 + j3
        Grade = g1 + g2
        teaches = p4->c1 + p4->c2
        enrolled = p2->c2 + p3->c2
        Person <: projects = p2->j1 + p2->j2 + p4->j1 + p4->j3
        Course <: projects = c1->j1 + c2->j2 + c2->j3
        grades = none->none->none
        Grade <: next = g2->g1
    }
}
run PositiveScenario1 for exactly 4 Person, exactly 2 Course, exactly 3 Project, exactly 2 Grade, 8 Int expect 1

// Violates the supplied oracle: Only students work on projects and projects must have someone working on them
pred NegativeScenario1 {
    some disj p1, p2, p3 : Person |
    some disj c1, c2 : Course |
    some disj j1, j2, j3 : Project |
    some disj g1, g2 : Grade |
    {
        Person = p1 + p2 + p3
        Professor = p2
        Student = p1 + p3
        Course = c1 + c2
        Project = j1 + j2 + j3
        Grade = g1 + g2
        teaches = p2->c1 + p2->c2
        enrolled = none->none
        Person <: projects = p3->j1 + p3->j3
        Course <: projects = c1->j3 + c2->j1 + c2->j2
        grades = none->none->none
        Grade <: next = g2->g1
    }
}
run NegativeScenario1 for exactly 3 Person, exactly 2 Course, exactly 3 Project, exactly 2 Grade, 8 Int expect 0
