// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 1: Only professors can teach courses
// All tests satisfy earlier requirements 0 through 0.
// Total wrong specifications in dataset: 34
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 33/34
// Detection ratio among parseable specifications: 0.970588 (97.06%)
// Maximum domain scope per test: 4
// Append to the courses declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Only professors can teach courses
pred PositiveScenario1 {
    some disj p1, p2, p3 : Person |
    some disj c1, c2 : Course |
    some disj j1 : Project |
    some disj g1, g2, g3 : Grade |
    {
        Person = p1 + p2 + p3
        Professor = p2 + p3
        Student = p1 + p3
        Course = c1 + c2
        Project = j1
        Grade = g1 + g2 + g3
        teaches = p2->c2
        enrolled = p3->c1 + p3->c2
        Person <: projects = none->none
        Course <: projects = c1->j1 + c2->j1
        grades = c1->p3->g1 + c1->p3->g2 + c1->p3->g3
        Grade <: next = g1->g3 + g2->g1
    }
}
run PositiveScenario1 for exactly 3 Person, exactly 2 Course, exactly 1 Project, exactly 3 Grade, 8 Int expect 1

// Violates the supplied oracle: Only professors can teach courses
pred NegativeScenario1 {
    some disj p1, p2 : Person |
    some disj c1, c2 : Course |
    some disj j1 : Project |
    some disj g1 : Grade |
    {
        Person = p1 + p2
        Professor = none
        Student = p2
        Course = c1 + c2
        Project = j1
        Grade = g1
        teaches = p1->c2
        enrolled = none->none
        Person <: projects = p2->j1
        Course <: projects = none->none
        grades = none->none->none
        Grade <: next = none->none
    }
}
run NegativeScenario1 for exactly 2 Person, exactly 2 Course, exactly 1 Project, exactly 1 Grade, 8 Int expect 0
