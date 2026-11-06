// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 3: Projects are proposed by one course
// All tests satisfy earlier requirements 0 through 2.
// Total wrong specifications in dataset: 86
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 84/86
// Detection ratio among parseable specifications: 0.976744 (97.67%)
// Maximum domain scope per test: 4
// Append to the courses declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Projects are proposed by one course
pred PositiveScenario1 {
    some disj p1, p2, p3 : Person |
    some disj c1, c2, c3 : Course |
    some disj j1, j2, j3 : Project |
    some disj g1 : Grade |
    {
        Person = p1 + p2 + p3
        Professor = p2 + p3
        Student = p3
        Course = c1 + c2 + c3
        Project = j1 + j2 + j3
        Grade = g1
        teaches = p2->c1 + p2->c2 + p2->c3 + p3->c2
        enrolled = none->none
        Person <: projects = p3->j1 + p3->j3
        Course <: projects = c1->j2 + c1->j3 + c2->j1
        grades = none->none->none
        Grade <: next = none->none
    }
}
run PositiveScenario1 for exactly 3 Person, exactly 3 Course, exactly 3 Project, exactly 1 Grade, 8 Int expect 1

// Violates the supplied oracle: Projects are proposed by one course
pred NegativeScenario1 {
    some disj p1 : Person |
    some disj c1, c2 : Course |
    some disj j1, j2 : Project |
    some disj g1, g2, g3 : Grade |
    {
        Person = p1
        Professor = p1
        Student = none
        Course = c1 + c2
        Project = j1 + j2
        Grade = g1 + g2 + g3
        teaches = p1->c1 + p1->c2
        enrolled = none->none
        Person <: projects = none->none
        Course <: projects = c2->j2
        grades = none->none->none
        Grade <: next = g1->g3 + g2->g1
    }
}
run NegativeScenario1 for exactly 1 Person, exactly 2 Course, exactly 2 Project, exactly 3 Grade, 8 Int expect 0
