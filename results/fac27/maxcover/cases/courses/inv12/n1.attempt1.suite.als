// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 11: Students have at most one grade per course
// All tests satisfy earlier requirements 0 through 10.
// Total wrong specifications in dataset: 54
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 54/54
// Detection ratio among parseable specifications: 1.000000 (100.00%)
// Maximum domain scope per test: 4
// Append to the courses declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Students have at most one grade per course
pred PositiveScenario1 {
    some disj p1, p2, p3 : Person |
    some disj c1, c2, c3 : Course |
    some disj g1, g2, g3, g4 : Grade |
    {
        Person = p1 + p2 + p3
        Professor = p2 + p3
        Student = p1 + p2 + p3
        Course = c1 + c2 + c3
        Project = none
        Grade = g1 + g2 + g3 + g4
        teaches = p2->c1 + p2->c2 + p2->c3
        enrolled = p1->c2 + p1->c3 + p3->c1 + p3->c2 + p3->c3
        Person <: projects = none->none
        Course <: projects = none->none
        grades = c1->p3->g3 + c2->p1->g1 + c2->p3->g4 + c3->p3->g4
        Grade <: next = g1->g4 + g2->g3 + g4->g2
    }
}
run PositiveScenario1 for exactly 3 Person, exactly 3 Course, exactly 0 Project, exactly 4 Grade, 8 Int expect 1

// Violates the supplied oracle: Students have at most one grade per course
pred NegativeScenario1 {
    some disj p1, p2 : Person |
    some disj c1 : Course |
    some disj g1, g2 : Grade |
    {
        Person = p1 + p2
        Professor = p2
        Student = p1 + p2
        Course = c1
        Project = none
        Grade = g1 + g2
        teaches = p2->c1
        enrolled = p1->c1
        Person <: projects = none->none
        Course <: projects = none->none
        grades = c1->p1->g1 + c1->p1->g2
        Grade <: next = g2->g1
    }
}
run NegativeScenario1 for exactly 2 Person, exactly 1 Course, exactly 0 Project, exactly 2 Grade, 8 Int expect 0
