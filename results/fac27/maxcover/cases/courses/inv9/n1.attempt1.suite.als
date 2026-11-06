// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 8: A professor cannot teach colleagues
// All tests satisfy earlier requirements 0 through 7.
// Total wrong specifications in dataset: 152
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 152/152
// Detection ratio among parseable specifications: 1.000000 (100.00%)
// Maximum domain scope per test: 4
// Append to the courses declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: A professor cannot teach colleagues
pred PositiveScenario1 {
    some disj p1, p2, p3, p4 : Person |
    some disj c1, c2, c3, c4 : Course |
    some disj g1 : Grade |
    {
        Person = p1 + p2 + p3 + p4
        Professor = p1 + p2 + p3 + p4
        Student = p1 + p2 + p3 + p4
        Course = c1 + c2 + c3 + c4
        Project = none
        Grade = g1
        teaches = p1->c1 + p1->c2 + p2->c1 + p2->c3 + p3->c4 + p4->c2
        enrolled = p2->c4 + p3->c3 + p4->c3 + p4->c4
        Person <: projects = none->none
        Course <: projects = none->none
        grades = c4->p2->g1 + c4->p3->g1 + c4->p4->g1
        Grade <: next = none->none
    }
}
run PositiveScenario1 for exactly 4 Person, exactly 4 Course, exactly 0 Project, exactly 1 Grade, 8 Int expect 1

// Violates the supplied oracle: A professor cannot teach colleagues
pred NegativeScenario1 {
    some disj p1, p2, p3, p4 : Person |
    some disj c1, c2, c3, c4 : Course |
    some disj g1 : Grade |
    {
        Person = p1 + p2 + p3 + p4
        Professor = p1 + p2 + p3 + p4
        Student = p1 + p2 + p3 + p4
        Course = c1 + c2 + c3 + c4
        Project = none
        Grade = g1
        teaches = p1->c4 + p2->c2 + p2->c3 + p3->c1 + p3->c3 + p4->c4
        enrolled = p1->c2 + p3->c2 + p3->c4 + p4->c1
        Person <: projects = none->none
        Course <: projects = none->none
        grades = c1->p3->g1 + c2->p1->g1 + c3->p4->g1 + c4->p2->g1
        Grade <: next = none->none
    }
}
run NegativeScenario1 for exactly 4 Person, exactly 4 Course, exactly 0 Project, exactly 1 Grade, 8 Int expect 0
