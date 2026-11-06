// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 10: Students only have grades in courses they are enrolled
// All tests satisfy earlier requirements 0 through 9.
// Total wrong specifications in dataset: 66
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 65/66
// Detection ratio among parseable specifications: 0.984848 (98.48%)
// Maximum domain scope per test: 4
// Append to the courses declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Students only have grades in courses they are enrolled
pred PositiveScenario1 {
    some disj p1, p2, p3 : Person |
    some disj c1, c2, c3, c4 : Course |
    some disj g1, g2, g3, g4 : Grade |
    {
        Person = p1 + p2 + p3
        Professor = p2 + p3
        Student = p1 + p2
        Course = c1 + c2 + c3 + c4
        Project = none
        Grade = g1 + g2 + g3 + g4
        teaches = p3->c1 + p3->c2 + p3->c3 + p3->c4
        enrolled = p1->c2 + p1->c3 + p1->c4 + p2->c1 + p2->c2
        Person <: projects = none->none
        Course <: projects = none->none
        grades = c1->p2->g1 + c1->p2->g3 + c1->p2->g4 + c2->p2->g1 + c3->p1->g2 + c3->p1->g4
        Grade <: next = g1->g3 + g2->g4 + g3->g2
    }
}
run PositiveScenario1 for exactly 3 Person, exactly 4 Course, exactly 0 Project, exactly 4 Grade, 8 Int expect 1

// Violates the supplied oracle: Students only have grades in courses they are enrolled
pred NegativeScenario1 {
    some disj p1, p2, p3, p4 : Person |
    some disj c1, c2, c3, c4 : Course |
    some disj j1, j2 : Project |
    some disj g1, g2, g3 : Grade |
    {
        Person = p1 + p2 + p3 + p4
        Professor = p1 + p4
        Student = p1 + p3
        Course = c1 + c2 + c3 + c4
        Project = j1 + j2
        Grade = g1 + g2 + g3
        teaches = p4->c1 + p4->c2 + p4->c3 + p4->c4
        enrolled = p1->c1 + p1->c3 + p1->c4 + p3->c2 + p3->c4
        Person <: projects = p1->j2 + p3->j1
        Course <: projects = c1->j2 + c2->j1
        grades = c1->p1->g1 + c2->p1->g1 + c2->p1->g2 + c2->p3->g1 + c3->p1->g2
        Grade <: next = g2->g3 + g3->g1
    }
}
run NegativeScenario1 for exactly 4 Person, exactly 4 Course, exactly 2 Project, exactly 3 Grade, 8 Int expect 0
