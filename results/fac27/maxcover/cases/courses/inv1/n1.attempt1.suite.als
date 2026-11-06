// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 0: Only students can be enrolled in courses
// Total wrong specifications in dataset: 166
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 164/166
// Detection ratio among parseable specifications: 0.987952 (98.80%)
// Maximum domain scope per test: 4
// Append to the courses declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Only students can be enrolled in courses
pred PositiveScenario1 {
    some disj p1, p2, p3, p4 : Person |
    some disj c1, c2, c3, c4 : Course |
    some disj j1 : Project |
    some disj g1, g2, g3, g4 : Grade |
    {
        Person = p1 + p2 + p3 + p4
        Professor = p3 + p4
        Student = p1 + p2 + p3
        Course = c1 + c2 + c3 + c4
        Project = j1
        Grade = g1 + g2 + g3 + g4
        teaches = p1->c1 + p1->c3 + p1->c4 + p3->c3 + p4->c4
        enrolled = p1->c3 + p1->c4 + p3->c3
        Person <: projects = p1->j1 + p2->j1 + p3->j1 + p4->j1
        Course <: projects = c1->j1 + c2->j1 + c3->j1 + c4->j1
        grades = c1->p1->g1 + c1->p1->g3 + c1->p2->g2 + c1->p2->g4 + c1->p3->g1 + c1->p3->g3 + c1->p4->g3 + c1->p4->g4 + c2->p3->g3 + c3->p2->g4 + c3->p3->g2 + c3->p4->g2 + c4->p4->g1
        Grade <: next = g2->g4 + g3->g1 + g4->g3
    }
}
run PositiveScenario1 for exactly 4 Person, exactly 4 Course, exactly 1 Project, exactly 4 Grade, 8 Int expect 1

// Violates the supplied oracle: Only students can be enrolled in courses
pred NegativeScenario1 {
    some disj p1, p2, p3, p4 : Person |
    some disj c1, c2, c3, c4 : Course |
    some disj j1 : Project |
    some disj g1, g2, g3, g4 : Grade |
    {
        Person = p1 + p2 + p3 + p4
        Professor = p2 + p4
        Student = p2 + p4
        Course = c1 + c2 + c3 + c4
        Project = j1
        Grade = g1 + g2 + g3 + g4
        teaches = p1->c2 + p3->c1 + p4->c2
        enrolled = p1->c2 + p4->c2
        Person <: projects = p2->j1 + p3->j1
        Course <: projects = c1->j1 + c2->j1 + c3->j1 + c4->j1
        grades = c1->p2->g3 + c1->p3->g3
        Grade <: next = g1->g2 + g2->g3 + g3->g4
    }
}
run NegativeScenario1 for exactly 4 Person, exactly 4 Course, exactly 1 Project, exactly 4 Grade, 8 Int expect 0
