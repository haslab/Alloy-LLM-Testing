// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 14: Students working on the same project in a course cannot have marks differing by more than one unit
// All tests satisfy earlier requirements 0 through 13.
// Total wrong specifications in dataset: 73
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 73/73
// Detection ratio among parseable specifications: 1.000000 (100.00%)
// Maximum domain scope per test: 4
// Append to the courses declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Students working on the same project in a course cannot have marks differing by more than one unit
pred PositiveScenario1 {
    some disj p1, p2, p3, p4 : Person |
    some disj c1, c2, c3, c4 : Course |
    some disj j1, j2, j3, j4 : Project |
    some disj g1, g2, g3, g4 : Grade |
    {
        Person = p1 + p2 + p3 + p4
        Professor = p2 + p3 + p4
        Student = p1 + p2 + p3 + p4
        Course = c1 + c2 + c3 + c4
        Project = j1 + j2 + j3 + j4
        Grade = g1 + g2 + g3 + g4
        teaches = p2->c4 + p3->c1 + p4->c2 + p4->c3
        enrolled = p1->c1 + p1->c3 + p1->c4 + p2->c1 + p2->c2 + p2->c3 + p3->c2 + p3->c3 + p3->c4 + p4->c1 + p4->c4
        Person <: projects = p1->j1 + p1->j2 + p1->j4 + p2->j1 + p3->j3 + p3->j4 + p4->j1 + p4->j3
        Course <: projects = c1->j1 + c3->j4 + c4->j2 + c4->j3
        grades = c1->p1->g4 + c1->p2->g1 + c2->p2->g2 + c2->p3->g2 + c3->p1->g2 + c3->p2->g1 + c3->p3->g2 + c4->p3->g4 + c4->p4->g1
        Grade <: next = g1->g4 + g2->g3 + g3->g1
    }
}
run PositiveScenario1 for exactly 4 Person, exactly 4 Course, exactly 4 Project, exactly 4 Grade, 8 Int expect 1

// Violates the supplied oracle: Students working on the same project in a course cannot have marks differing by more than one unit
pred NegativeScenario1 {
    some disj p1, p2, p3, p4 : Person |
    some disj c1, c2, c3, c4 : Course |
    some disj j1, j2, j3 : Project |
    some disj g1, g2, g3, g4 : Grade |
    {
        Person = p1 + p2 + p3 + p4
        Professor = p1 + p3 + p4
        Student = p1 + p2 + p3 + p4
        Course = c1 + c2 + c3 + c4
        Project = j1 + j2 + j3
        Grade = g1 + g2 + g3 + g4
        teaches = p1->c1 + p1->c2 + p4->c3 + p4->c4
        enrolled = p1->c3 + p1->c4 + p2->c1 + p2->c2 + p2->c3 + p3->c1 + p3->c2 + p3->c3 + p3->c4 + p4->c1 + p4->c2
        Person <: projects = p1->j1 + p1->j3 + p2->j1 + p2->j2 + p3->j3
        Course <: projects = c1->j2 + c3->j1 + c4->j3
        grades = c1->p3->g2 + c1->p4->g3 + c2->p3->g2 + c3->p1->g4 + c3->p2->g3 + c3->p3->g3 + c4->p1->g2 + c4->p3->g4
        Grade <: next = g2->g3 + g3->g4 + g4->g1
    }
}
run NegativeScenario1 for exactly 4 Person, exactly 4 Course, exactly 3 Project, exactly 4 Grade, 8 Int expect 0
