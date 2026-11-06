// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 7: A professor cannot teach herself
// All tests satisfy earlier requirements 0 through 6.
// Total wrong specifications in dataset: 62
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 62/62
// Detection ratio among parseable specifications: 1.000000 (100.00%)
// Maximum domain scope per test: 4
// Append to the courses declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: A professor cannot teach herself
pred PositiveScenario1 {
    some disj p1 : Person |
    some disj g1, g2 : Grade |
    {
        Person = p1
        Professor = p1
        Student = p1
        Course = none
        Project = none
        Grade = g1 + g2
        teaches = none->none
        enrolled = none->none
        Person <: projects = none->none
        Course <: projects = none->none
        grades = none->none->none
        Grade <: next = g1->g2
    }
}
run PositiveScenario1 for exactly 1 Person, exactly 0 Course, exactly 0 Project, exactly 2 Grade, 8 Int expect 1

// Satisfies the supplied oracle: A professor cannot teach herself
pred PositiveScenario2 {
    some disj p1, p2 : Person |
    some disj c1, c2, c3 : Course |
    some disj j1 : Project |
    some disj g1, g2, g3, g4 : Grade |
    {
        Person = p1 + p2
        Professor = p1 + p2
        Student = p2
        Course = c1 + c2 + c3
        Project = j1
        Grade = g1 + g2 + g3 + g4
        teaches = p1->c2 + p1->c3 + p2->c1 + p2->c3
        enrolled = p2->c2
        Person <: projects = p2->j1
        Course <: projects = c2->j1
        grades = c1->p2->g1 + c1->p2->g2 + c1->p2->g3 + c1->p2->g4 + c2->p2->g1 + c2->p2->g2 + c2->p2->g3 + c2->p2->g4 + c3->p2->g1 + c3->p2->g2 + c3->p2->g4
        Grade <: next = g1->g4 + g3->g2 + g4->g3
    }
}
run PositiveScenario2 for exactly 2 Person, exactly 3 Course, exactly 1 Project, exactly 4 Grade, 8 Int expect 1

// Violates the supplied oracle: A professor cannot teach herself
pred NegativeScenario1 {
    some disj p1 : Person |
    some disj c1 : Course |
    some disj j1 : Project |
    some disj g1, g2 : Grade |
    {
        Person = p1
        Professor = p1
        Student = p1
        Course = c1
        Project = j1
        Grade = g1 + g2
        teaches = p1->c1
        enrolled = p1->c1
        Person <: projects = p1->j1
        Course <: projects = c1->j1
        grades = none->none->none
        Grade <: next = g2->g1
    }
}
run NegativeScenario1 for exactly 1 Person, exactly 1 Course, exactly 1 Project, exactly 2 Grade, 8 Int expect 0

// Violates the supplied oracle: A professor cannot teach herself
pred NegativeScenario2 {
    some disj p1, p2, p3 : Person |
    some disj c1, c2, c3, c4 : Course |
    some disj j1 : Project |
    some disj g1, g2, g3, g4 : Grade |
    {
        Person = p1 + p2 + p3
        Professor = p1 + p2 + p3
        Student = p1 + p3
        Course = c1 + c2 + c3 + c4
        Project = j1
        Grade = g1 + g2 + g3 + g4
        teaches = p1->c1 + p1->c2 + p1->c4 + p2->c2 + p2->c4 + p3->c1 + p3->c2 + p3->c3 + p3->c4
        enrolled = p1->c2 + p1->c3 + p1->c4 + p3->c2 + p3->c4
        Person <: projects = p1->j1
        Course <: projects = c3->j1
        grades = c2->p1->g1 + c2->p1->g2 + c2->p1->g3 + c2->p1->g4 + c2->p2->g2 + c2->p2->g3 + c2->p2->g4 + c3->p2->g1 + c3->p2->g2 + c3->p2->g3 + c3->p2->g4 + c4->p2->g2 + c4->p2->g3 + c4->p2->g4
        Grade <: next = g2->g3 + g3->g1 + g4->g2
    }
}
run NegativeScenario2 for exactly 3 Person, exactly 4 Course, exactly 1 Project, exactly 4 Grade, 8 Int expect 0
