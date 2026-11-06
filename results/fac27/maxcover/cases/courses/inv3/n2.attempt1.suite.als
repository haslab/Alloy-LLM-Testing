// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 2: Courses must have teachers
// All tests satisfy earlier requirements 0 through 1.
// Total wrong specifications in dataset: 65
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 65/65
// Detection ratio among parseable specifications: 1.000000 (100.00%)
// Maximum domain scope per test: 4
// Append to the courses declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Courses must have teachers
pred PositiveScenario1 {
    some disj p1 : Person |
    some disj j1, j2 : Project |
    some disj g1, g2 : Grade |
    {
        Person = p1
        Professor = p1
        Student = p1
        Course = none
        Project = j1 + j2
        Grade = g1 + g2
        teaches = none->none
        enrolled = none->none
        Person <: projects = none->none
        Course <: projects = none->none
        grades = none->none->none
        Grade <: next = g1->g2
    }
}
run PositiveScenario1 for exactly 1 Person, exactly 0 Course, exactly 2 Project, exactly 2 Grade, 8 Int expect 1

// Satisfies the supplied oracle: Courses must have teachers
pred PositiveScenario2 {
    some disj p1, p2, p3 : Person |
    some disj c1, c2, c3, c4 : Course |
    some disj j1, j2 : Project |
    some disj g1, g2 : Grade |
    {
        Person = p1 + p2 + p3
        Professor = p1 + p2 + p3
        Student = p2 + p3
        Course = c1 + c2 + c3 + c4
        Project = j1 + j2
        Grade = g1 + g2
        teaches = p1->c1 + p2->c3 + p2->c4 + p3->c2 + p3->c3
        enrolled = p2->c2
        Person <: projects = none->none
        Course <: projects = c1->j1 + c1->j2 + c2->j1 + c2->j2 + c3->j1 + c3->j2 + c4->j1 + c4->j2
        grades = none->none->none
        Grade <: next = g2->g1
    }
}
run PositiveScenario2 for exactly 3 Person, exactly 4 Course, exactly 2 Project, exactly 2 Grade, 8 Int expect 1

// Violates the supplied oracle: Courses must have teachers
pred NegativeScenario1 {
    some disj p1 : Person |
    some disj c1, c2, c3, c4 : Course |
    some disj j1, j2 : Project |
    some disj g1, g2 : Grade |
    {
        Person = p1
        Professor = p1
        Student = p1
        Course = c1 + c2 + c3 + c4
        Project = j1 + j2
        Grade = g1 + g2
        teaches = p1->c1 + p1->c2 + p1->c3
        enrolled = p1->c1 + p1->c2 + p1->c3 + p1->c4
        Person <: projects = none->none
        Course <: projects = c1->j1 + c1->j2 + c2->j1 + c2->j2 + c3->j1 + c3->j2 + c4->j1 + c4->j2
        grades = c1->p1->g1 + c1->p1->g2 + c2->p1->g1 + c2->p1->g2 + c3->p1->g1 + c3->p1->g2 + c4->p1->g1 + c4->p1->g2
        Grade <: next = g2->g1
    }
}
run NegativeScenario1 for exactly 1 Person, exactly 4 Course, exactly 2 Project, exactly 2 Grade, 8 Int expect 0

// Violates the supplied oracle: Courses must have teachers
pred NegativeScenario2 {
    some disj p1, p2, p3 : Person |
    some disj c1, c2, c3, c4 : Course |
    some disj j1, j2, j3 : Project |
    some disj g1, g2, g3, g4 : Grade |
    {
        Person = p1 + p2 + p3
        Professor = p2 + p3
        Student = p2 + p3
        Course = c1 + c2 + c3 + c4
        Project = j1 + j2 + j3
        Grade = g1 + g2 + g3 + g4
        teaches = p2->c1 + p2->c3 + p2->c4
        enrolled = none->none
        Person <: projects = none->none
        Course <: projects = c1->j2 + c1->j3 + c2->j2 + c2->j3 + c3->j2 + c3->j3 + c4->j1
        grades = none->none->none
        Grade <: next = g2->g4 + g3->g2 + g4->g1
    }
}
run NegativeScenario2 for exactly 3 Person, exactly 4 Course, exactly 3 Project, exactly 4 Grade, 8 Int expect 0
