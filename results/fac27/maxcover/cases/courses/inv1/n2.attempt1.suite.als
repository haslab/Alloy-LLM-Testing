// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 0: Only students can be enrolled in courses
// Total wrong specifications in dataset: 166
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 166/166
// Detection ratio among parseable specifications: 1.000000 (100.00%)
// Maximum domain scope per test: 4
// Append to the courses declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Only students can be enrolled in courses
pred PositiveScenario1 {
    some disj p1, p2 : Person |
    some disj c1, c2, c3, c4 : Course |
    some disj j1, j2 : Project |
    some disj g1, g2, g3 : Grade |
    {
        Person = p1 + p2
        Professor = p2
        Student = none
        Course = c1 + c2 + c3 + c4
        Project = j1 + j2
        Grade = g1 + g2 + g3
        teaches = p1->c1 + p1->c2
        enrolled = none->none
        Person <: projects = none->none
        Course <: projects = c1->j1 + c1->j2 + c2->j1 + c2->j2 + c3->j1 + c4->j1
        grades = c2->p1->g1
        Grade <: next = g1->g2 + g2->g3
    }
}
run PositiveScenario1 for exactly 2 Person, exactly 4 Course, exactly 2 Project, exactly 3 Grade, 8 Int expect 1

// Satisfies the supplied oracle: Only students can be enrolled in courses
pred PositiveScenario2 {
    some disj p1, p2, p3 : Person |
    some disj c1, c2, c3, c4 : Course |
    some disj j1, j2 : Project |
    some disj g1, g2, g3, g4 : Grade |
    {
        Person = p1 + p2 + p3
        Professor = p2
        Student = p2 + p3
        Course = c1 + c2 + c3 + c4
        Project = j1 + j2
        Grade = g1 + g2 + g3 + g4
        teaches = p2->c2 + p2->c4
        enrolled = p2->c2
        Person <: projects = none->none
        Course <: projects = c1->j1 + c1->j2 + c2->j1 + c2->j2 + c3->j1 + c3->j2
        grades = c1->p2->g1 + c1->p2->g2 + c1->p2->g3 + c1->p3->g4
        Grade <: next = g2->g4 + g3->g2 + g4->g1
    }
}
run PositiveScenario2 for exactly 3 Person, exactly 4 Course, exactly 2 Project, exactly 4 Grade, 8 Int expect 1

// Violates the supplied oracle: Only students can be enrolled in courses
pred NegativeScenario1 {
    some disj p1, p2, p3, p4 : Person |
    some disj c1, c2, c3 : Course |
    some disj j1 : Project |
    some disj g1, g2 : Grade |
    {
        Person = p1 + p2 + p3 + p4
        Professor = p2 + p4
        Student = none
        Course = c1 + c2 + c3
        Project = j1
        Grade = g1 + g2
        teaches = none->none
        enrolled = p1->c3
        Person <: projects = none->none
        Course <: projects = c1->j1 + c2->j1
        grades = none->none->none
        Grade <: next = g2->g1
    }
}
run NegativeScenario1 for exactly 4 Person, exactly 3 Course, exactly 1 Project, exactly 2 Grade, 8 Int expect 0

// Violates the supplied oracle: Only students can be enrolled in courses
pred NegativeScenario2 {
    some disj p1, p2 : Person |
    some disj c1, c2, c3 : Course |
    some disj j1 : Project |
    some disj g1, g2, g3 : Grade |
    {
        Person = p1 + p2
        Professor = p1 + p2
        Student = p1
        Course = c1 + c2 + c3
        Project = j1
        Grade = g1 + g2 + g3
        teaches = p1->c1 + p2->c1 + p2->c2 + p2->c3
        enrolled = p1->c1 + p1->c2 + p1->c3 + p2->c1 + p2->c2
        Person <: projects = none->none
        Course <: projects = c1->j1 + c2->j1
        grades = none->none->none
        Grade <: next = g2->g1 + g3->g2
    }
}
run NegativeScenario2 for exactly 2 Person, exactly 3 Course, exactly 1 Project, exactly 3 Grade, 8 Int expect 0
