// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 4: Only students work on projects and projects must have someone working on them
// All tests satisfy earlier requirements 0 through 3.
// Total wrong specifications in dataset: 205
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 202/205
// Detection ratio among parseable specifications: 0.985366 (98.54%)
// Maximum domain scope per test: 4
// Append to the courses declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Only students work on projects and projects must have someone working on them
pred PositiveScenario1 {
    some disj p1, p2, p3, p4 : Person |
    some disj c1 : Course |
    some disj j1, j2, j3 : Project |
    some disj g1, g2, g3 : Grade |
    {
        Person = p1 + p2 + p3 + p4
        Professor = p2 + p3 + p4
        Student = p1 + p2 + p3 + p4
        Course = c1
        Project = j1 + j2 + j3
        Grade = g1 + g2 + g3
        teaches = p2->c1
        enrolled = p1->c1
        Person <: projects = p3->j1 + p4->j2 + p4->j3
        Course <: projects = c1->j1 + c1->j2 + c1->j3
        grades = none->none->none
        Grade <: next = g2->g3 + g3->g1
    }
}
run PositiveScenario1 for exactly 4 Person, exactly 1 Course, exactly 3 Project, exactly 3 Grade, 8 Int expect 1

// Satisfies the supplied oracle: Only students work on projects and projects must have someone working on them
pred PositiveScenario2 {
    some disj p1, p2, p3, p4 : Person |
    some disj c1, c2 : Course |
    some disj j1, j2, j3, j4 : Project |
    some disj g1, g2, g3, g4 : Grade |
    {
        Person = p1 + p2 + p3 + p4
        Professor = p3
        Student = p3 + p4
        Course = c1 + c2
        Project = j1 + j2 + j3 + j4
        Grade = g1 + g2 + g3 + g4
        teaches = p3->c1 + p3->c2
        enrolled = p3->c2
        Person <: projects = p3->j2 + p3->j3 + p3->j4 + p4->j1 + p4->j2
        Course <: projects = c2->j1 + c2->j2 + c2->j3 + c2->j4
        grades = none->none->none
        Grade <: next = g2->g4 + g3->g2 + g4->g1
    }
}
run PositiveScenario2 for exactly 4 Person, exactly 2 Course, exactly 4 Project, exactly 4 Grade, 8 Int expect 1

// Violates the supplied oracle: Only students work on projects and projects must have someone working on them
pred NegativeScenario1 {
    some disj p1, p2, p3, p4 : Person |
    some disj c1 : Course |
    some disj j1, j2, j3 : Project |
    some disj g1, g2, g3, g4 : Grade |
    {
        Person = p1 + p2 + p3 + p4
        Professor = p4
        Student = p3 + p4
        Course = c1
        Project = j1 + j2 + j3
        Grade = g1 + g2 + g3 + g4
        teaches = p4->c1
        enrolled = none->none
        Person <: projects = p2->j2 + p3->j1 + p3->j2 + p4->j3
        Course <: projects = c1->j1 + c1->j2 + c1->j3
        grades = none->none->none
        Grade <: next = g1->g4 + g3->g2 + g4->g3
    }
}
run NegativeScenario1 for exactly 4 Person, exactly 1 Course, exactly 3 Project, exactly 4 Grade, 8 Int expect 0

// Violates the supplied oracle: Only students work on projects and projects must have someone working on them
pred NegativeScenario2 {
    some disj p1, p2, p3 : Person |
    some disj c1, c2 : Course |
    some disj j1, j2, j3 : Project |
    some disj g1, g2, g3, g4 : Grade |
    {
        Person = p1 + p2 + p3
        Professor = p3
        Student = p1 + p2 + p3
        Course = c1 + c2
        Project = j1 + j2 + j3
        Grade = g1 + g2 + g3 + g4
        teaches = p3->c1 + p3->c2
        enrolled = p1->c1 + p2->c2 + p3->c2
        Person <: projects = p1->j2 + p1->j3
        Course <: projects = c1->j1 + c1->j2 + c1->j3
        grades = none->none->none
        Grade <: next = g1->g4 + g3->g2 + g4->g3
    }
}
run NegativeScenario2 for exactly 3 Person, exactly 2 Course, exactly 3 Project, exactly 4 Grade, 8 Int expect 0
