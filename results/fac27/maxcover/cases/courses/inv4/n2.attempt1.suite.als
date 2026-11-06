// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 3: Projects are proposed by one course
// All tests satisfy earlier requirements 0 through 2.
// Total wrong specifications in dataset: 86
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 85/86
// Detection ratio among parseable specifications: 0.988372 (98.84%)
// Maximum domain scope per test: 4
// Append to the courses declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Projects are proposed by one course
pred PositiveScenario1 {
    some disj p1 : Person |
    some disj c1 : Course |
    some disj j1, j2 : Project |
    some disj g1, g2, g3 : Grade |
    {
        Person = p1
        Professor = p1
        Student = p1
        Course = c1
        Project = j1 + j2
        Grade = g1 + g2 + g3
        teaches = p1->c1
        enrolled = none->none
        Person <: projects = p1->j1 + p1->j2
        Course <: projects = c1->j1 + c1->j2
        grades = none->none->none
        Grade <: next = g2->g3 + g3->g1
    }
}
run PositiveScenario1 for exactly 1 Person, exactly 1 Course, exactly 2 Project, exactly 3 Grade, 8 Int expect 1

// Satisfies the supplied oracle: Projects are proposed by one course
pred PositiveScenario2 {
    some disj p1, p2 : Person |
    some disj c1, c2, c3, c4 : Course |
    some disj j1, j2, j3 : Project |
    some disj g1, g2, g3, g4 : Grade |
    {
        Person = p1 + p2
        Professor = p1 + p2
        Student = p1
        Course = c1 + c2 + c3 + c4
        Project = j1 + j2 + j3
        Grade = g1 + g2 + g3 + g4
        teaches = p1->c3 + p1->c4 + p2->c1 + p2->c2 + p2->c4
        enrolled = p1->c1 + p1->c2 + p1->c3 + p1->c4
        Person <: projects = p1->j1 + p2->j1 + p2->j2
        Course <: projects = c2->j1 + c2->j3 + c4->j2
        grades = none->none->none
        Grade <: next = g1->g4 + g2->g1 + g3->g2
    }
}
run PositiveScenario2 for exactly 2 Person, exactly 4 Course, exactly 3 Project, exactly 4 Grade, 8 Int expect 1

// Violates the supplied oracle: Projects are proposed by one course
pred NegativeScenario1 {
    some disj p1 : Person |
    some disj c1, c2, c3, c4 : Course |
    some disj j1, j2, j3, j4 : Project |
    some disj g1, g2, g3, g4 : Grade |
    {
        Person = p1
        Professor = p1
        Student = p1
        Course = c1 + c2 + c3 + c4
        Project = j1 + j2 + j3 + j4
        Grade = g1 + g2 + g3 + g4
        teaches = p1->c1 + p1->c2 + p1->c3 + p1->c4
        enrolled = p1->c1 + p1->c2 + p1->c3 + p1->c4
        Person <: projects = p1->j2 + p1->j3 + p1->j4
        Course <: projects = c3->j4 + c4->j2 + c4->j3
        grades = none->none->none
        Grade <: next = g1->g4 + g2->g3 + g4->g2
    }
}
run NegativeScenario1 for exactly 1 Person, exactly 4 Course, exactly 4 Project, exactly 4 Grade, 8 Int expect 0

// Violates the supplied oracle: Projects are proposed by one course
pred NegativeScenario2 {
    some disj p1, p2 : Person |
    some disj c1, c2, c3, c4 : Course |
    some disj j1, j2 : Project |
    some disj g1, g2, g3, g4 : Grade |
    {
        Person = p1 + p2
        Professor = p1 + p2
        Student = p1 + p2
        Course = c1 + c2 + c3 + c4
        Project = j1 + j2
        Grade = g1 + g2 + g3 + g4
        teaches = p1->c1 + p1->c2 + p1->c3 + p2->c4
        enrolled = p1->c1 + p1->c2 + p2->c1 + p2->c2 + p2->c3
        Person <: projects = p2->j1
        Course <: projects = c1->j1 + c1->j2 + c2->j2 + c3->j2
        grades = none->none->none
        Grade <: next = g2->g3 + g3->g1 + g4->g2
    }
}
run NegativeScenario2 for exactly 2 Person, exactly 4 Course, exactly 2 Project, exactly 4 Grade, 8 Int expect 0
