// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 3: Projects are proposed by one course
// All tests satisfy earlier requirements 0 through 2.
// Total wrong specifications in dataset: 86
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 86/86
// Detection ratio among parseable specifications: 1.000000 (100.00%)
// Maximum domain scope per test: 4
// Append to the courses declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Projects are proposed by one course
pred PositiveScenario1 {
    some disj p1, p2 : Person |
    some disj c1 : Course |
    some disj j1, j2 : Project |
    some disj g1, g2, g3 : Grade |
    {
        Person = p1 + p2
        Professor = p1
        Student = p1
        Course = c1
        Project = j1 + j2
        Grade = g1 + g2 + g3
        teaches = p1->c1
        enrolled = p1->c1
        Person <: projects = none->none
        Course <: projects = c1->j1 + c1->j2
        grades = none->none->none
        Grade <: next = g1->g2 + g3->g1
    }
}
run PositiveScenario1 for exactly 2 Person, exactly 1 Course, exactly 2 Project, exactly 3 Grade, 8 Int expect 1

// Satisfies the supplied oracle: Projects are proposed by one course
pred PositiveScenario2 {
    some disj p1, p2 : Person |
    some disj c1, c2, c3 : Course |
    some disj j1, j2, j3, j4 : Project |
    some disj g1, g2, g3, g4 : Grade |
    {
        Person = p1 + p2
        Professor = p1 + p2
        Student = p1 + p2
        Course = c1 + c2 + c3
        Project = j1 + j2 + j3 + j4
        Grade = g1 + g2 + g3 + g4
        teaches = p1->c1 + p1->c2 + p1->c3 + p2->c2
        enrolled = p1->c1 + p1->c2 + p1->c3
        Person <: projects = p1->j2 + p1->j4 + p2->j3
        Course <: projects = c1->j1 + c1->j4 + c2->j3 + c3->j2
        grades = none->none->none
        Grade <: next = g2->g3 + g3->g1 + g4->g2
    }
}
run PositiveScenario2 for exactly 2 Person, exactly 3 Course, exactly 4 Project, exactly 4 Grade, 8 Int expect 1

// Satisfies the supplied oracle: Projects are proposed by one course
pred PositiveScenario3 {
    some disj p1, p2, p3 : Person |
    some disj c1, c2, c3, c4 : Course |
    some disj j1, j2 : Project |
    some disj g1, g2, g3, g4 : Grade |
    {
        Person = p1 + p2 + p3
        Professor = p1 + p2 + p3
        Student = p2 + p3
        Course = c1 + c2 + c3 + c4
        Project = j1 + j2
        Grade = g1 + g2 + g3 + g4
        teaches = p1->c1 + p1->c2 + p1->c3 + p1->c4
        enrolled = p2->c1 + p2->c2 + p2->c3 + p2->c4
        Person <: projects = p1->j1 + p1->j2
        Course <: projects = c1->j2 + c2->j1
        grades = none->none->none
        Grade <: next = g2->g1 + g3->g4 + g4->g2
    }
}
run PositiveScenario3 for exactly 3 Person, exactly 4 Course, exactly 2 Project, exactly 4 Grade, 8 Int expect 1

// Violates the supplied oracle: Projects are proposed by one course
pred NegativeScenario1 {
    some disj p1, p2, p3 : Person |
    some disj j1 : Project |
    some disj g1, g2, g3, g4 : Grade |
    {
        Person = p1 + p2 + p3
        Professor = p3
        Student = p3
        Course = none
        Project = j1
        Grade = g1 + g2 + g3 + g4
        teaches = none->none
        enrolled = none->none
        Person <: projects = none->none
        Course <: projects = none->none
        grades = none->none->none
        Grade <: next = g1->g4 + g3->g2 + g4->g3
    }
}
run NegativeScenario1 for exactly 3 Person, exactly 0 Course, exactly 1 Project, exactly 4 Grade, 8 Int expect 0

// Violates the supplied oracle: Projects are proposed by one course
pred NegativeScenario2 {
    some disj p1, p2 : Person |
    some disj c1 : Course |
    some disj j1, j2, j3, j4 : Project |
    some disj g1, g2, g3, g4 : Grade |
    {
        Person = p1 + p2
        Professor = p2
        Student = p2
        Course = c1
        Project = j1 + j2 + j3 + j4
        Grade = g1 + g2 + g3 + g4
        teaches = p2->c1
        enrolled = none->none
        Person <: projects = p2->j1 + p2->j2 + p2->j4
        Course <: projects = c1->j1 + c1->j2 + c1->j4
        grades = none->none->none
        Grade <: next = g2->g1 + g3->g2 + g4->g3
    }
}
run NegativeScenario2 for exactly 2 Person, exactly 1 Course, exactly 4 Project, exactly 4 Grade, 8 Int expect 0

// Violates the supplied oracle: Projects are proposed by one course
pred NegativeScenario3 {
    some disj p1, p2, p3 : Person |
    some disj c1, c2, c3, c4 : Course |
    some disj j1, j2, j3 : Project |
    some disj g1, g2, g3, g4 : Grade |
    {
        Person = p1 + p2 + p3
        Professor = p1 + p2 + p3
        Student = p2 + p3
        Course = c1 + c2 + c3 + c4
        Project = j1 + j2 + j3
        Grade = g1 + g2 + g3 + g4
        teaches = p1->c4 + p3->c1 + p3->c2 + p3->c3
        enrolled = p2->c1 + p2->c2 + p2->c3
        Person <: projects = p1->j2 + p1->j3 + p2->j3 + p3->j2
        Course <: projects = c1->j1 + c1->j2 + c2->j1 + c2->j2 + c3->j1 + c3->j3
        grades = none->none->none
        Grade <: next = g1->g4 + g3->g1 + g4->g2
    }
}
run NegativeScenario3 for exactly 3 Person, exactly 4 Course, exactly 3 Project, exactly 4 Grade, 8 Int expect 0
