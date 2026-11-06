// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 2: Every component is assembled in one workstation
// All tests satisfy earlier requirements 0 through 1.
// Total wrong specifications in dataset: 31
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 31/31
// Detection ratio among parseable specifications: 1.000000 (100.00%)
// Maximum domain scope per test: 4
// Append to the productionline declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Every component is assembled in one workstation
pred PositiveScenario1 {
    some disj w1, w2, w3, w4 : Workstation |
    some disj k1, k2, k3, k4 : Worker |
    some disj p1, p2, p3, p4 : Product |
    {
        Workstation = w1 + w2 + w3 + w4
        begin = w2
        end = w3
        Worker = k1 + k2 + k3 + k4
        Human = k2 + k3 + k4
        Robot = k1
        Product = p1 + p2 + p3 + p4
        Material = p2 + p3
        Component = p1 + p4
        Dangerous = p3
        workers = w1->k2 + w2->k1 + w3->k4 + w4->k3
        succ = w1->w2 + w1->w4 + w2->w2 + w2->w3 + w3->w2 + w4->w3
        parts = p1->p4 + p2->p2 + p2->p3 + p3->p1 + p3->p4 + p4->p2 + p4->p4
        workstation = p1->w1 + p4->w1
    }
}
run PositiveScenario1 for exactly 4 Workstation, exactly 4 Worker, exactly 4 Product, 6 Int expect 1

// Satisfies the supplied oracle: Every component is assembled in one workstation
pred PositiveScenario2 {
    some disj w1, w2, w3, w4 : Workstation |
    some disj k1, k2, k3, k4 : Worker |
    some disj p1, p2, p3, p4 : Product |
    {
        Workstation = w1 + w2 + w3 + w4
        begin = w4
        end = w4
        Worker = k1 + k2 + k3 + k4
        Human = k1
        Robot = k2 + k3 + k4
        Product = p1 + p2 + p3 + p4
        Material = p2 + p3
        Component = p1 + p4
        Dangerous = p3 + p4
        workers = w1->k2 + w2->k4 + w3->k1 + w4->k3
        succ = w1->w4 + w2->w1 + w2->w2 + w2->w4 + w3->w3 + w4->w1 + w4->w2
        parts = p1->p2 + p1->p4 + p2->p2 + p2->p3 + p3->p1 + p3->p4 + p4->p2 + p4->p4
        workstation = p1->w3 + p4->w1
    }
}
run PositiveScenario2 for exactly 4 Workstation, exactly 4 Worker, exactly 4 Product, 6 Int expect 1

// Violates the supplied oracle: Every component is assembled in one workstation
pred NegativeScenario1 {
    some disj w1, w2, w3, w4 : Workstation |
    some disj k1, k2, k3, k4 : Worker |
    some disj p1, p2, p3, p4 : Product |
    {
        Workstation = w1 + w2 + w3 + w4
        begin = w3
        end = w2
        Worker = k1 + k2 + k3 + k4
        Human = none
        Robot = k1 + k2 + k3 + k4
        Product = p1 + p2 + p3 + p4
        Material = p1
        Component = p2 + p3 + p4
        Dangerous = p1 + p3
        workers = w1->k1 + w2->k2 + w3->k4 + w4->k3
        succ = w1->w1 + w1->w3 + w2->w4 + w3->w1 + w3->w3 + w4->w2
        parts = p1->p2 + p1->p4 + p2->p2 + p2->p3 + p3->p1 + p3->p4 + p4->p2 + p4->p4
        workstation = p2->w1 + p2->w2 + p2->w3 + p2->w4 + p3->w3 + p3->w4 + p4->w4
    }
}
run NegativeScenario1 for exactly 4 Workstation, exactly 4 Worker, exactly 4 Product, 6 Int expect 0

// Violates the supplied oracle: Every component is assembled in one workstation
pred NegativeScenario2 {
    some disj w1 : Workstation |
    some disj k1, k2, k3 : Worker |
    some disj p1, p2, p3 : Product |
    {
        Workstation = w1
        begin = w1
        end = w1
        Worker = k1 + k2 + k3
        Human = k3
        Robot = k1 + k2
        Product = p1 + p2 + p3
        Material = p2
        Component = p1 + p3
        Dangerous = p2 + p3
        workers = w1->k1 + w1->k2 + w1->k3
        succ = none->none
        parts = p1->p2 + p1->p3 + p2->p1 + p2->p2 + p2->p3 + p3->p1 + p3->p2 + p3->p3
        workstation = p1->w1
    }
}
run NegativeScenario2 for exactly 1 Workstation, exactly 3 Worker, exactly 3 Product, 6 Int expect 0
