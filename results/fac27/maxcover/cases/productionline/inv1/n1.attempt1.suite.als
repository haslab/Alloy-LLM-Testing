// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 0: Workers are either human or robots
// Total wrong specifications in dataset: 50
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 49/50
// Detection ratio among parseable specifications: 0.980000 (98.00%)
// Maximum domain scope per test: 4
// Append to the productionline declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Workers are either human or robots
pred PositiveScenario1 {
    some disj w1, w2, w3, w4 : Workstation |
    some disj k1, k2, k3, k4 : Worker |
    some disj p1, p2, p3 : Product |
    {
        Workstation = w1 + w2 + w3 + w4
        begin = w3
        end = w3
        Worker = k1 + k2 + k3 + k4
        Human = k2 + k3
        Robot = k1 + k4
        Product = p1 + p2 + p3
        Material = p3
        Component = p1 + p2
        Dangerous = p1 + p3
        workers = w1->k3 + w4->k1 + w4->k3 + w4->k4
        succ = w1->w1 + w2->w2 + w2->w4 + w3->w1 + w3->w3 + w4->w3
        parts = p1->p1 + p3->p3
        workstation = none->none
    }
}
run PositiveScenario1 for exactly 4 Workstation, exactly 4 Worker, exactly 3 Product, 6 Int expect 1

// Violates the supplied oracle: Workers are either human or robots
pred NegativeScenario1 {
    some disj w1 : Workstation |
    some disj k1, k2, k3, k4 : Worker |
    some disj p1, p2, p3, p4 : Product |
    {
        Workstation = w1
        begin = w1
        end = w1
        Worker = k1 + k2 + k3 + k4
        Human = k4
        Robot = k1 + k3
        Product = p1 + p2 + p3 + p4
        Material = p1 + p2
        Component = p3 + p4
        Dangerous = p2 + p4
        workers = w1->k4
        succ = w1->w1
        parts = p1->p1 + p1->p3 + p2->p4 + p3->p2 + p3->p3 + p4->p1
        workstation = none->none
    }
}
run NegativeScenario1 for exactly 1 Workstation, exactly 4 Worker, exactly 4 Product, 6 Int expect 0
