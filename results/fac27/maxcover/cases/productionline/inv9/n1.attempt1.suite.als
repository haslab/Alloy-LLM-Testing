// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 8: The workstations form a single line between begin and end
// All tests satisfy earlier requirements 0 through 7.
// Total wrong specifications in dataset: 647
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 479/647
// Detection ratio among parseable specifications: 0.740340 (74.03%)
// Maximum domain scope per test: 4
// Append to the productionline declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: The workstations form a single line between begin and end
pred PositiveScenario1 {
    some disj w1, w2, w3, w4 : Workstation |
    some disj k1, k2, k3, k4 : Worker |
    some disj p1, p2, p3 : Product |
    {
        Workstation = w1 + w2 + w3 + w4
        begin = w4
        end = w3
        Worker = k1 + k2 + k3 + k4
        Human = k2 + k3 + k4
        Robot = k1
        Product = p1 + p2 + p3
        Material = p1 + p2
        Component = p3
        Dangerous = none
        workers = w1->k2 + w2->k4 + w3->k3 + w4->k1
        succ = w1->w3 + w2->w1 + w4->w2
        parts = p3->p1
        workstation = p3->w4
    }
}
run PositiveScenario1 for exactly 4 Workstation, exactly 4 Worker, exactly 3 Product, 6 Int expect 1

// Violates the supplied oracle: The workstations form a single line between begin and end
pred NegativeScenario1 {
    some disj w1, w2, w3, w4 : Workstation |
    some disj k1, k2, k3, k4 : Worker |
    some disj p1, p2 : Product |
    {
        Workstation = w1 + w2 + w3 + w4
        begin = w3
        end = w2
        Worker = k1 + k2 + k3 + k4
        Human = k3 + k4
        Robot = k1 + k2
        Product = p1 + p2
        Material = p1
        Component = p2
        Dangerous = p1 + p2
        workers = w1->k2 + w2->k3 + w3->k4 + w4->k1
        succ = w1->w4 + w3->w2 + w4->w1
        parts = p2->p1
        workstation = p2->w4
    }
}
run NegativeScenario1 for exactly 4 Workstation, exactly 4 Worker, exactly 2 Product, 6 Int expect 0
