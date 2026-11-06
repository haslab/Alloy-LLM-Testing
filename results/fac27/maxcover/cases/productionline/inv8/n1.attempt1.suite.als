// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 7: Dangerous components cannot be assembled by humans
// All tests satisfy earlier requirements 0 through 6.
// Total wrong specifications in dataset: 78
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 75/78
// Detection ratio among parseable specifications: 0.961538 (96.15%)
// Maximum domain scope per test: 4
// Append to the productionline declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Dangerous components cannot be assembled by humans
pred PositiveScenario1 {
    some disj w1, w2, w3, w4 : Workstation |
    some disj k1, k2, k3, k4 : Worker |
    some disj p1, p2, p3, p4 : Product |
    {
        Workstation = w1 + w2 + w3 + w4
        begin = w4
        end = w2
        Worker = k1 + k2 + k3 + k4
        Human = k3 + k4
        Robot = k1 + k2
        Product = p1 + p2 + p3 + p4
        Material = p1
        Component = p2 + p3 + p4
        Dangerous = p4
        workers = w1->k2 + w2->k4 + w3->k3 + w4->k1
        succ = w3->w3 + w4->w3
        parts = p2->p1 + p3->p1 + p4->p1
        workstation = p2->w3 + p3->w4 + p4->w4
    }
}
run PositiveScenario1 for exactly 4 Workstation, exactly 4 Worker, exactly 4 Product, 6 Int expect 1

// Violates the supplied oracle: Dangerous components cannot be assembled by humans
pred NegativeScenario1 {
    some disj w1, w2, w3, w4 : Workstation |
    some disj k1, k2, k3, k4 : Worker |
    some disj p1, p2, p3, p4 : Product |
    {
        Workstation = w1 + w2 + w3 + w4
        begin = w3
        end = w3
        Worker = k1 + k2 + k3 + k4
        Human = k2 + k3 + k4
        Robot = k1
        Product = p1 + p2 + p3 + p4
        Material = p1
        Component = p2 + p3 + p4
        Dangerous = p2 + p3 + p4
        workers = w1->k3 + w2->k4 + w3->k2 + w4->k1
        succ = w2->w2 + w2->w3 + w3->w4 + w4->w2 + w4->w4
        parts = p2->p1 + p3->p1 + p4->p1
        workstation = p2->w2 + p3->w4 + p4->w4
    }
}
run NegativeScenario1 for exactly 4 Workstation, exactly 4 Worker, exactly 4 Product, 6 Int expect 0
