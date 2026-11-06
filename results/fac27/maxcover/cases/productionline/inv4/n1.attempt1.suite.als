// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 3: Components must have parts and materials have no parts
// All tests satisfy earlier requirements 0 through 2.
// Total wrong specifications in dataset: 85
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 78/85
// Detection ratio among parseable specifications: 0.917647 (91.76%)
// Maximum domain scope per test: 4
// Append to the productionline declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Components must have parts and materials have no parts
pred PositiveScenario1 {
    some disj w1, w2, w3, w4 : Workstation |
    some disj k1, k2, k3, k4 : Worker |
    some disj p1, p2, p3, p4 : Product |
    {
        Workstation = w1 + w2 + w3 + w4
        begin = w2
        end = w3
        Worker = k1 + k2 + k3 + k4
        Human = k3
        Robot = k1 + k2 + k4
        Product = p1 + p2 + p3 + p4
        Material = p1
        Component = p2 + p3 + p4
        Dangerous = p1 + p2 + p4
        workers = w1->k4 + w2->k3 + w3->k1 + w4->k2
        succ = w2->w2 + w3->w4 + w4->w4
        parts = p2->p3 + p2->p4 + p3->p1 + p4->p4
        workstation = p2->w1 + p3->w1 + p4->w1
    }
}
run PositiveScenario1 for exactly 4 Workstation, exactly 4 Worker, exactly 4 Product, 6 Int expect 1

// Violates the supplied oracle: Components must have parts and materials have no parts
pred NegativeScenario1 {
    some disj w1, w2 : Workstation |
    some disj k1, k2, k3, k4 : Worker |
    some disj p1, p2, p3 : Product |
    {
        Workstation = w1 + w2
        begin = w2
        end = w1
        Worker = k1 + k2 + k3 + k4
        Human = k4
        Robot = k1 + k2 + k3
        Product = p1 + p2 + p3
        Material = none
        Component = p1 + p2 + p3
        Dangerous = p2 + p3
        workers = w1->k2 + w1->k3 + w1->k4 + w2->k1
        succ = w1->w1 + w2->w1
        parts = p1->p1 + p1->p2
        workstation = p1->w2 + p2->w1 + p3->w1
    }
}
run NegativeScenario1 for exactly 2 Workstation, exactly 4 Worker, exactly 3 Product, 6 Int expect 0
