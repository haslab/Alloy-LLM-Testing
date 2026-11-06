// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 9: The parts of a component must be assembled before it in the production line
// All tests satisfy earlier requirements 0 through 8.
// Total wrong specifications in dataset: 89
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 85/89
// Detection ratio among parseable specifications: 0.955056 (95.51%)
// Maximum domain scope per test: 4
// Append to the productionline declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: The parts of a component must be assembled before it in the production line
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
        Dangerous = none
        workers = w1->k4 + w2->k2 + w3->k1 + w4->k3
        succ = w1->w3 + w3->w2 + w4->w1
        parts = p2->p1 + p3->p2 + p3->p4 + p4->p1
        workstation = p2->w1 + p3->w3 + p4->w4
    }
}
run PositiveScenario1 for exactly 4 Workstation, exactly 4 Worker, exactly 4 Product, 6 Int expect 1

// Violates the supplied oracle: The parts of a component must be assembled before it in the production line
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
        Material = p2
        Component = p1 + p3 + p4
        Dangerous = p1 + p4
        workers = w1->k2 + w2->k3 + w3->k1 + w4->k4
        succ = w1->w2 + w3->w4 + w4->w1
        parts = p1->p3 + p1->p4 + p3->p2 + p4->p2
        workstation = p1->w4 + p3->w1 + p4->w3
    }
}
run NegativeScenario1 for exactly 4 Workstation, exactly 4 Worker, exactly 4 Product, 6 Int expect 0
