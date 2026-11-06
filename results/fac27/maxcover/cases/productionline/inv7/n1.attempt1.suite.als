// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 6: Components built of dangerous parts are also dangerous
// All tests satisfy earlier requirements 0 through 5.
// Total wrong specifications in dataset: 78
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 76/78
// Detection ratio among parseable specifications: 0.974359 (97.44%)
// Maximum domain scope per test: 4
// Append to the productionline declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Components built of dangerous parts are also dangerous
pred PositiveScenario1 {
    some disj w1, w2 : Workstation |
    some disj k1, k2, k3, k4 : Worker |
    some disj p1, p2, p3, p4 : Product |
    {
        Workstation = w1 + w2
        begin = w2
        end = w1
        Worker = k1 + k2 + k3 + k4
        Human = k2 + k3 + k4
        Robot = k1
        Product = p1 + p2 + p3 + p4
        Material = p1 + p2
        Component = p3 + p4
        Dangerous = p1 + p4
        workers = w1->k2 + w1->k3 + w1->k4 + w2->k1
        succ = w1->w1 + w2->w1
        parts = p3->p2 + p4->p1 + p4->p2 + p4->p3
        workstation = p3->w1 + p4->w1
    }
}
run PositiveScenario1 for exactly 2 Workstation, exactly 4 Worker, exactly 4 Product, 6 Int expect 1

// Violates the supplied oracle: Components built of dangerous parts are also dangerous
pred NegativeScenario1 {
    some disj w1, w2, w3 : Workstation |
    some disj k1, k2, k3, k4 : Worker |
    some disj p1, p2, p3, p4 : Product |
    {
        Workstation = w1 + w2 + w3
        begin = w2
        end = w2
        Worker = k1 + k2 + k3 + k4
        Human = k1 + k4
        Robot = k2 + k3
        Product = p1 + p2 + p3 + p4
        Material = p1 + p3
        Component = p2 + p4
        Dangerous = p3 + p4
        workers = w1->k4 + w2->k2 + w2->k3 + w3->k1
        succ = w1->w1 + w1->w2 + w2->w3 + w3->w1 + w3->w3
        parts = p2->p1 + p2->p3 + p4->p2 + p4->p3
        workstation = p2->w3 + p4->w3
    }
}
run NegativeScenario1 for exactly 3 Workstation, exactly 4 Worker, exactly 4 Product, 6 Int expect 0
