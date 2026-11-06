// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 4: Humans and robots cannot work together
// All tests satisfy earlier requirements 0 through 3.
// Total wrong specifications in dataset: 66
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 64/66
// Detection ratio among parseable specifications: 0.969697 (96.97%)
// Maximum domain scope per test: 4
// Append to the productionline declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Humans and robots cannot work together
pred PositiveScenario1 {
    some disj w1, w2, w3, w4 : Workstation |
    some disj k1, k2, k3, k4 : Worker |
    some disj p1, p2, p3 : Product |
    {
        Workstation = w1 + w2 + w3 + w4
        begin = w4
        end = w4
        Worker = k1 + k2 + k3 + k4
        Human = k3 + k4
        Robot = k1 + k2
        Product = p1 + p2 + p3
        Material = none
        Component = p1 + p2 + p3
        Dangerous = p3
        workers = w1->k2 + w2->k3 + w3->k1 + w4->k4
        succ = w1->w3 + w1->w4 + w2->w4 + w3->w2 + w4->w1 + w4->w4
        parts = p1->p1 + p1->p2 + p2->p1 + p3->p3
        workstation = p1->w4 + p2->w4 + p3->w3
    }
}
run PositiveScenario1 for exactly 4 Workstation, exactly 4 Worker, exactly 3 Product, 6 Int expect 1

// Violates the supplied oracle: Humans and robots cannot work together
pred NegativeScenario1 {
    some disj w1, w2, w3 : Workstation |
    some disj k1, k2, k3, k4 : Worker |
    some disj p1, p2 : Product |
    {
        Workstation = w1 + w2 + w3
        begin = w2
        end = w3
        Worker = k1 + k2 + k3 + k4
        Human = k2 + k4
        Robot = k1 + k3
        Product = p1 + p2
        Material = p2
        Component = p1
        Dangerous = p1 + p2
        workers = w1->k2 + w2->k1 + w2->k4 + w3->k3
        succ = w3->w3
        parts = p1->p1
        workstation = p1->w3
    }
}
run NegativeScenario1 for exactly 3 Workstation, exactly 4 Worker, exactly 2 Product, 6 Int expect 0
