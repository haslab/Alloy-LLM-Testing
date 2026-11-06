// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 4: Humans and robots cannot work together
// All tests satisfy earlier requirements 0 through 3.
// Total wrong specifications in dataset: 66
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 66/66
// Detection ratio among parseable specifications: 1.000000 (100.00%)
// Maximum domain scope per test: 4
// Append to the productionline declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Humans and robots cannot work together
pred PositiveScenario1 {
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
        Dangerous = p1 + p3 + p4
        workers = w1->k2 + w2->k3 + w3->k4 + w4->k1
        succ = w1->w2 + w2->w1 + w2->w3 + w3->w2 + w3->w4 + w4->w1 + w4->w3
        parts = p2->p2 + p2->p4 + p3->p1 + p3->p2 + p4->p2
        workstation = p2->w4 + p3->w2 + p4->w4
    }
}
run PositiveScenario1 for exactly 4 Workstation, exactly 4 Worker, exactly 4 Product, 6 Int expect 1

// Satisfies the supplied oracle: Humans and robots cannot work together
pred PositiveScenario2 {
    some disj w1, w2, w3 : Workstation |
    some disj k1, k2, k3, k4 : Worker |
    some disj p1, p2, p3, p4 : Product |
    {
        Workstation = w1 + w2 + w3
        begin = w2
        end = w2
        Worker = k1 + k2 + k3 + k4
        Human = k1 + k2 + k3 + k4
        Robot = none
        Product = p1 + p2 + p3 + p4
        Material = p2
        Component = p1 + p3 + p4
        Dangerous = p1 + p3
        workers = w1->k2 + w2->k1 + w3->k3 + w3->k4
        succ = w2->w2
        parts = p1->p1 + p1->p2 + p1->p3 + p1->p4 + p3->p1 + p3->p2 + p4->p1
        workstation = p1->w3 + p3->w3 + p4->w3
    }
}
run PositiveScenario2 for exactly 3 Workstation, exactly 4 Worker, exactly 4 Product, 6 Int expect 1

// Violates the supplied oracle: Humans and robots cannot work together
pred NegativeScenario1 {
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
        Material = p2 + p3
        Component = p1
        Dangerous = p2
        workers = w1->k1 + w1->k2 + w1->k3
        succ = w1->w1
        parts = p1->p1 + p1->p2 + p1->p3
        workstation = p1->w1
    }
}
run NegativeScenario1 for exactly 1 Workstation, exactly 3 Worker, exactly 3 Product, 6 Int expect 0

// Violates the supplied oracle: Humans and robots cannot work together
pred NegativeScenario2 {
    some disj w1, w2 : Workstation |
    some disj k1, k2, k3, k4 : Worker |
    some disj p1, p2, p3 : Product |
    {
        Workstation = w1 + w2
        begin = w1
        end = w2
        Worker = k1 + k2 + k3 + k4
        Human = k1 + k3
        Robot = k2 + k4
        Product = p1 + p2 + p3
        Material = p2 + p3
        Component = p1
        Dangerous = p2 + p3
        workers = w1->k3 + w2->k1 + w2->k2 + w2->k4
        succ = w1->w1
        parts = p1->p1 + p1->p2 + p1->p3
        workstation = p1->w1
    }
}
run NegativeScenario2 for exactly 2 Workstation, exactly 4 Worker, exactly 3 Product, 6 Int expect 0
