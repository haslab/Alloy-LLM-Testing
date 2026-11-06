// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 1: Every workstation has workers and every worker works in one workstation
// All tests satisfy earlier requirements 0 through 0.
// Total wrong specifications in dataset: 92
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 91/92
// Detection ratio among parseable specifications: 0.989130 (98.91%)
// Maximum domain scope per test: 4
// Append to the productionline declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Every workstation has workers and every worker works in one workstation
pred PositiveScenario1 {
    some disj w1 : Workstation |
    some disj k1, k2 : Worker |
    some disj p1, p2, p3 : Product |
    {
        Workstation = w1
        begin = w1
        end = w1
        Worker = k1 + k2
        Human = k2
        Robot = k1
        Product = p1 + p2 + p3
        Material = p1 + p2
        Component = p3
        Dangerous = p1 + p2
        workers = w1->k1 + w1->k2
        succ = none->none
        parts = none->none
        workstation = none->none
    }
}
run PositiveScenario1 for exactly 1 Workstation, exactly 2 Worker, exactly 3 Product, 6 Int expect 1

// Satisfies the supplied oracle: Every workstation has workers and every worker works in one workstation
pred PositiveScenario2 {
    some disj w1 : Workstation |
    some disj k1, k2 : Worker |
    some disj p1, p2, p3 : Product |
    {
        Workstation = w1
        begin = w1
        end = w1
        Worker = k1 + k2
        Human = none
        Robot = k1 + k2
        Product = p1 + p2 + p3
        Material = p1 + p3
        Component = p2
        Dangerous = p1 + p3
        workers = w1->k1 + w1->k2
        succ = w1->w1
        parts = none->none
        workstation = p2->w1
    }
}
run PositiveScenario2 for exactly 1 Workstation, exactly 2 Worker, exactly 3 Product, 6 Int expect 1

// Satisfies the supplied oracle: Every workstation has workers and every worker works in one workstation
pred PositiveScenario3 {
    some disj w1, w2 : Workstation |
    some disj k1, k2, k3 : Worker |
    some disj p1, p2, p3 : Product |
    {
        Workstation = w1 + w2
        begin = w1
        end = w1
        Worker = k1 + k2 + k3
        Human = none
        Robot = k1 + k2 + k3
        Product = p1 + p2 + p3
        Material = p1 + p3
        Component = p2
        Dangerous = p1 + p3
        workers = w1->k2 + w1->k3 + w2->k1
        succ = w1->w1
        parts = none->none
        workstation = p2->w2
    }
}
run PositiveScenario3 for exactly 2 Workstation, exactly 3 Worker, exactly 3 Product, 6 Int expect 1

// Satisfies the supplied oracle: Every workstation has workers and every worker works in one workstation
pred PositiveScenario4 {
    some disj w1 : Workstation |
    some disj k1, k2 : Worker |
    some disj p1, p2, p3, p4 : Product |
    {
        Workstation = w1
        begin = w1
        end = w1
        Worker = k1 + k2
        Human = none
        Robot = k1 + k2
        Product = p1 + p2 + p3 + p4
        Material = p1 + p3
        Component = p2 + p4
        Dangerous = p2 + p4
        workers = w1->k1 + w1->k2
        succ = w1->w1
        parts = none->none
        workstation = p2->w1
    }
}
run PositiveScenario4 for exactly 1 Workstation, exactly 2 Worker, exactly 4 Product, 6 Int expect 1

// Violates the supplied oracle: Every workstation has workers and every worker works in one workstation
pred NegativeScenario1 {
    some disj w1, w2 : Workstation |
    some disj k1 : Worker |
    some disj p1, p2, p3, p4 : Product |
    {
        Workstation = w1 + w2
        begin = w1
        end = w1
        Worker = k1
        Human = none
        Robot = k1
        Product = p1 + p2 + p3 + p4
        Material = p1 + p3
        Component = p2 + p4
        Dangerous = p1 + p3
        workers = w1->k1
        succ = w2->w2
        parts = none->none
        workstation = none->none
    }
}
run NegativeScenario1 for exactly 2 Workstation, exactly 1 Worker, exactly 4 Product, 6 Int expect 0

// Violates the supplied oracle: Every workstation has workers and every worker works in one workstation
pred NegativeScenario2 {
    some disj w1 : Workstation |
    some disj p1, p2, p3, p4 : Product |
    {
        Workstation = w1
        begin = w1
        end = w1
        Worker = none
        Human = none
        Robot = none
        Product = p1 + p2 + p3 + p4
        Material = p1 + p3
        Component = p2 + p4
        Dangerous = p1 + p3
        workers = none->none
        succ = none->none
        parts = none->none
        workstation = none->none
    }
}
run NegativeScenario2 for exactly 1 Workstation, exactly 0 Worker, exactly 4 Product, 6 Int expect 0

// Violates the supplied oracle: Every workstation has workers and every worker works in one workstation
pred NegativeScenario3 {
    some disj w1, w2, w3 : Workstation |
    some disj k1, k2 : Worker |
    some disj p1, p2, p3, p4 : Product |
    {
        Workstation = w1 + w2 + w3
        begin = w2
        end = w2
        Worker = k1 + k2
        Human = none
        Robot = k1 + k2
        Product = p1 + p2 + p3 + p4
        Material = p1 + p3
        Component = p2 + p4
        Dangerous = p1 + p3
        workers = w1->k2 + w2->k2 + w3->k1
        succ = w1->w1
        parts = none->none
        workstation = none->none
    }
}
run NegativeScenario3 for exactly 3 Workstation, exactly 2 Worker, exactly 4 Product, 6 Int expect 0

// Violates the supplied oracle: Every workstation has workers and every worker works in one workstation
pred NegativeScenario4 {
    some disj w1 : Workstation |
    some disj k1, k2, k3 : Worker |
    some disj p1, p2, p3, p4 : Product |
    {
        Workstation = w1
        begin = w1
        end = w1
        Worker = k1 + k2 + k3
        Human = k3
        Robot = k1 + k2
        Product = p1 + p2 + p3 + p4
        Material = p1 + p3
        Component = p2 + p4
        Dangerous = p1 + p3
        workers = w1->k2 + w1->k3
        succ = w1->w1
        parts = none->none
        workstation = none->none
    }
}
run NegativeScenario4 for exactly 1 Workstation, exactly 3 Worker, exactly 4 Product, 6 Int expect 0
