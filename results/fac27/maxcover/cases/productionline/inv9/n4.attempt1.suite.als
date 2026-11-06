// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 8: The workstations form a single line between begin and end
// All tests satisfy earlier requirements 0 through 7.
// Total wrong specifications in dataset: 647
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 624/647
// Detection ratio among parseable specifications: 0.964451 (96.45%)
// Maximum domain scope per test: 4
// Append to the productionline declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: The workstations form a single line between begin and end
pred PositiveScenario1 {
    some disj w1, w2 : Workstation |
    some disj k1, k2, k3, k4 : Worker |
    some disj p1, p2 : Product |
    {
        Workstation = w1 + w2
        begin = w2
        end = w1
        Worker = k1 + k2 + k3 + k4
        Human = k2 + k3 + k4
        Robot = k1
        Product = p1 + p2
        Material = p1 + p2
        Component = none
        Dangerous = p1
        workers = w1->k1 + w2->k2 + w2->k3 + w2->k4
        succ = w2->w1
        parts = none->none
        workstation = none->none
    }
}
run PositiveScenario1 for exactly 2 Workstation, exactly 4 Worker, exactly 2 Product, 6 Int expect 1

// Satisfies the supplied oracle: The workstations form a single line between begin and end
pred PositiveScenario2 {
    some disj w1 : Workstation |
    some disj k1 : Worker |
    some disj p1, p2, p3 : Product |
    {
        Workstation = w1
        begin = w1
        end = w1
        Worker = k1
        Human = k1
        Robot = none
        Product = p1 + p2 + p3
        Material = p1 + p2 + p3
        Component = none
        Dangerous = p1 + p2
        workers = w1->k1
        succ = none->none
        parts = none->none
        workstation = none->none
    }
}
run PositiveScenario2 for exactly 1 Workstation, exactly 1 Worker, exactly 3 Product, 6 Int expect 1

// Satisfies the supplied oracle: The workstations form a single line between begin and end
pred PositiveScenario3 {
    some disj w1, w2, w3, w4 : Workstation |
    some disj k1, k2, k3, k4 : Worker |
    some disj p1, p2, p3 : Product |
    {
        Workstation = w1 + w2 + w3 + w4
        begin = w1
        end = w4
        Worker = k1 + k2 + k3 + k4
        Human = k1 + k3 + k4
        Robot = k2
        Product = p1 + p2 + p3
        Material = p1 + p2 + p3
        Component = none
        Dangerous = p1 + p2
        workers = w1->k2 + w2->k1 + w3->k3 + w4->k4
        succ = w1->w2 + w2->w3 + w3->w4
        parts = none->none
        workstation = none->none
    }
}
run PositiveScenario3 for exactly 4 Workstation, exactly 4 Worker, exactly 3 Product, 6 Int expect 1

// Satisfies the supplied oracle: The workstations form a single line between begin and end
pred PositiveScenario4 {
    some disj w1, w2 : Workstation |
    some disj k1, k2, k3 : Worker |
    some disj p1, p2, p3 : Product |
    {
        Workstation = w1 + w2
        begin = w1
        end = w2
        Worker = k1 + k2 + k3
        Human = k1 + k2 + k3
        Robot = none
        Product = p1 + p2 + p3
        Material = p1 + p2 + p3
        Component = none
        Dangerous = p1 + p3
        workers = w1->k2 + w2->k1 + w2->k3
        succ = w1->w2
        parts = none->none
        workstation = none->none
    }
}
run PositiveScenario4 for exactly 2 Workstation, exactly 3 Worker, exactly 3 Product, 6 Int expect 1

// Violates the supplied oracle: The workstations form a single line between begin and end
pred NegativeScenario1 {
    some disj w1, w2, w3, w4 : Workstation |
    some disj k1, k2, k3, k4 : Worker |
    some disj p1, p2 : Product |
    {
        Workstation = w1 + w2 + w3 + w4
        begin = w3
        end = w1
        Worker = k1 + k2 + k3 + k4
        Human = k2 + k3 + k4
        Robot = k1
        Product = p1 + p2
        Material = p1 + p2
        Component = none
        Dangerous = p2
        workers = w1->k3 + w2->k1 + w3->k4 + w4->k2
        succ = w2->w4 + w3->w1 + w3->w2 + w4->w1
        parts = none->none
        workstation = none->none
    }
}
run NegativeScenario1 for exactly 4 Workstation, exactly 4 Worker, exactly 2 Product, 6 Int expect 0

// Violates the supplied oracle: The workstations form a single line between begin and end
pred NegativeScenario2 {
    some disj w1, w2, w3, w4 : Workstation |
    some disj k1, k2, k3, k4 : Worker |
    some disj p1, p2 : Product |
    {
        Workstation = w1 + w2 + w3 + w4
        begin = w3
        end = w1
        Worker = k1 + k2 + k3 + k4
        Human = k1 + k3 + k4
        Robot = k2
        Product = p1 + p2
        Material = p1 + p2
        Component = none
        Dangerous = p1
        workers = w1->k1 + w2->k3 + w3->k2 + w4->k4
        succ = w2->w3 + w3->w1 + w4->w2
        parts = none->none
        workstation = none->none
    }
}
run NegativeScenario2 for exactly 4 Workstation, exactly 4 Worker, exactly 2 Product, 6 Int expect 0

// Violates the supplied oracle: The workstations form a single line between begin and end
pred NegativeScenario3 {
    some disj w1, w2, w3, w4 : Workstation |
    some disj k1, k2, k3, k4 : Worker |
    some disj p1, p2, p3 : Product |
    {
        Workstation = w1 + w2 + w3 + w4
        begin = w2
        end = w4
        Worker = k1 + k2 + k3 + k4
        Human = k2
        Robot = k1 + k3 + k4
        Product = p1 + p2 + p3
        Material = p1 + p2 + p3
        Component = none
        Dangerous = p2 + p3
        workers = w1->k1 + w2->k3 + w3->k2 + w4->k4
        succ = w1->w3 + w2->w4 + w3->w1
        parts = none->none
        workstation = none->none
    }
}
run NegativeScenario3 for exactly 4 Workstation, exactly 4 Worker, exactly 3 Product, 6 Int expect 0

// Violates the supplied oracle: The workstations form a single line between begin and end
pred NegativeScenario4 {
    some disj w1, w2, w3 : Workstation |
    some disj k1, k2, k3, k4 : Worker |
    some disj p1, p2, p3 : Product |
    {
        Workstation = w1 + w2 + w3
        begin = w1
        end = w3
        Worker = k1 + k2 + k3 + k4
        Human = k1 + k2 + k4
        Robot = k3
        Product = p1 + p2 + p3
        Material = p1
        Component = p2 + p3
        Dangerous = none
        workers = w1->k1 + w2->k3 + w3->k2 + w3->k4
        succ = w1->w3 + w2->w1 + w3->w2
        parts = p2->p3 + p3->p1
        workstation = p2->w2 + p3->w2
    }
}
run NegativeScenario4 for exactly 3 Workstation, exactly 4 Worker, exactly 3 Product, 6 Int expect 0
