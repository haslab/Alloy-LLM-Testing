// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 1: Signals belong to one track
// All tests satisfy earlier requirements 0 through 0.
// Total wrong specifications in dataset: 48
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 46/48
// Detection ratio among parseable specifications: 0.958333 (95.83%)
// Maximum domain scope per test: 4
// Append to the trainstation declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Signals belong to one track
pred PositiveScenario1 {
    some disj t1, t2, t3, t4 : Track |
    some disj s1, s2, s3, s4 : Signal |
    {
        Track = t1 + t2 + t3 + t4
        Junction = none
        Entry = t3
        Exit = t2 + t3 + t4
        Signal = s1 + s2 + s3 + s4
        Semaphore = s3 + s4
        Speed = none
        succs = t4->t2 + t4->t4
        signals = t2->s1 + t2->s4 + t4->s2 + t4->s3
    }
}
run PositiveScenario1 for exactly 4 Track, exactly 4 Signal, 6 Int expect 1

// Violates the supplied oracle: Signals belong to one track
pred NegativeScenario1 {
    some disj t1, t2 : Track |
    some disj s1 : Signal |
    {
        Track = t1 + t2
        Junction = t2
        Entry = t2
        Exit = t2
        Signal = s1
        Semaphore = none
        Speed = s1
        succs = t1->t2
        signals = none->none
    }
}
run NegativeScenario1 for exactly 2 Track, exactly 1 Signal, 6 Int expect 0
