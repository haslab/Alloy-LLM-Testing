// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 6: The station has no cycles
// All tests satisfy earlier requirements 0 through 5.
// Total wrong specifications in dataset: 20
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 17/20
// Detection ratio among parseable specifications: 0.850000 (85.00%)
// Maximum domain scope per test: 4
// Append to the trainstation declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: The station has no cycles
pred PositiveScenario1 {
    some disj t1, t2, t3, t4 : Track |
    some disj s1, s2, s3, s4 : Signal |
    {
        Track = t1 + t2 + t3 + t4
        Junction = none
        Entry = t4
        Exit = t2 + t3
        Signal = s1 + s2 + s3 + s4
        Semaphore = s3 + s4
        Speed = s1 + s2
        succs = t1->t3 + t4->t1 + t4->t2
        signals = t1->s2 + t1->s3 + t2->s4 + t4->s1
    }
}
run PositiveScenario1 for exactly 4 Track, exactly 4 Signal, 6 Int expect 1

// Violates the supplied oracle: The station has no cycles
pred NegativeScenario1 {
    some disj t1, t2, t3, t4 : Track |
    some disj s1 : Signal |
    {
        Track = t1 + t2 + t3 + t4
        Junction = t1
        Entry = t4
        Exit = t3
        Signal = s1
        Semaphore = none
        Speed = s1
        succs = t1->t2 + t1->t3 + t2->t1 + t4->t1
        signals = t4->s1
    }
}
run NegativeScenario1 for exactly 4 Track, exactly 1 Signal, 6 Int expect 0
