// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 6: The station has no cycles
// All tests satisfy earlier requirements 0 through 5.
// Total wrong specifications in dataset: 20
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 19/20
// Detection ratio among parseable specifications: 0.950000 (95.00%)
// Maximum domain scope per test: 4
// Append to the trainstation declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: The station has no cycles
pred PositiveScenario1 {
    some disj t1 : Track |
    some disj s1, s2, s3 : Signal |
    {
        Track = t1
        Junction = none
        Entry = t1
        Exit = t1
        Signal = s1 + s2 + s3
        Semaphore = s2 + s3
        Speed = s1
        succs = none->none
        signals = t1->s1 + t1->s2 + t1->s3
    }
}
run PositiveScenario1 for exactly 1 Track, exactly 3 Signal, 6 Int expect 1

// Satisfies the supplied oracle: The station has no cycles
pred PositiveScenario2 {
    some disj t1, t2, t3, t4 : Track |
    some disj s1, s2, s3, s4 : Signal |
    {
        Track = t1 + t2 + t3 + t4
        Junction = none
        Entry = t1 + t3
        Exit = t1 + t4
        Signal = s1 + s2 + s3 + s4
        Semaphore = none
        Speed = s3 + s4
        succs = t2->t4 + t3->t2
        signals = t1->s4 + t3->s1 + t3->s2 + t3->s3
    }
}
run PositiveScenario2 for exactly 4 Track, exactly 4 Signal, 6 Int expect 1

// Violates the supplied oracle: The station has no cycles
pred NegativeScenario1 {
    some disj t1, t2, t3, t4 : Track |
    some disj s1, s2, s3, s4 : Signal |
    {
        Track = t1 + t2 + t3 + t4
        Junction = none
        Entry = t4
        Exit = t4
        Signal = s1 + s2 + s3 + s4
        Semaphore = s2 + s3 + s4
        Speed = s1
        succs = t1->t2 + t2->t3 + t3->t1
        signals = t2->s4 + t3->s2 + t4->s1 + t4->s3
    }
}
run NegativeScenario1 for exactly 4 Track, exactly 4 Signal, 6 Int expect 0

// Violates the supplied oracle: The station has no cycles
pred NegativeScenario2 {
    some disj t1, t2, t3, t4 : Track |
    some disj s1, s2, s3, s4 : Signal |
    {
        Track = t1 + t2 + t3 + t4
        Junction = none
        Entry = t2
        Exit = t1 + t2
        Signal = s1 + s2 + s3 + s4
        Semaphore = s2 + s4
        Speed = s1 + s3
        succs = t3->t1 + t4->t3 + t4->t4
        signals = t2->s3 + t2->s4 + t3->s1 + t3->s2
    }
}
run NegativeScenario2 for exactly 4 Track, exactly 4 Signal, 6 Int expect 0
