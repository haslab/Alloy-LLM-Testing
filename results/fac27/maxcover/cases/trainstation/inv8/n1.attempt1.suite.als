// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 7: It should be possible to reach every exit from every entry
// All tests satisfy earlier requirements 0 through 6.
// Total wrong specifications in dataset: 20
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 18/20
// Detection ratio among parseable specifications: 0.900000 (90.00%)
// Maximum domain scope per test: 4
// Append to the trainstation declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: It should be possible to reach every exit from every entry
pred PositiveScenario1 {
    some disj t1, t2, t3, t4 : Track |
    some disj s1, s2, s3 : Signal |
    {
        Track = t1 + t2 + t3 + t4
        Junction = none
        Entry = t4
        Exit = t1 + t3
        Signal = s1 + s2 + s3
        Semaphore = s3
        Speed = s1 + s2
        succs = t2->t1 + t4->t2 + t4->t3
        signals = t3->s3 + t4->s1 + t4->s2
    }
}
run PositiveScenario1 for exactly 4 Track, exactly 3 Signal, 6 Int expect 1

// Violates the supplied oracle: It should be possible to reach every exit from every entry
pred NegativeScenario1 {
    some disj t1, t2, t3, t4 : Track |
    some disj s1, s2, s3, s4 : Signal |
    {
        Track = t1 + t2 + t3 + t4
        Junction = t1
        Entry = t2 + t3
        Exit = t1 + t4
        Signal = s1 + s2 + s3 + s4
        Semaphore = s2 + s3
        Speed = s1 + s4
        succs = t2->t1 + t3->t1 + t3->t4
        signals = t2->s3 + t2->s4 + t3->s1 + t3->s2
    }
}
run NegativeScenario1 for exactly 4 Track, exactly 4 Signal, 6 Int expect 0
