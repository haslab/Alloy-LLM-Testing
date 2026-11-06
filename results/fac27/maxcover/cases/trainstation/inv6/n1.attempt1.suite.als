// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 5: Entry tracks must have a speed signal
// All tests satisfy earlier requirements 0 through 4.
// Total wrong specifications in dataset: 52
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 52/52
// Detection ratio among parseable specifications: 1.000000 (100.00%)
// Maximum domain scope per test: 4
// Append to the trainstation declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Entry tracks must have a speed signal
pred PositiveScenario1 {
    some disj t1, t2, t3 : Track |
    some disj s1, s2, s3, s4 : Signal |
    {
        Track = t1 + t2 + t3
        Junction = none
        Entry = t3
        Exit = t3
        Signal = s1 + s2 + s3 + s4
        Semaphore = none
        Speed = s2 + s3 + s4
        succs = t1->t1 + t2->t2
        signals = t2->s4 + t3->s1 + t3->s2 + t3->s3
    }
}
run PositiveScenario1 for exactly 3 Track, exactly 4 Signal, 6 Int expect 1

// Violates the supplied oracle: Entry tracks must have a speed signal
pred NegativeScenario1 {
    some disj t1, t2, t3, t4 : Track |
    some disj s1, s2, s3, s4 : Signal |
    {
        Track = t1 + t2 + t3 + t4
        Junction = none
        Entry = t3 + t4
        Exit = t1 + t2
        Signal = s1 + s2 + s3 + s4
        Semaphore = none
        Speed = s3 + s4
        succs = t3->t2 + t4->t1
        signals = t1->s1 + t2->s3 + t3->s2 + t4->s4
    }
}
run NegativeScenario1 for exactly 4 Track, exactly 4 Signal, 6 Int expect 0
