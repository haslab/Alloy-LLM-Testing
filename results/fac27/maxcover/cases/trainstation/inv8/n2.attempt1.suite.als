// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 7: It should be possible to reach every exit from every entry
// All tests satisfy earlier requirements 0 through 6.
// Total wrong specifications in dataset: 20
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 20/20
// Detection ratio among parseable specifications: 1.000000 (100.00%)
// Maximum domain scope per test: 4
// Append to the trainstation declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: It should be possible to reach every exit from every entry
pred PositiveScenario1 {
    some disj t1, t2, t3, t4 : Track |
    some disj s1, s2, s3, s4 : Signal |
    {
        Track = t1 + t2 + t3 + t4
        Junction = none
        Entry = t4
        Exit = t1 + t2
        Signal = s1 + s2 + s3 + s4
        Semaphore = s4
        Speed = s1 + s3
        succs = t3->t1 + t3->t2 + t4->t3
        signals = t4->s1 + t4->s2 + t4->s3 + t4->s4
    }
}
run PositiveScenario1 for exactly 4 Track, exactly 4 Signal, 6 Int expect 1

// Satisfies the supplied oracle: It should be possible to reach every exit from every entry
pred PositiveScenario2 {
    some disj t1 : Track |
    some disj s1 : Signal |
    {
        Track = t1
        Junction = none
        Entry = t1
        Exit = t1
        Signal = s1
        Semaphore = none
        Speed = s1
        succs = none->none
        signals = t1->s1
    }
}
run PositiveScenario2 for exactly 1 Track, exactly 1 Signal, 6 Int expect 1

// Violates the supplied oracle: It should be possible to reach every exit from every entry
pred NegativeScenario1 {
    some disj t1, t2, t3, t4 : Track |
    some disj s1, s2, s3, s4 : Signal |
    {
        Track = t1 + t2 + t3 + t4
        Junction = t1
        Entry = t3 + t4
        Exit = t1 + t2
        Signal = s1 + s2 + s3 + s4
        Semaphore = s2 + s3
        Speed = s1 + s4
        succs = t3->t1 + t3->t2 + t4->t1
        signals = t3->s4 + t4->s1 + t4->s2 + t4->s3
    }
}
run NegativeScenario1 for exactly 4 Track, exactly 4 Signal, 6 Int expect 0

// Violates the supplied oracle: It should be possible to reach every exit from every entry
pred NegativeScenario2 {
    some disj t1, t2, t3, t4 : Track |
    some disj s1, s2, s3, s4 : Signal |
    {
        Track = t1 + t2 + t3 + t4
        Junction = none
        Entry = t1 + t2 + t3 + t4
        Exit = t1 + t2 + t3 + t4
        Signal = s1 + s2 + s3 + s4
        Semaphore = none
        Speed = s1 + s2 + s3 + s4
        succs = none->none
        signals = t1->s2 + t2->s1 + t3->s3 + t4->s4
    }
}
run NegativeScenario2 for exactly 4 Track, exactly 4 Signal, 6 Int expect 0
