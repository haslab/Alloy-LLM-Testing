// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 4: Junctions are the tracks with more than one predecessor
// All tests satisfy earlier requirements 0 through 3.
// Total wrong specifications in dataset: 136
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 136/136
// Detection ratio among parseable specifications: 1.000000 (100.00%)
// Maximum domain scope per test: 4
// Append to the trainstation declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Junctions are the tracks with more than one predecessor
pred PositiveScenario1 {
    some disj t1 : Track |
    some disj s1, s2, s3 : Signal |
    {
        Track = t1
        Junction = none
        Entry = t1
        Exit = t1
        Signal = s1 + s2 + s3
        Semaphore = s3
        Speed = s1 + s2
        succs = none->none
        signals = t1->s1 + t1->s2 + t1->s3
    }
}
run PositiveScenario1 for exactly 1 Track, exactly 3 Signal, 6 Int expect 1

// Satisfies the supplied oracle: Junctions are the tracks with more than one predecessor
pred PositiveScenario2 {
    some disj t1, t2, t3, t4 : Track |
    some disj s1 : Signal |
    {
        Track = t1 + t2 + t3 + t4
        Junction = t2 + t4
        Entry = t3
        Exit = t3
        Signal = s1
        Semaphore = none
        Speed = none
        succs = t1->t2 + t1->t4 + t2->t2 + t4->t1 + t4->t2 + t4->t4
        signals = t3->s1
    }
}
run PositiveScenario2 for exactly 4 Track, exactly 1 Signal, 6 Int expect 1

// Violates the supplied oracle: Junctions are the tracks with more than one predecessor
pred NegativeScenario1 {
    some disj t1, t2, t3, t4 : Track |
    some disj s1, s2, s3, s4 : Signal |
    {
        Track = t1 + t2 + t3 + t4
        Junction = none
        Entry = t4
        Exit = t4
        Signal = s1 + s2 + s3 + s4
        Semaphore = s3
        Speed = s1
        succs = t1->t1 + t2->t2 + t3->t1 + t3->t3
        signals = t1->s1 + t1->s4 + t2->s2 + t2->s3
    }
}
run NegativeScenario1 for exactly 4 Track, exactly 4 Signal, 6 Int expect 0

// Violates the supplied oracle: Junctions are the tracks with more than one predecessor
pred NegativeScenario2 {
    some disj t1, t2, t3 : Track |
    some disj s1, s2, s3, s4 : Signal |
    {
        Track = t1 + t2 + t3
        Junction = t1 + t2
        Entry = t3
        Exit = t2
        Signal = s1 + s2 + s3 + s4
        Semaphore = s4
        Speed = s2
        succs = t1->t1 + t1->t2 + t3->t1
        signals = t1->s1 + t1->s3 + t3->s2 + t3->s4
    }
}
run NegativeScenario2 for exactly 3 Track, exactly 4 Signal, 6 Int expect 0
