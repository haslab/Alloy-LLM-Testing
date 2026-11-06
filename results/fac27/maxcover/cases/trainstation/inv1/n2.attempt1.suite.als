// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 0: The station has at least one entry and one exit
// Total wrong specifications in dataset: 134
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 133/134
// Detection ratio among parseable specifications: 0.992537 (99.25%)
// Maximum domain scope per test: 4
// Append to the trainstation declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: The station has at least one entry and one exit
pred PositiveScenario1 {
    some disj t1, t2 : Track |
    some disj s1, s2, s3 : Signal |
    {
        Track = t1 + t2
        Junction = t2
        Entry = t2
        Exit = t2
        Signal = s1 + s2 + s3
        Semaphore = s2
        Speed = s1
        succs = t2->t1
        signals = none->none
    }
}
run PositiveScenario1 for exactly 2 Track, exactly 3 Signal, 6 Int expect 1

// Satisfies the supplied oracle: The station has at least one entry and one exit
pred PositiveScenario2 {
    some disj t1, t2, t3, t4 : Track |
    some disj s1, s2, s3, s4 : Signal |
    {
        Track = t1 + t2 + t3 + t4
        Junction = none
        Entry = t2 + t3
        Exit = t1 + t4
        Signal = s1 + s2 + s3 + s4
        Semaphore = s1 + s3 + s4
        Speed = s2
        succs = t1->t2 + t1->t4 + t2->t2 + t3->t3 + t4->t1 + t4->t3 + t4->t4
        signals = t4->s1 + t4->s2 + t4->s3 + t4->s4
    }
}
run PositiveScenario2 for exactly 4 Track, exactly 4 Signal, 6 Int expect 1

// Violates the supplied oracle: The station has at least one entry and one exit
pred NegativeScenario1 {
    some disj s1, s2, s3 : Signal |
    {
        Track = none
        Junction = none
        Entry = none
        Exit = none
        Signal = s1 + s2 + s3
        Semaphore = s2 + s3
        Speed = s1
        succs = none->none
        signals = none->none
    }
}
run NegativeScenario1 for exactly 0 Track, exactly 3 Signal, 6 Int expect 0

// Violates the supplied oracle: The station has at least one entry and one exit
pred NegativeScenario2 {
    some disj t1 : Track |
    some disj s1, s2, s3 : Signal |
    {
        Track = t1
        Junction = none
        Entry = none
        Exit = t1
        Signal = s1 + s2 + s3
        Semaphore = s2 + s3
        Speed = s1
        succs = t1->t1
        signals = t1->s1 + t1->s2 + t1->s3
    }
}
run NegativeScenario2 for exactly 1 Track, exactly 3 Signal, 6 Int expect 0
