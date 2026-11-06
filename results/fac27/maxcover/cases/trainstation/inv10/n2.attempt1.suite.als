// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 9: Every track before a junction has a semaphore
// All tests satisfy earlier requirements 0 through 8.
// Total wrong specifications in dataset: 48
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 48/48
// Detection ratio among parseable specifications: 1.000000 (100.00%)
// Maximum domain scope per test: 4
// Append to the trainstation declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Every track before a junction has a semaphore
pred PositiveScenario1 {
    some disj t1, t2 : Track |
    some disj s1, s2, s3 : Signal |
    {
        Track = t1 + t2
        Junction = none
        Entry = t2
        Exit = t1
        Signal = s1 + s2 + s3
        Semaphore = none
        Speed = s1 + s3
        succs = t2->t1
        signals = t1->s3 + t2->s1 + t2->s2
    }
}
run PositiveScenario1 for exactly 2 Track, exactly 3 Signal, 6 Int expect 1

// Satisfies the supplied oracle: Every track before a junction has a semaphore
pred PositiveScenario2 {
    some disj t1, t2, t3, t4 : Track |
    some disj s1, s2, s3, s4 : Signal |
    {
        Track = t1 + t2 + t3 + t4
        Junction = t4
        Entry = t2
        Exit = t4
        Signal = s1 + s2 + s3 + s4
        Semaphore = s1 + s2 + s4
        Speed = s3
        succs = t1->t3 + t2->t1 + t2->t4 + t3->t4
        signals = t2->s1 + t2->s2 + t2->s3 + t3->s4
    }
}
run PositiveScenario2 for exactly 4 Track, exactly 4 Signal, 6 Int expect 1

// Violates the supplied oracle: Every track before a junction has a semaphore
pred NegativeScenario1 {
    some disj t1, t2, t3, t4 : Track |
    some disj s1, s2, s3, s4 : Signal |
    {
        Track = t1 + t2 + t3 + t4
        Junction = t1
        Entry = t4
        Exit = t1 + t3
        Signal = s1 + s2 + s3 + s4
        Semaphore = s4
        Speed = s2
        succs = t2->t1 + t2->t3 + t4->t1 + t4->t2
        signals = t1->s1 + t2->s3 + t4->s2 + t4->s4
    }
}
run NegativeScenario1 for exactly 4 Track, exactly 4 Signal, 6 Int expect 0

// Violates the supplied oracle: Every track before a junction has a semaphore
pred NegativeScenario2 {
    some disj t1, t2, t3 : Track |
    some disj s1, s2, s3 : Signal |
    {
        Track = t1 + t2 + t3
        Junction = t3
        Entry = t2
        Exit = t3
        Signal = s1 + s2 + s3
        Semaphore = s2 + s3
        Speed = s1
        succs = t1->t3 + t2->t1 + t2->t3
        signals = t1->s2 + t1->s3 + t2->s1
    }
}
run NegativeScenario2 for exactly 3 Track, exactly 3 Signal, 6 Int expect 0
