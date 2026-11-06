// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 0: The station has at least one entry and one exit
// Total wrong specifications in dataset: 134
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 128/134
// Detection ratio among parseable specifications: 0.955224 (95.52%)
// Maximum domain scope per test: 4
// Append to the trainstation declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: The station has at least one entry and one exit
pred PositiveScenario1 {
    some disj t1, t2, t3, t4 : Track |
    some disj s1, s2, s3, s4 : Signal |
    {
        Track = t1 + t2 + t3 + t4
        Junction = t2 + t4
        Entry = t4
        Exit = t1 + t2
        Signal = s1 + s2 + s3 + s4
        Semaphore = s2 + s3 + s4
        Speed = none
        succs = t1->t1 + t1->t3 + t2->t1 + t2->t2 + t2->t3 + t3->t3 + t4->t3
        signals = t1->s1 + t2->s1 + t3->s2 + t3->s3 + t3->s4 + t4->s1 + t4->s2 + t4->s3 + t4->s4
    }
}
run PositiveScenario1 for exactly 4 Track, exactly 4 Signal, 6 Int expect 1

// Violates the supplied oracle: The station has at least one entry and one exit
pred NegativeScenario1 {
    some disj t1, t2 : Track |
    some disj s1 : Signal |
    {
        Track = t1 + t2
        Junction = t1 + t2
        Entry = t2
        Exit = none
        Signal = s1
        Semaphore = s1
        Speed = none
        succs = t1->t2 + t2->t1
        signals = t1->s1
    }
}
run NegativeScenario1 for exactly 2 Track, exactly 1 Signal, 6 Int expect 0
