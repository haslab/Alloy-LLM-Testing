// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 3: Entry tracks are those without predecessors
// All tests satisfy earlier requirements 0 through 2.
// Total wrong specifications in dataset: 77
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 76/77
// Detection ratio among parseable specifications: 0.987013 (98.70%)
// Maximum domain scope per test: 4
// Append to the trainstation declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Entry tracks are those without predecessors
pred PositiveScenario1 {
    some disj t1, t2, t3, t4 : Track |
    some disj s1, s2, s3, s4 : Signal |
    {
        Track = t1 + t2 + t3 + t4
        Junction = t1 + t4
        Entry = t3 + t4
        Exit = t2 + t4
        Signal = s1 + s2 + s3 + s4
        Semaphore = s4
        Speed = s2
        succs = t1->t1 + t3->t2
        signals = t1->s1 + t3->s2 + t3->s4 + t4->s3
    }
}
run PositiveScenario1 for exactly 4 Track, exactly 4 Signal, 6 Int expect 1

// Violates the supplied oracle: Entry tracks are those without predecessors
pred NegativeScenario1 {
    some disj t1, t2, t3, t4 : Track |
    some disj s1 : Signal |
    {
        Track = t1 + t2 + t3 + t4
        Junction = t2
        Entry = t2
        Exit = t1 + t3
        Signal = s1
        Semaphore = none
        Speed = none
        succs = t2->t1 + t4->t4
        signals = t3->s1
    }
}
run NegativeScenario1 for exactly 4 Track, exactly 1 Signal, 6 Int expect 0
