// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 8: Tracks not followed by junctions do not have semaphores
// All tests satisfy earlier requirements 0 through 7.
// Total wrong specifications in dataset: 143
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 137/143
// Detection ratio among parseable specifications: 0.958042 (95.80%)
// Maximum domain scope per test: 4
// Append to the trainstation declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Tracks not followed by junctions do not have semaphores
pred PositiveScenario1 {
    some disj t1, t2, t3, t4 : Track |
    some disj s1, s2, s3, s4 : Signal |
    {
        Track = t1 + t2 + t3 + t4
        Junction = t1 + t2
        Entry = t4
        Exit = t2
        Signal = s1 + s2 + s3 + s4
        Semaphore = s3 + s4
        Speed = s2
        succs = t1->t2 + t3->t1 + t4->t1 + t4->t2 + t4->t3
        signals = t1->s4 + t2->s1 + t4->s2 + t4->s3
    }
}
run PositiveScenario1 for exactly 4 Track, exactly 4 Signal, 6 Int expect 1

// Violates the supplied oracle: Tracks not followed by junctions do not have semaphores
pred NegativeScenario1 {
    some disj t1, t2, t3, t4 : Track |
    some disj s1, s2, s3, s4 : Signal |
    {
        Track = t1 + t2 + t3 + t4
        Junction = t1
        Entry = t3
        Exit = t1
        Signal = s1 + s2 + s3 + s4
        Semaphore = s1 + s2
        Speed = s3 + s4
        succs = t2->t1 + t3->t1 + t3->t2 + t3->t4 + t4->t1
        signals = t1->s2 + t1->s4 + t3->s1 + t3->s3
    }
}
run NegativeScenario1 for exactly 4 Track, exactly 4 Signal, 6 Int expect 0
