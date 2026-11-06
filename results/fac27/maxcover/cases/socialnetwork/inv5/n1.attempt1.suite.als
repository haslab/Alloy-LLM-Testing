// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 4: Influencers are followed by everyone else
// All tests satisfy earlier requirements 0 through 3.
// Total wrong specifications in dataset: 121
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 119/121
// Detection ratio among parseable specifications: 0.983471 (98.35%)
// Maximum domain scope per test: 4
// Append to the socialnetwork declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Influencers are followed by everyone else
pred PositiveScenario1 {
    some disj u1, u2, u3, u4 : User |
    some disj p1, p2, p3, p4 : Photo |
    some disj d1, d2, d3 : Day |
    {
        User = u1 + u2 + u3 + u4
        Influencer = u3 + u4
        Photo = p1 + p2 + p3 + p4
        Ad = p3 + p4
        Day = d1 + d2 + d3
        follows = u1->u3 + u1->u4 + u2->u3 + u2->u4 + u3->u4 + u4->u2 + u4->u3
        sees = u2->p1 + u3->p4 + u4->p2 + u4->p3
        posts = u1->p3 + u1->p4 + u2->p2 + u4->p1
        suggested = none->none
        date = p1->d3 + p2->d3 + p3->d2 + p4->d2
    }
}
run PositiveScenario1 for exactly 4 User, exactly 4 Photo, exactly 3 Day, 6 Int expect 1

// Violates the supplied oracle: Influencers are followed by everyone else
pred NegativeScenario1 {
    some disj u1, u2, u3, u4 : User |
    some disj p1, p2, p3 : Photo |
    some disj d1 : Day |
    {
        User = u1 + u2 + u3 + u4
        Influencer = u1 + u2 + u4
        Photo = p1 + p2 + p3
        Ad = p1 + p2
        Day = d1
        follows = u1->u2 + u2->u1 + u2->u4 + u3->u1 + u3->u2 + u3->u4 + u4->u2
        sees = u1->p1 + u1->p2 + u2->p1 + u2->p2 + u3->p1 + u3->p2 + u4->p1 + u4->p2
        posts = u1->p1 + u1->p2 + u4->p3
        suggested = none->none
        date = p1->d1 + p2->d1 + p3->d1
    }
}
run NegativeScenario1 for exactly 4 User, exactly 3 Photo, exactly 1 Day, 6 Int expect 0
