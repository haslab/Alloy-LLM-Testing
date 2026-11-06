// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 5: Influencers post every day
// All tests satisfy earlier requirements 0 through 4.
// Total wrong specifications in dataset: 71
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 66/71
// Detection ratio among parseable specifications: 0.929577 (92.96%)
// Maximum domain scope per test: 4
// Append to the socialnetwork declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Influencers post every day
pred PositiveScenario1 {
    some disj u1, u2, u3, u4 : User |
    some disj p1, p2, p3, p4 : Photo |
    some disj d1, d2 : Day |
    {
        User = u1 + u2 + u3 + u4
        Influencer = u4
        Photo = p1 + p2 + p3 + p4
        Ad = none
        Day = d1 + d2
        follows = u1->u2 + u1->u4 + u2->u1 + u2->u3 + u2->u4 + u3->u1 + u3->u2 + u3->u4 + u4->u1 + u4->u2 + u4->u3
        sees = u3->p2
        posts = u1->p4 + u4->p1 + u4->p2 + u4->p3
        suggested = none->none
        date = p1->d2 + p2->d2 + p3->d1 + p4->d1
    }
}
run PositiveScenario1 for exactly 4 User, exactly 4 Photo, exactly 2 Day, 6 Int expect 1

// Violates the supplied oracle: Influencers post every day
pred NegativeScenario1 {
    some disj u1, u2 : User |
    some disj p1, p2, p3, p4 : Photo |
    some disj d1, d2, d3, d4 : Day |
    {
        User = u1 + u2
        Influencer = u1 + u2
        Photo = p1 + p2 + p3 + p4
        Ad = none
        Day = d1 + d2 + d3 + d4
        follows = u1->u2 + u2->u1
        sees = u1->p4
        posts = u1->p1 + u1->p3 + u2->p2 + u2->p4
        suggested = none->none
        date = p1->d4 + p2->d2 + p3->d3 + p4->d1
    }
}
run NegativeScenario1 for exactly 2 User, exactly 4 Photo, exactly 4 Day, 6 Int expect 0
