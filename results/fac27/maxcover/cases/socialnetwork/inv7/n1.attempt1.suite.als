// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 6: Suggested are other users followed by followed users, but not yet followed
// All tests satisfy earlier requirements 0 through 5.
// Total wrong specifications in dataset: 464
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 452/464
// Detection ratio among parseable specifications: 0.974138 (97.41%)
// Maximum domain scope per test: 4
// Append to the socialnetwork declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Suggested are other users followed by followed users, but not yet followed
pred PositiveScenario1 {
    some disj u1, u2, u3, u4 : User |
    some disj p1, p2, p3, p4 : Photo |
    some disj d1, d2 : Day |
    {
        User = u1 + u2 + u3 + u4
        Influencer = u4
        Photo = p1 + p2 + p3 + p4
        Ad = p1 + p2 + p3 + p4
        Day = d1 + d2
        follows = u1->u2 + u1->u3 + u1->u4 + u2->u1 + u2->u4 + u3->u4 + u4->u1
        sees = none->none
        posts = u1->p4 + u4->p1 + u4->p2 + u4->p3
        suggested = u2->u3 + u3->u1 + u4->u2 + u4->u3
        date = p1->d1 + p2->d2 + p3->d2 + p4->d2
    }
}
run PositiveScenario1 for exactly 4 User, exactly 4 Photo, exactly 2 Day, 6 Int expect 1

// Violates the supplied oracle: Suggested are other users followed by followed users, but not yet followed
pred NegativeScenario1 {
    some disj u1, u2, u3, u4 : User |
    some disj p1, p2, p3, p4 : Photo |
    some disj d1, d2, d3 : Day |
    {
        User = u1 + u2 + u3 + u4
        Influencer = none
        Photo = p1 + p2 + p3 + p4
        Ad = p2 + p3 + p4
        Day = d1 + d2 + d3
        follows = u1->u4 + u2->u3 + u3->u1 + u3->u2 + u3->u4 + u4->u1 + u4->u3
        sees = none->none
        posts = u2->p2 + u3->p3 + u3->p4 + u4->p1
        suggested = u1->u3 + u2->u1 + u2->u4
        date = p1->d2 + p2->d3 + p3->d2 + p4->d1
    }
}
run NegativeScenario1 for exactly 4 User, exactly 4 Photo, exactly 3 Day, 6 Int expect 0
