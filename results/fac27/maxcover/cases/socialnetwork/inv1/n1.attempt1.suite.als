// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 0: Every photo is posted by one user
// Total wrong specifications in dataset: 126
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 121/126
// Detection ratio among parseable specifications: 0.960317 (96.03%)
// Maximum domain scope per test: 4
// Append to the socialnetwork declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Every photo is posted by one user
pred PositiveScenario1 {
    some disj u1, u2, u3 : User |
    some disj p1, p2, p3 : Photo |
    some disj d1, d2 : Day |
    {
        User = u1 + u2 + u3
        Influencer = u2 + u3
        Photo = p1 + p2 + p3
        Ad = p1 + p2
        Day = d1 + d2
        follows = u1->u2 + u2->u2 + u3->u1 + u3->u3
        sees = u1->p1 + u3->p2 + u3->p3
        posts = u1->p1 + u3->p2 + u3->p3
        suggested = none->none
        date = p1->d2 + p2->d1 + p3->d2
    }
}
run PositiveScenario1 for exactly 3 User, exactly 3 Photo, exactly 2 Day, 6 Int expect 1

// Violates the supplied oracle: Every photo is posted by one user
pred NegativeScenario1 {
    some disj u1, u2, u3 : User |
    some disj p1, p2 : Photo |
    some disj d1, d2 : Day |
    {
        User = u1 + u2 + u3
        Influencer = u3
        Photo = p1 + p2
        Ad = p1 + p2
        Day = d1 + d2
        follows = u1->u3
        sees = u1->p1 + u3->p2
        posts = u1->p1 + u3->p1 + u3->p2
        suggested = none->none
        date = p1->d2 + p2->d1
    }
}
run NegativeScenario1 for exactly 3 User, exactly 2 Photo, exactly 2 Day, 6 Int expect 0
