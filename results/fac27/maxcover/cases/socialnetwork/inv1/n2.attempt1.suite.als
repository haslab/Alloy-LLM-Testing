// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 0: Every photo is posted by one user
// Total wrong specifications in dataset: 126
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 126/126
// Detection ratio among parseable specifications: 1.000000 (100.00%)
// Maximum domain scope per test: 4
// Append to the socialnetwork declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: Every photo is posted by one user
pred PositiveScenario1 {
    some disj u1, u2, u3, u4 : User |
    some disj d1, d2, d3 : Day |
    {
        User = u1 + u2 + u3 + u4
        Influencer = u3 + u4
        Photo = none
        Ad = none
        Day = d1 + d2 + d3
        follows = u1->u3 + u1->u4 + u2->u2 + u2->u3 + u2->u4 + u3->u1 + u3->u4 + u4->u2 + u4->u3 + u4->u4
        sees = none->none
        posts = none->none
        suggested = none->none
        date = none->none
    }
}
run PositiveScenario1 for exactly 4 User, exactly 0 Photo, exactly 3 Day, 6 Int expect 1

// Satisfies the supplied oracle: Every photo is posted by one user
pred PositiveScenario2 {
    some disj u1, u2, u3, u4 : User |
    some disj p1, p2, p3 : Photo |
    some disj d1, d2, d3, d4 : Day |
    {
        User = u1 + u2 + u3 + u4
        Influencer = u4
        Photo = p1 + p2 + p3
        Ad = p2
        Day = d1 + d2 + d3 + d4
        follows = u1->u3 + u2->u1 + u4->u4
        sees = u3->p1 + u4->p1
        posts = u2->p2 + u2->p3 + u4->p1
        suggested = none->none
        date = p1->d3 + p2->d4 + p3->d3
    }
}
run PositiveScenario2 for exactly 4 User, exactly 3 Photo, exactly 4 Day, 6 Int expect 1

// Violates the supplied oracle: Every photo is posted by one user
pred NegativeScenario1 {
    some disj p1 : Photo |
    some disj d1, d2, d3 : Day |
    {
        User = none
        Influencer = none
        Photo = p1
        Ad = none
        Day = d1 + d2 + d3
        follows = none->none
        sees = none->none
        posts = none->none
        suggested = none->none
        date = p1->d3
    }
}
run NegativeScenario1 for exactly 0 User, exactly 1 Photo, exactly 3 Day, 6 Int expect 0

// Violates the supplied oracle: Every photo is posted by one user
pred NegativeScenario2 {
    some disj u1, u2, u3, u4 : User |
    some disj p1, p2, p3, p4 : Photo |
    some disj d1, d2, d3 : Day |
    {
        User = u1 + u2 + u3 + u4
        Influencer = none
        Photo = p1 + p2 + p3 + p4
        Ad = p4
        Day = d1 + d2 + d3
        follows = u1->u2 + u1->u4 + u2->u2 + u3->u1 + u3->u4
        sees = u2->p1 + u2->p3 + u2->p4 + u3->p1 + u3->p2 + u3->p3 + u3->p4
        posts = u3->p1 + u3->p2 + u3->p3 + u3->p4 + u4->p4
        suggested = none->none
        date = p1->d1 + p2->d2 + p3->d3 + p4->d1
    }
}
run NegativeScenario2 for exactly 4 User, exactly 4 Photo, exactly 3 Day, 6 Int expect 0
