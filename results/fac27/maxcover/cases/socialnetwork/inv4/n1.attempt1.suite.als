// Dataset: /Users/alcino/Projectos/Alloy-LLM-Testing/minimal/results/dataset.json
// Optimizer backend: sat4jmax
// Requirement 3: If a user posts an ad then all its posts should be labeled as ads
// All tests satisfy earlier requirements 0 through 2.
// Total wrong specifications in dataset: 127
// Unparseable wrong specifications skipped: 0
// Maximum wrong specifications detected: 124/127
// Detection ratio among parseable specifications: 0.976378 (97.64%)
// Maximum domain scope per test: 4
// Append to the socialnetwork declarations.
// expect assumes the target requirement is enforced as a fact.
// Both classes satisfy the declarations and earlier requirement facts.

// Satisfies the supplied oracle: If a user posts an ad then all its posts should be labeled as ads
pred PositiveScenario1 {
    some disj u1, u2, u3, u4 : User |
    some disj p1, p2, p3, p4 : Photo |
    some disj d1, d2, d3, d4 : Day |
    {
        User = u1 + u2 + u3 + u4
        Influencer = u3 + u4
        Photo = p1 + p2 + p3 + p4
        Ad = p1 + p3 + p4
        Day = d1 + d2 + d3 + d4
        follows = u2->u4 + u3->u4 + u4->u1
        sees = none->none
        posts = u1->p3 + u2->p1 + u2->p4 + u4->p2
        suggested = none->none
        date = p1->d4 + p2->d3 + p3->d2 + p4->d1
    }
}
run PositiveScenario1 for exactly 4 User, exactly 4 Photo, exactly 4 Day, 6 Int expect 1

// Violates the supplied oracle: If a user posts an ad then all its posts should be labeled as ads
pred NegativeScenario1 {
    some disj u1, u2, u3, u4 : User |
    some disj p1, p2, p3, p4 : Photo |
    some disj d1 : Day |
    {
        User = u1 + u2 + u3 + u4
        Influencer = none
        Photo = p1 + p2 + p3 + p4
        Ad = p2 + p3 + p4
        Day = d1
        follows = u4->u3
        sees = none->none
        posts = u1->p1 + u1->p2 + u2->p3 + u4->p4
        suggested = none->none
        date = p1->d1 + p2->d1 + p3->d1 + p4->d1
    }
}
run NegativeScenario1 for exactly 4 User, exactly 4 Photo, exactly 1 Day, 6 Int expect 0
