sig User {
	follows : set User,
	sees : set Photo,
	posts : set Photo,
	suggested : set User
}

sig Influencer extends User {}

sig Photo {
	date : one Day
}
sig Ad extends Photo {}

sig Day {}

// Req 3: Users can see ads posted by everyone, but only see non ads posted by followed users

// Unexpectedly generated instance for negative instance
run Neg1_run1_3 {
    some disj U1, U2 : User | some disj A1 : Photo | some disj D1 : Day {
        User = U1 + U2
        Influencer = none
        Photo = A1
        Ad = A1
        Day = D1

        follows = none->none
        posts = U1->A1
        sees = U1->A1
        suggested = none->none
        date = A1->D1
    }
} for 2 User, 1 Photo, 1 Day expect 0

// Unexpectedly generated instance for negative instance
run Neg1_run2_3 {
    -- Negative: The user does not see the ad (Pa), violating that ads are visible to everyone.
    some disj U : User | some disj Pa : Photo | some disj D : Day {
        User = U
        Influencer = none
        Photo = Pa
        Ad = Pa
        Day = D

        date = Pa->D
        posts = U->Pa

        follows = none->none
        sees = none->none
        suggested = none->none
    }
} for 1 User, 1 Photo, 1 Day expect 0


// Unexpectedly generated instance for negative instance
run InstanceN1_run3_3 {
    some disj U1, U2: User | some disj P1: Photo | some disj D1: Day {
        User = U1 + U2
        Influencer = U2
        Photo = P1
        Ad = P1
        Day = D1

        follows = none->none
        posts = U1->P1
        sees = U1->P1
        suggested = none->none
        date = P1->D1
    }
} for 2 User, 1 Photo, 1 Day expect 0

// Req 7: Suggested are other users followed by followed users, but not yet followed

// Failed to parse Alloy model
run Pos1_run1_7 {
    some disj U1, U2 : User {
        User = U1 + U2
        Influencer = none

        Photo = none
        Ad = none
        Day = none

        follows = U1->U2 + U2->U1
        // suggested = none

        posts = none->none
        sees = none->none
        date = none->none
    }
} for 2 User, 0 Photo, 0 Day expect 1

// Failed to parse Alloy model
run Neg2_run1_7 {
    some disj U1, U2, U3 : User {
        User = U1 + U2 + U3
        Influencer = none

        Photo = none
        Ad = none
        Day = none

        follows = U1->U2 + U2->U3
        // suggested = none

        posts = none->none
        sees = none->none
        date = none->none
    }
} for 3 User, 0 Photo, 0 Day expect 0

// Req 8: A user only sees ads from followed or suggested users

// Instance failed to satisfy previous requirements
// Fails req 2: Users cannot follow themselves
// because influencer I can be unified with other users
run NegInstance3_run3_8 {
    some disj I : Influencer | some disj U1, U2, U3 : User | some disj AdI, Ad3 : Ad | some disj D1 : Day {
        User = I + U1 + U2 + U3
        Influencer = I
        Photo = AdI + Ad3
        Ad = AdI + Ad3
        Day = D1

        follows = U1->I + U2->I + U3->I + I->U2
        suggested = U1->U2

        posts = I->AdI + U3->Ad3
        sees = U1->Ad3
        date = AdI->D1 + Ad3->D1
    }
} for 4 User, 2 Photo, 1 Day expect 0
