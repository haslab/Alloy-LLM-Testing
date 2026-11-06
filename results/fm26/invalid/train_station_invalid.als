sig Track {
	succs : set Track,
	signals : set Signal
}
sig Junction, Entry, Exit in Track {}

sig Signal {}
sig Semaphore, Speed extends Signal {}

// Req 5: Junctions are the tracks with more than one predecessor

// Instance failed to satisfy previous requirements
// Fails req 3: Exit tracks are those without successor
run Pos3_run1_5 {
    some disj P, Q, R : Track {
        Track = P + Q + R
        Junction = R
        Entry = Q
        Exit = Q

        Signal = none
        Semaphore = none
        Speed = none

        succs = P->R + Q->R + R->P
        signals = none->none
    }
} for 3 Track, 0 Signal expect 1


// Req 10: Every track before a junction has a semaphore

// Instance failed to satisfy previous requirements
// Fails req 9: Tracks not followed by junctions do not have semaphores
run Pos3_run1_10 {
    some disj E1,A,E2,J,Ex : Track | some disj Sp1,Sp2,Sm1,Sm2,Sm3 : Signal {
        Track = E1 + A + E2 + J + Ex
        Junction = J
        Entry = E1 + E2
        Exit = Ex

        Signal = Sp1 + Sp2 + Sm1 + Sm2 + Sm3
        Speed = Sp1 + Sp2
        Semaphore = Sm1 + Sm2 + Sm3

        succs = E1->A + A->J + E2->J + J->Ex

        signals = E1->Sp1 + E1->Sm1 + A->Sm2 + E2->Sp2 + E2->Sm3
        // All signals are used by exactly one track; exactly the tracks before the junction have semaphores; entries have speed; all entries reach Ex; no cycles.
    }
} for 5 Track, 5 Signal expect 1

// Instance failed to satisfy previous requirements
// Fails req 9: Tracks not followed by junctions do not have semaphores
run Neg2_run1_10 {
    some disj E1,A,E2,J,Ex : Track | some disj Sp1,Sp2,Sm1,Sm2 : Signal {
        Track = E1 + A + E2 + J + Ex
        Junction = J
        Entry = E1 + E2
        Exit = Ex

        Signal = Sp1 + Sp2 + Sm1 + Sm2
        Speed = Sp1 + Sp2
        Semaphore = Sm1 + Sm2

        succs = E1->A + A->J + E2->J + J->Ex

        signals = E1->Sp1 + E1->Sm1 + E2->Sp2 + E2->Sm2
        // A precedes the junction J but has no semaphore (violation). No semaphores on tracks not followed by a junction (J and Ex); entries have speed; every entry reaches Ex; no cycles.
    }
} for 5 Track, 4 Signal expect 0
