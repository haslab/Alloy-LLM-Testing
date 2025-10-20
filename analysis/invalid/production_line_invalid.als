sig Workstation {
	workers : set Worker,
	succ : set Workstation
}
one sig begin, end in Workstation {}

sig Worker {}
sig Human, Robot extends Worker {}

abstract sig Product {
	parts : set Product	
}

sig Material extends Product {}

sig Component extends Product {
	workstation : set Workstation
}

sig Dangerous in Product {}

// Req 6: Components cannot be their own parts

// Unexpectedly failed to generate instance for positive instance
run Pos3_run2_6 {
    some disj WB, WE : Workstation | some disj H, R : Worker | some disj P1, P2 : Product {
        // Positive: two components point to each other as parts (no self-parts). Begin has a human, end has a robot; no mixing at a workstation.
        Workstation = WB + WE
        begin = WB
        end = WE
        succ = WE->WB

        Worker = H + R
        Human = H
        Robot = R
        workers = WB->H + WE->R

        Product = P1 + P2
        Component = P1 + P2
        Material = none
        Dangerous = P2
        parts = P1->P2 + P2->P1
        workstation = P1->WB + P2->WE
    }
} for 2 Workstation, 2 Worker, 2 Product expect 1

// Req 7: Components built of dangerous parts are also dangerous

// Failed to parse Alloy model
run Pos1_run2_7 {
    some disj WB, WE : Workstation | some disj HU1, HU2 : Worker | some disj M1 : Material | some disj C1 : Component {
        Workstation = WB + WE
        begin = WB
        end = WE

        Worker = HU1 + HU2
        Human = HU1 + HU2
        Robot = none

        Product = M1 + C1
        Material = M1
        Component = C1
        Dangerous = M1 + C1

        workers = WB->HU1 + WE->HU2
        // succ = none
        parts = C1->M1
        workstation = C1->WB
    }
} for 2 Workstation, 2 Worker, 2 Product expect 1

// Failed to parse Alloy model
run Neg1_run2_7 {
    some disj WB, WE : Workstation | some disj HU1, HU2 : Worker | some disj M1 : Material | some disj C1 : Component {
        Workstation = WB + WE
        begin = WB
        end = WE

        Worker = HU1 + HU2
        Human = HU1 + HU2
        Robot = none

        Product = M1 + C1
        Material = M1
        Component = C1
        Dangerous = M1

        workers = WB->HU1 + WE->HU2
        // succ = none
        parts = C1->M1
        workstation = C1->WB
    }
} for 2 Workstation, 2 Worker, 2 Product expect 0
