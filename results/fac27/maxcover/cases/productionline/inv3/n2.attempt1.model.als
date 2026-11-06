abstract sig Atom {}
sig WorkstationAtom, WorkerAtom, ProductAtom extends Atom {}
abstract sig Formula {}
one sig Oracle extends Formula {}
sig detected in Formula {}
sig Instance {
    valid : set Formula,
    Workstation : set WorkstationAtom,
    begin : set WorkstationAtom,
    end : set WorkstationAtom,
    Worker : set WorkerAtom,
    Human : set WorkerAtom,
    Robot : set WorkerAtom,
    Product : set ProductAtom,
    Material : set ProductAtom,
    Component : set ProductAtom,
    Dangerous : set ProductAtom,
    workers : WorkstationAtom -> WorkerAtom,
    succ : WorkstationAtom -> WorkstationAtom,
    parts : ProductAtom -> ProductAtom,
    workstation : ProductAtom -> WorkstationAtom
} {
    workers in Workstation -> Worker
    succ in Workstation -> Workstation
    parts in Product -> Product
    workstation in Component -> Workstation
    one begin
    one end
    begin + end in Workstation
    Human + Robot in Worker
    no Human & Robot
    Product = Material + Component
    no Material & Component
    Dangerous in Product
    // Earlier requirement 0, required in every Instance.
{
	// Workers are either human or robots
 all w: Worker | w in Human or w in Robot
}
    // Earlier requirement 1, required in every Instance.
{
	// Every workstation has workers and every worker works in one workstation
	all ws: Workstation | some ws.workers
  	all w: Worker | one ws: Workstation | w in ws.workers
}
    Oracle in valid iff {
	// Every component is assembled in one workstation
	all c: Component | one c.workstation
}
    S1 in valid iff {
	// Every component is assembled in one workstation
    workstation in Component lone -> Workstation
}
    S2 in valid iff {
	// Every component is assembled in one workstation
    workstation in Component one -> Workstation
}
    S3 in valid iff {
	// Every component is assembled in one workstation
    workstation in Component some -> Workstation
}
    S4 in valid iff {
	// Every component is assembled in one workstation

}
    S5 in valid iff {
	// Every component is assembled in one workstation
	all c: Component | one workstation
}
    S6 in valid iff {
	// Every component is assembled in one workstation
	one w: Workstation | all c: Component | c in c.workstation
}
    S7 in valid iff {
	// Every component is assembled in one workstation
	one w: Workstation | all c: Component | w in c.workstation
}
    S8 in valid iff {
	// Every component is assembled in one workstation
  	all c : Component, p : Product | p.parts in c.workstation

}
    S9 in valid iff {
	// Every component is assembled in one workstation
	one Component.workstation
}
    S10 in valid iff {
	// Every component is assembled in one workstation
	all c: Component | one w: Workstation | c in w.workstation
}
    S11 in valid iff {
	// Every component is assembled in one workstation
    all c : Component | one Workstation 
}
    S12 in valid iff {
	// Every component is assembled in one workstation
	all c : Component | some c.workstation
}
    S13 in valid iff {
	// Every component is assembled in one workstation
	   all c: Component | one w: Workstation | c in w.workstation
    all w: Workstation | some c: Component | c in w.workstation
}
    S14 in valid iff {
	// Every component is assembled in one workstation
	all p:Product | p in Component and one(p.workstation)
}
    S15 in valid iff {
	// Every component is assembled in one workstation
	all c: Component | c.workstation not in (Component-c).workstation
}
    S16 in valid iff {
	// Every component is assembled in one workstation
  all c: Component | #c.workstation = 2

}
    S17 in valid iff {
	// Every component is assembled in one workstation
	all c : Component | lone c.workstation
}
    S18 in valid iff {
	// Every component is assembled in one workstation
	all c:Component | c.workstation = Workstation
}
    S19 in valid iff {
	// Every component is assembled in one workstation
  all c : Component | all w1, w2 : Workstation | w1 in c.workstation implies w2 not in c.workstation and w1 != w2
}
    S20 in valid iff {
	// Every component is assembled in one workstation
	workstation in Component one -> one Workstation
}
    S21 in valid iff {
	// Every component is assembled in one workstation
  lone Component.workstation

}
    S22 in valid iff {
	// Every component is assembled in one workstation
	all p: Product | all c: p.parts | c.workstation = p.parts.workstation
}
    S23 in valid iff {
	// Every component is assembled in one workstation
	one c : Component | one w : Workstation | w in c.workstation
}
    S24 in valid iff {
	// Every component is assembled in one workstation
	all c : Component | one w : Workstation | c.parts in w.succ
}
    S25 in valid iff {
	// Every component is assembled in one workstation
	all c : Component | one w : Workstation | c.workstation in w

}
    S26 in valid iff {
	// Every component is assembled in one workstation
  all c : Component, w : Workstation | c.workstation in w

}
    S27 in valid iff {
	// Every component is assembled in one workstation
  all c : Component | c.workstation in Workstation.succ

}
    S28 in valid iff {
	// Every component is assembled in one workstation
	all c: Component | one Component.workstation
}
    S29 in valid iff {
	// Every component is assembled in one workstation
	workstation in Component some -> one Workstation
}
    S30 in valid iff {
	// Every component is assembled in one workstation
  	Product in workstation.Workstation

}
    S31 in valid iff {
	// Every component is assembled in one workstation
  	all c : Component | one workstation.Workstation
}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31 extends Formula {}

run {
    #valid.Oracle = 2
    #(Instance - valid.Oracle) = 2
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 12 Atom, exactly 4 WorkstationAtom, exactly 4 WorkerAtom, exactly 4 ProductAtom,
       exactly 4 Instance, 6 Int
