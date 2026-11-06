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
    // Earlier requirement 2, required in every Instance.
{
	// Every component is assembled in one workstation
	all c: Component | one c.workstation
}
    // Earlier requirement 3, required in every Instance.
{
	// Components must have parts and materials have no parts
	all c: Component | some c.parts
    all m: Material | no m.parts
}
    Oracle in valid iff {
	// Humans and robots cannot work together
    all w: Workstation | w.workers in Human or w.workers in Robot
}
    S1 in valid iff {
	// Humans and robots cannot work together
    all w: Workstation, workers: w.workers | workers in Human or workers in Robot 
}
    S2 in valid iff {
	// Humans and robots cannot work together
	all w: Workstation | (Human & Robot) not in w.workers
}
    S3 in valid iff {
	// Humans and robots cannot work together
  	all w: Workstation | Human in w.workers

}
    S4 in valid iff {
	// Humans and robots cannot work together
	all w: Workstation | (Human in w.workers) implies (Robot not in w.workers)
  	//all w: Workstation | !((Human in w.workers) and (Robot in w.workers))
}
    S5 in valid iff {
	// Humans and robots cannot work together
	all w: Workstation | !((Human in w.workers) or (Robot in w.workers))
}
    S6 in valid iff {
	// Humans and robots cannot work together
  	all w: Workstation | (w.workers = Worker - Human) or (w.workers = Worker - Robot)
	//all w: Workstation | (Human in w.workers) implies (Robot not in w.workers)
  	//all w: Workstation | (Robot in w.workers) implies (Human not in w.workers)
  	//all w: Workstation | !((Human in w.workers) and (Robot in w.workers))
}
    S7 in valid iff {
	// Humans and robots cannot work together
	all w: Workstation | (Human in w.workers) <=> (Robot not in w.workers)
  	//all w: Workstation | (Robot in w.workers) implies (Human not in w.workers)
  //all w: Workstation | !((Human in w.workers) and (Robot in w.workers))
}
    S8 in valid iff {
	// Humans and robots cannot work together
	all w: Workstation | (Human not in w.workers) <=> (Robot not in w.workers)
  	//all w: Workstation | (Robot in w.workers) implies (Human not in w.workers)
  	//all w: Workstation | !((Human in w.workers) and (Robot in w.workers))
}
    S9 in valid iff {
	// Humans and robots cannot work together
	all w: Workstation | (Human in w.workers) => (Robot in w.workers)
  	//all w: Workstation | (Robot in w.workers) implies (Human not in w.workers)
  	//all w: Workstation | !((Human in w.workers) and (Robot in w.workers))
}
    S10 in valid iff {
	// Humans and robots cannot work together
	all w: Workstation | (Human in w.workers) => !(Robot in w.workers)
    all w: Workstation | (Robot in w.workers) => !(Robot in w.workers)
  	//all w: Workstation | (Robot in w.workers) implies (Human not in w.workers)
  	//all w: Workstation | !((Human in w.workers) and (Robot in w.workers))
}
    S11 in valid iff {
	// Humans and robots cannot work together
  	all w: Workstation | Human in w.workers or Robot in w.workers
	//all w: Workstation | (Human in w.workers) => !(Robot in w.workers)
    //all w: Workstation | (Robot in w.workers) => !(Human in w.workers)
  	//all w: Workstation | (Robot in w.workers) implies (Human not in w.workers)
  	//all w: Workstation | !((Human in w.workers) and (Robot in w.workers))
}
    S12 in valid iff {
	// Humans and robots cannot work together
  	some w: Workstation | (w.workers = Worker - Human) or (w.workers = Worker - Robot)
  	//all w: Workstation | Human in w.workers or Robot in w.workers
	//all w: Workstation | (Human in w.workers) => !(Robot in w.workers)
    //all w: Workstation | (Robot in w.workers) => !(Human in w.workers)
  	//all w: Workstation | (Robot in w.workers) implies (Human not in w.workers)
  	//all w: Workstation | !((Human in w.workers) and (Robot in w.workers))
}
    S13 in valid iff {
	// Humans and robots cannot work together
	all w : Workstation | some r: Robot | r in w.workers implies all wor: Worker | wor in w.workers and wor in Robot
}
    S14 in valid iff {
	// Humans and robots cannot work together
	all w : Workstation | some r: Robot | r in w.workers implies all human: Human | human not in w.workers
  	all w : Workstation | some r: Human | r in w.workers implies all robot: Robot | robot not in w.workers
}
    S15 in valid iff {
	// Humans and robots cannot work together
	Workstation.workers in Human or Workstation.workers in Robot
}
    S16 in valid iff {
	// Humans and robots cannot work together
	all y1,y2: Worker, x: Workstation | (y1 in x.workers) and(y1 in Human) implies (y2 not in x.workers) and (y2 not in Robot)  

  //all r:Robot, h:Human, w:Workstation | w -> r in workers implies w->h not in workers

  all r: Robot, h:Human, x:Workstation | x in workers.r implies x not in workers.h
}
    S17 in valid iff {
	// Humans and robots cannot work together
  	all ws:Workstation| (some w:Human | w in ws.workers implies workers.w not in Robot)
}
    S18 in valid iff {
	// Humans and robots cannot work together
  	all ws:Workstation | (some w:Worker | w in Human and w in ws.workers implies all w1:Worker | w1 in Robot and w1 not in ws.workers) 

}
    S19 in valid iff {
	// Humans and robots cannot work together
  	all w:Human | (some ws : Workstation | w in ws.workers implies Robot not in ws.workers)  

}
    S20 in valid iff {
	// Humans and robots cannot work together
	all h: Human, r: Robot | Workstation.workers not in (h + r)
}
    S21 in valid iff {
	// Humans and robots cannot work together
  	all x: Workstation | x.workers in Human implies x.^succ.workers in Human
}
    S22 in valid iff {
	// Humans and robots cannot work together
  	some Workstation.((^(succ.workers)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) & Human iff
  		no Workstation.((^(succ.workers)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) & Robot
}
    S23 in valid iff {
	// Humans and robots cannot work together
  	some begin.((^(succ.workers)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) & Human iff
  		no begin.((^(succ.workers)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) & Robot
}
    S24 in valid iff {
	// Humans and robots cannot work together
  	all  ws:Workstation | some h:Human| (h in ws.workers) implies ws.workers in Human

}
    S25 in valid iff {
	// Humans and robots cannot work together
	all w: Workstation | Human in w.workers => Robot not in w.workers else w.workers in Robot
}
    S26 in valid iff {
	// Humans and robots cannot work together
	all w: Workstation | Human in w.workers => no Robot & w.workers else w.workers in Robot
}
    S27 in valid iff {
	// Humans and robots cannot work together
	some p1,p2: Worker | all w : Workstation | (p1 in w.workers) and (p2 in w.workers) iff (p1 in Human and p2 in Robot) or (p1 in Robot and p2 in Human)  
}
    S28 in valid iff {
	// Humans and robots cannot work together 
  	all ws: Workstation + Workstation.succ | one p:ws.workers | p in Human implies ws.workers in Human
}
    S29 in valid iff {
	// Humans and robots cannot work together
	no h: Human, r: Robot | some w: Workstation | w.workers = h + r
}
    S30 in valid iff {
	// Humans and robots cannot work together
	all ws : Workstation | ws.workers not in Human and ws.workers not in Robot
}
    S31 in valid iff {
	// Humans and robots cannot work together
	// all ws:Workstation | some w:Worker | 
  	all ws:Workstation | some ws.workers & Worker iff no ws.workers & Robot
}
    S32 in valid iff {
	// Humans and robots cannot work together
	all w1:Human ,w2:Robot | some ws:Workstation | w1 in ws.workers implies w2 not in ws.workers
  
  	// all ws:Workstation | some ws.workers & Human iff no ws.workers & Robot
}
    S33 in valid iff {
	// Humans and robots cannot work together
  	all disj u1, u2 : Worker, w : Workstation | u1 in w.workers implies u2 not in w.workers

}
    S34 in valid iff {
	// Humans and robots cannot work together
	all w: Workstation | one x : Worker| (x in w.workers and x in Human) implies w.workers in Human
}
    S35 in valid iff {
	// Humans and robots cannot work together
  	//if a workstation has 1 human, then it is all humans
  	//if a workstation has 1 robot, then it is all robots
	all ws: Workstation | one h: Human| one r:Robot| (h in ws.workers) implies ws.workers in Human
}
    S36 in valid iff {
	// Humans and robots cannot work together
  	//if a workstation has 1 human, then it is all humans
  	//if a workstation has 1 robot, then it is all robots
	all ws: Workstation | one h: Human| (h in ws.workers) implies ws.workers in Human
}
    S37 in valid iff {
	// Humans and robots cannot work together
  	//if a workstation has 1 human, then it is all humans
  	//if a workstation has 1 robot, then it is all robots
	all ws: Workstation | one h: Human| (h in ws.workers) implies ws.workers in Human
  	all ws: Workstation | one r: Robot| (r in ws.workers) implies ws.workers in Robot
}
    S38 in valid iff {
	// Humans and robots cannot work together
  	//if a workstation has 1 human, then it is all humans
  	//if a workstation has 1 robot, then it is all robots
	//all ws: Workstation | one h: Human| (h in ws.workers) implies ws.workers in Human
  	all ws: Workstation | one r: Robot| (r in ws.workers) implies ws.workers in Robot
}
    S39 in valid iff {
	// Humans and robots cannot work together
  	//if a workstation has 1 human, then it is all humans
  	//if a workstation has 1 robot, then it is all robots
	all ws: Workstation | one p: Worker | (( p in ws.workers and p in Human) implies ws.workers in Human ) and ((p in ws.workers and p in Robot) implies ws.workers in Robot)
}
    S40 in valid iff {
	// Humans and robots cannot work together
  no disj h1, h2: Human | h1.workstation = h2.workstation
	no disj r1, r2: Robot | r1.workstation = r2.workstation
}
    S41 in valid iff {
	// Humans and robots cannot work together
  all ws: Workstation |
		all wr: ws.workers |
			(wr in Robot => no ws.succ.workers & Human) and
			(wr in Human => no ws.succ.workers & Robot)

}
    S42 in valid iff {
	// Humans and robots cannot work together
  all w: Workstation | some w.workers & Robot => no w.workers & Human and no w.succ.workers & Human
  all w: Workstation | some w.workers & Human => no w.workers & Robot and no w.succ.workers & Robot
  

}
    S43 in valid iff {
	// Humans and robots cannot work together
	no disj h1, h2: Human | workers.h1 & workers.h2 != none
    no disj r1, r2: Robot | workers.r1 & workers.r2 != none
}
    S44 in valid iff {
	// Humans and robots cannot work together
	no w: Human | w.workers in Robot and no w: Robot | w.workers in Human


}
    S45 in valid iff {
	// Humans and robots cannot work together
	no w : Workstation |  no (w.workers & Robot)
}
    S46 in valid iff {
	// Humans and robots cannot work together
	all disj h: Human, r: Robot | Workstation.workers = h + r
}
    S47 in valid iff {
	// Humans and robots cannot work together
	one w: Workstation | all h: Human, r: Robot | h&r not in w.workers
}
    S48 in valid iff {
	// Humans and robots cannot work together
	all w: Workstation | lone (w.workers & Human) or lone (w.workers & Robot)
}
    S49 in valid iff {
	// Humans and robots cannot work together
  
	all h : Human , r : Robot | some (workers.h & workers.r)

}
    S50 in valid iff {
	// Humans and robots cannot work together
  all w : Workstation.workers, r : Robot | some h : Human | h in w implies not r in w
    all w : Workstation.workers, r : Human | some h : Robot | r in w implies not h in w
}
    S51 in valid iff {
	// Humans and robots cannot work together
  all w : Workstation.workers | Human in w
}
    S52 in valid iff {
	// Humans and robots cannot work together
	all w: Workstation, wo: w.workers {
      (Human in wo) implies (Robot not in wo)
       (Robot in wo) implies (Human not in wo)
    }
}
    S53 in valid iff {
	// Humans and robots cannot work together
  	all ws: Workstation | one h: Human | h in ws.workers implies !(Robot in ws.workers)

}
    S54 in valid iff {
	// Humans and robots cannot work together
  	all ws: Workstation | all h: Human | h in ws.workers implies !(Robot in ws.workers)

}
    S55 in valid iff {
	// Humans and robots cannot work together
  	one ws: Workstation | all h: Human | h in ws.workers implies !(Robot in ws.workers)

}
    S56 in valid iff {
	// Humans and robots cannot work together
  	all ws:Workstation | no w1, w2: Worker | w1 in ws.workers and w2 in ws.workers
	and w1 = Robot and w2 = Human
}
    S57 in valid iff {
	// Humans and robots cannot work together
  	all ws:Workstation | all w1, w2: Worker | w1 in ws.workers and w2 in ws.workers 	implies ((w1 = Robot and w2 = Robot) or (w1 = Human and w2 = Human))
}
    S58 in valid iff {
	// Humans and robots cannot work together
	all ws : Workstation | ws.workers in Human || ws.workers not in Robot
}
    S59 in valid iff {
	// Humans and robots cannot work together
	one ws : Workstation | (ws.workers = Human) or (ws.workers = Robot)
}
    S60 in valid iff {
	// Humans and robots cannot work together
  all ws: Workstation | all w: Worker | w in ws.workers and (w in Robot iff not w in Human)

}
    S61 in valid iff {
	// Humans and robots cannot work together
  all ws: Workstation | all  w1: Worker, w2 : Worker | w1 in ws.workers and w2 in ws.workers and (w1 in Robot and w2 in Robot ) or (w1 in Human and w2 in Human)
}
    S62 in valid iff {
	// Humans and robots cannot work together
  all w : Workstation | w.workers = Human - Robot

}
    S63 in valid iff {
	// Humans and robots cannot work together
  //all h: Human, r: Robot, wst: Workstation | h in wst.workers implies r not in wst.workers
  all h: Human, r: Robot, wst: Workstation | h in wst.workers iff r not in wst.workers
}
    S64 in valid iff {
	// Humans and robots cannot work together
	all s:Workstation,w1,w2:Worker | s->w1 in workers and s->w2 in workers implies w1 in Robot iff w2 in Robot
}
    S65 in valid iff {
	// Humans and robots cannot work together
    all w:Workstation | Human + Robot not in (w.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)).workers)

}
    S66 in valid iff {
	// Humans and robots cannot work together
  	// Workstation so tem ou um, ou outro
  some w : Workstation | one h : Human | some r : Robot | h in w implies no r
  some w : Workstation | some h : Human | one r : Robot | r in w implies no h

}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66 extends Formula {}

run {
    #valid.Oracle = 2
    #(Instance - valid.Oracle) = 2
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 12 Atom, exactly 4 WorkstationAtom, exactly 4 WorkerAtom, exactly 4 ProductAtom,
       exactly 4 Instance, 6 Int
