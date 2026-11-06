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
    Oracle in valid iff {
	// Workers are either human or robots
 all w: Worker | w in Human or w in Robot
}
    S1 in valid iff {
	// Workers are either human or robots
	
}
    S2 in valid iff {
	// Workers are either human or robots
	all w: Workstation | w.workers in (Human + Robot) and some w.workers and no Worker
}
    S3 in valid iff {
	// Workers are either human or robots
 all w: Worker | w in Human and w in Robot
}
    S4 in valid iff {
	// Workers are either human or robots
  	all w: Workstation | Worker !in w.workers
	
}
    S5 in valid iff {
	// Workers are either human or robots
  	all w: Workstation | (Human in Worker implies Human in w.workers) 
	or (Robot in Worker implies Robot in w.workers) and lone w.workers and Worker in w.workers
	
}
    S6 in valid iff {
	// Workers are either human or robots
  	all w: Workstation | (Human in Worker implies Human in w.workers) 
	and (Robot in Worker implies Robot in w.workers) and lone w.workers and Worker in w.workers
	
}
    S7 in valid iff {
	// Workers are either human or robots
  all w:Workstation | w.workers in Robot or w.workers in Human
	
}
    S8 in valid iff {
	// Workers are either human or robots
	all w: Workstation | w.workers in Human + Robot
}
    S9 in valid iff {
	// Workers are either human or robots
	all w : Worker | w = Human + Robot
}
    S10 in valid iff {
	// Workers are either human or robots
	all w: Workstation | w.workers in Human + Robot and some w.workers
}
    S11 in valid iff {
	// Workers are either human or robots
	all w: Workstation | w.workers in (Human + Robot)
  	all h: Human | h in workers.h
}
    S12 in valid iff {
	// Workers are either human or robots
	Worker-(Human+Robot) & Workstation.workers = none
}
    S13 in valid iff {
	// Workers are either human or robots
	all w: Workstation | w.workers in (Human + Robot)
  	all H: Human | some w: Workstation | H in w.workers
}
    S14 in valid iff {
	// Workers are either human or robots
	all w: Workstation | (w.workers not in Human) or (w.workers not in Robot)
}
    S15 in valid iff {
	// Workers are either human or robots
  	all e : Worker | e=Human or e=Robot 
	
}
    S16 in valid iff {
	// Workers are either human or robots
	Worker = Human
	
}
    S17 in valid iff {
	// Workers are either human or robots
	all wk : Workstation | wk.workers in Human
}
    S18 in valid iff {
	// Workers are either human or robots
  	all ws: Workstation| (ws.workers in Human and ws.workers not in Robot) or (ws.workers not in Human and ws.workers in Robot)
	
}
    S19 in valid iff {
	// Workers are either human or robots
	Worker in Human or Worker in Robot
}
    S20 in valid iff {
	// Workers are either human or robots
  	all ws: Workstation.^succ | ws.workers in Human or ws.workers in Robot
	
}
    S21 in valid iff {
	// Workers are either human or robots
  	all ws: Workstation.^succ, w: ws.workers | w in Human or w in Robot
	
}
    S22 in valid iff {
	// Workers are either human or robots
  	all ws: Workstation.^succ, w: ws.workers | ws in Human or ws in Robot
	
}
    S23 in valid iff {
	// Workers are either human or robots
  	Workstation.workers + Workstation.^succ.workers in Human or Workstation.workers + Workstation.^succ.workers in Robot
  	
}
    S24 in valid iff {
	// Workers are either human or robots
  	all w: Workstation | w.workers + w.^succ.workers in Human or w.workers + w.^succ.workers in Robot
  	
}
    S25 in valid iff {
	// Workers are either human or robots
	all w : Workstation.workers | w = Human or w = Human
}
    S26 in valid iff {
	// Workers are either human or robots
	all w : Workstation | w.workers = Human or w.workers = Human
}
    S27 in valid iff {
	// Workers are either human or robots
	all w : Workstation | w.workers = Human or w.workers = Robot
}
    S28 in valid iff {
	// Workers are either human or robots
  all w : Workstation | w.workers = Human + Robot
	
}
    S29 in valid iff {
	// Workers are either human or robots
	all u: Worker | Human in u or Robot in u
}
    S30 in valid iff {
	// Workers are either human or robots
  not Worker in (Worker - Human - Robot)
}
    S31 in valid iff {
	// Workers are either human or robots
	Workstation.workers = Human + Robot
}
    S32 in valid iff {
	// Workers are either human or robots
	Human + Robot in Workstation.workers
}
    S33 in valid iff {
	// Workers are either human or robots
	all w : Worker | w not in Human and w not in Robot
}
    S34 in valid iff {
	// Workers are either human or robots
  all h: Human, r: Robot | Workstation->h in workers or Workstation->r in workers
	
}
    S35 in valid iff {
	// Workers are either human or robots
	all w : Worker | w in Human or w !in Robot
}
    S36 in valid iff {
	// Workers are either human or robots
  	all w:Worker | not (w in Human) and (w in Robot) and (w in Human or w in Robot)
	
}
    S37 in valid iff {
	// Workers are either human or robots
	all disj w,a : Worker | (w = Human implies a = Human) or (a = Robot implies w 		= Robot)
}
    S38 in valid iff {
	// Workers are either human or robots
	all disj w,a : Worker | w.(~workers) =a.(~workers)implies((w = Human implies 	  a = Human) or (a = Robot implies w = Robot))
}
    S39 in valid iff {
	// Workers are either human or robots
	some w : Worker | w = Human or w = Robot
}
    S40 in valid iff {
	// Workers are either human or robots
	all w: Worker | w in Human or w = Robot
}
    S41 in valid iff {
	// Workers are either human or robots
	all wo: Workstation | (Human in wo.workers implies Robot not in wo.workers) and 						  (Robot in wo.workers implies Human not in wo.workers)
}
    S42 in valid iff {
	// Workers are either human or robots
	some Human+Robot & Workstation.workers 
}
    S43 in valid iff {
	// Workers are either human or robots
  all w : Worker | w =  Human - Robot
	
}
    S44 in valid iff {
	// Workers are either human or robots
  all w : Workstation | Human in w.workers  or Robot in w.workers
}
    S45 in valid iff {
	// Workers are either human or robots
	no Human.~workers & Robot.~workers
}
    S46 in valid iff {
	// Workers are either human or robots
  	all w : Workstation | not (w.workers in Robot + Human)
}
    S47 in valid iff {
	// Workers are either human or robots
	all w : Worker | some h : Human | some r : Robot | w = h or w = r
	
}
    S48 in valid iff {
	// Workers are either human or robots
	all w : Worker | some h : Human | some r : Robot | ((w = h) implies (w != r)) and ((w=r) implies (w != h))
	
}
    S49 in valid iff {
	// Workers are either human or robots
	// all w: Worker | w in Human + Robot
	// no Human - no Robot in
  	Human - Robot = none
}
    S50 in valid iff {
	// Workers are either human or robots
	all wk : Workstation | not wk.workers in Human and wk.workers in Robot
}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50 extends Formula {}

run {
    #valid.Oracle = 1
    #(Instance - valid.Oracle) = 1
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 12 Atom, exactly 4 WorkstationAtom, exactly 4 WorkerAtom, exactly 4 ProductAtom,
       exactly 2 Instance, 6 Int
