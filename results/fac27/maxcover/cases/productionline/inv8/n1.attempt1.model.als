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
    // Earlier requirement 4, required in every Instance.
{
	// Humans and robots cannot work together
    all w: Workstation | w.workers in Human or w.workers in Robot
}
    // Earlier requirement 5, required in every Instance.
{
	// Components cannot be their own parts
	all c: Component | c not in c.^parts
}
    // Earlier requirement 6, required in every Instance.
{
	// Components built of dangerous parts are also dangerous
	all c: Component | some (c.parts & Dangerous) implies c in Dangerous
}
    Oracle in valid iff {
	// Dangerous components cannot be assembled by humans
	all c: (Component & Dangerous) | no c.workstation.workers & Human
}
    S1 in valid iff {
  // Dangerous components cannot be assembled by humans
  all w: Workstation | Dangerous in workstation.w.parts implies no w.workers & Human
}
    S2 in valid iff {
	// Dangerous components cannot be assembled by humans
    
}
    S3 in valid iff {
	// Dangerous components cannot be assembled by humans
  all c : Component | no c.workstation.workers & Human

}
    S4 in valid iff {
	// Dangerous components cannot be assembled by humans
	all c : Component | c in Dangerous 
}
    S5 in valid iff {
	// Dangerous components cannot be assembled by humans
  all c: Component| all w: Worker| c in Dangerous implies w in Human
  //all c:Component| c.workers in Human implies c in Dangerous
}
    S6 in valid iff {
	// Dangerous components cannot be assembled by humans
  all c: Component| all w: Worker| c in Dangerous iff w in Human
  //all c:Component| c.workers in Human implies c in Dangerous
}
    S7 in valid iff {
	// Dangerous components cannot be assembled by humans
  	all c : Component | no h : Human | c in Dangerous => h in c.workstation

}
    S8 in valid iff {
	// Dangerous components cannot be assembled by humans
	all o: Component | (o in Dangerous) implies (Human not in o.workstation)
}
    S9 in valid iff {
	// Dangerous components cannot be assembled by humans
	all o: Component | (o in Dangerous) implies (Human not in o.workstation.workers)
}
    S10 in valid iff {
	// Dangerous components cannot be assembled by humans
	all o: Component | (o in Dangerous) implies (Robot in o.workstation.workers)
}
    S11 in valid iff {
	// Dangerous components cannot be assembled by humans
	all o: Component | (o in Dangerous) implies (Robot in o.workstation.workers)
  	all o: Component | (o in Dangerous) implies (Human not in o.workstation.workers)
}
    S12 in valid iff {
	// Dangerous components cannot be assembled by humans
	//all o: Component | (o in Dangerous) implies (Robot in o.workstation.workers)
  	//all o: Component | (o in Dangerous) implies (Human not in o.workstation.workers)
	all o: Component, h: Human | some r: Robot | (o in Dangerous) implies (h not in o.workstation.workers)
}
    S13 in valid iff {
	// Dangerous components cannot be assembled by humans
  //all c: Component| all w: Worker| w in Human implies c in Dangerous
  //all c:Component| c.workers in Human implies c in Dangerous
  all c:Component | all work: c.workstation | c in Dangerous iff Human not in work.workers
  
}
    S14 in valid iff {
	// Dangerous components cannot be assembled by humans
  //all c: Component| all w: Worker| w in Human implies c in Dangerous
  //all c:Component| c.workers in Human implies c in Dangerous
  all c:Component | all work: c.workstation | Human not in work.workers implies c in Dangerous 
}
    S15 in valid iff {
	// Dangerous components cannot be assembled by humans
  //all c: Component| all w: Worker| w in Human implies c in Dangerous
  //all c:Component| c.workers in Human implies c in Dangerous
  some c:Component | all work: c.workstation | c in Dangerous implies Human not in work.workers
  
}
    S16 in valid iff {
	// Dangerous components cannot be assembled by humans
  //all c: Component| all w: Worker| w in Human implies c in Dangerous
  //all c:Component| c.workers in Human implies c in Dangerous
  all c:Component | all work: c.workstation | c in Dangerous iff Human not in work.workers and Robot in work.workers
  
}
    S17 in valid iff {
	// Dangerous components cannot be assembled by humans
  //all c: Component| all w: Worker| w in Human implies c in Dangerous
  //all c:Component| c.workers in Human implies c in Dangerous
  all c:Component | all work: c.workstation | c in Dangerous iff Robot in work.workers
  
}
    S18 in valid iff {
	// Dangerous components cannot be assembled by humans
  //all c: Component| all w: Worker| w in Human implies c in Dangerous
  //all c:Component| c.workers in Human implies c in Dangerous
  all c:Component | some work: c.workstation | c in Dangerous iff no Human & work.workers
  
}
    S19 in valid iff {
	// Dangerous components cannot be assembled by humans
  all c:Component, w:Workstation | Dangerous in c.^parts implies w.workers not in Human 

}
    S20 in valid iff {
	// Dangerous components cannot be assembled by humans
  all c:Component, w:Workstation | Dangerous in c.^parts implies Human not in w.workers 

}
    S21 in valid iff {
	// Dangerous components cannot be assembled by humans
  all c:Component, w:c.workstation | Dangerous in c.^parts implies Human not in w.workers 

}
    S22 in valid iff {
	// Dangerous components cannot be assembled by humans
  all c:Component | (c in Dangerous) implies (c.workstation.workers in Human)

}
    S23 in valid iff {
	// Dangerous components cannot be assembled by humans
	all c: Component | (c in Dangerous) implies all w: Worker | w in Robot
}
    S24 in valid iff {
	// Dangerous components cannot be assembled by humans
	all x: Workstation | workstation.x in (Component & Dangerous) implies x.workers not in Human
}
    S25 in valid iff {
	// Dangerous components cannot be assembled by humans
    workers.Human & Dangerous.parts.workstation = none
}
    S26 in valid iff {
	// Dangerous components cannot be assembled by humans
  no d:Dangerous | no (Human & (d.^parts & Component).workstation.workers)

}
    S27 in valid iff {
	// Dangerous components cannot be assembled by humans
	(all c: Component|
  	c in Dangerous and c.workstation not in	(workers.Human))
}
    S28 in valid iff {
	// Dangerous components cannot be assembled by humans
	(all c: Component|
  	c in Dangerous and c.workstation not in (Workstation - workers.Human))
}
    S29 in valid iff {
	// Dangerous components cannot be assembled by humans
	(all c: Component|all ws: Workstation|
  	c in Dangerous and c.workstation in ws and no ws.workers & Human)
}
    S30 in valid iff {
	// Dangerous components cannot be assembled by humans
  	all c:Component | (c in Dangerous) implies (c.workstation in Robot)

}
    S31 in valid iff {
	// Dangerous components cannot be assembled by humans
	all p : Product, ws : Workstation | ws.workers in Robot implies p in Dangerous

}
    S32 in valid iff {
	// Dangerous components cannot be assembled by humans
	all p : Product, ws : Workstation | p in Dangerous implies ws.workers in Robot  

}
    S33 in valid iff {
	// Dangerous components cannot be assembled by humans
	all p : Product, ws : Workstation | p in Dangerous and ws.workers in Robot  

}
    S34 in valid iff { 
	// Dangerous components cannot be assembled by humans
	all c: Component | all wo: Workstation |all p: Product | all w: Worker| p in Dangerous and p in c.parts and wo in c.workstation and w in wo.workers implies w in Robot
}
    S35 in valid iff {
	// Dangerous components cannot be assembled by humans
    all c:Dangerous | some (c.workstation.workers & Human)
}
    S36 in valid iff {
	// Dangerous components cannot be assembled by humans
	all c : Component | (c.^parts in Dangerous) implies Robot in c.workstation.workers
}
    S37 in valid iff {
	// Dangerous components cannot be assembled by humans
	all c : Component | (c.^parts in Dangerous) implies c.workstation.workers in Robot
}
    S38 in valid iff {
	// Dangerous components cannot be assembled by humans
  	Human not in (parts.Dangerous).workers

}
    S39 in valid iff {
	// Dangerous components cannot be assembled by humans
  	(parts.Dangerous).workers not in Human

}
    S40 in valid iff {
	// Dangerous components cannot be assembled by humans
  	((Dangerous.workstation).workers) not in Human

}
    S41 in valid iff {
	// Dangerous components cannot be assembled by humans
  	all d: Dangerous | d in Component and d.workstation.workers in Robot

}
    S42 in valid iff {
	// Dangerous components cannot be assembled by humans
  	all c : Component | no h : Human | c in Dangerous => h in c.workstation.workers

}
    S43 in valid iff {
	// Dangerous components cannot be assembled by humans
	all c : Component, ws : Workstation | (c.parts & Dangerous) not in (ws.workers & Human)
}
    S44 in valid iff {
	// Dangerous components cannot be assembled by humans
	all c: Component | some wo: Workstation | (c in Dangerous implies wo.workers not in Human)
}
    S45 in valid iff {
	// Dangerous components cannot be assembled by humans
  	Human not in Dangerous.workstation.workers
}
    S46 in valid iff {
	// Dangerous components cannot be assembled by humans
  	all d:Dangerous| Human not in d.workstation.workers
}
    S47 in valid iff {
	// Dangerous components cannot be assembled by humans
  	all c: Dangerous | no w: Worker | w in Human and c.workstation in w


}
    S48 in valid iff {
	// Dangerous components cannot be assembled by humans
	all d: Dangerous | Human not in Dangerous.parts
}
    S49 in valid iff {
	// Dangerous components cannot be assembled by humans
	//all c: Component, h: Human | c in Dangerous => h not in c.workstation.workers
  	all c: Component, h: Human | c in Dangerous => Human not in c.workstation.workers
}
    S50 in valid iff {
	// Dangerous components cannot be assembled by humans
	all ws: Workstation, h: Human|
  		(h in ws.workers) implies (some c: Component |c->ws in workstation implies c not in Dangerous)
}
    S51 in valid iff {
	// Dangerous components cannot be assembled by humans
	// all d : Dangerous | no (d.workstation).workers & Human 
  	no h : Human | h not in (Dangerous.workstation).workers 
}
    S52 in valid iff {
	// Dangerous components cannot be assembled by humans
	all d:Dangerous, ws:Workstation |  Human not in ws.workers implies ws in d.workstation
}
    S53 in valid iff {
	// Dangerous components cannot be assembled by humans
	all d:Dangerous, ws:Workstation | ws in d.workstation and Human not in ws.workers
}
    S54 in valid iff {
	// Dangerous components cannot be assembled by humans
	all c : Component | Dangerous in c implies
  no Human & c.workstation.workers
}
    S55 in valid iff {
	// Dangerous components cannot be assembled by humans
	all c : Component, w : Workstation, r : Robot | c in Dangerous implies w.workers in r
}
    S56 in valid iff {
	// Dangerous components cannot be assembled by humans
	all c : Component, w : Workstation, r : Robot | c = Dangerous implies w.workers in r
}
    S57 in valid iff {
	// Dangerous components cannot be assembled by humans
	all c: Component, ws: Workstation | some h: Human |
  		h in ws.workers => c not in Dangerous
}
    S58 in valid iff {
	// Dangerous components cannot be assembled by humans
	all p: Product, ws: Workstation | some h: Human |
  		h in ws.workers => p not in Dangerous
}
    S59 in valid iff {
	// Dangerous components cannot be assembled by humans
	all p: Product, ws: Workstation | some h: Human |
  		(h in ws.workers) and (ws in p.workstation) => (p not in Dangerous)
}
    S60 in valid iff {
	// Dangerous components cannot be assembled by humans
	all c: Component, ws: Workstation | some h: Human |
  		(h in ws.workers and ws in c.workstation) => (c not in Dangerous)
}
    S61 in valid iff {
	// Dangerous components cannot be assembled by humans
	all ws: Workstation | some h: Human, c: Component |
  		(h in ws.workers and ws in c.workstation) => (c not in Dangerous)
}
    S62 in valid iff {
	// Dangerous components cannot be assembled by humans
	all c: Component | all p: Product | all w: Worker| p in Dangerous and p in c.parts implies w in Robot
}
    S63 in valid iff {
	// Dangerous components cannot be assembled by humans
	all ws : Workstation | some d : (Component & Dangerous) | ws in d.workstation implies Human not in ws.workers
}
    S64 in valid iff {
	// Dangerous components cannot be assembled by humans
	all ws : Workstation | some d : Dangerous | ws in d.workstation implies Human not in ws.workers
}
    S65 in valid iff {
	// Dangerous components cannot be assembled by humans
	all ws : Workstation | some d : Dangerous | ws in d.workstation implies ws.workers not in Human
}
    S66 in valid iff {
	// Dangerous components cannot be assembled by humans
  	all c : Component, h : Human | (c.workstation.workers in Human) iff (c in Dangerous)

}
    S67 in valid iff {
	// Dangerous components cannot be assembled by humans
  	all c : Component, h : Human | (c.workstation.workers not in Human) iff (c in Dangerous)

}
    S68 in valid iff {
	// Dangerous components cannot be assembled by humans
  all c: Component, p: Product, h: Human, ws: Workstation | p in Dangerous implies (not h in ws.workers) 

}
    S69 in valid iff {
	// Dangerous components cannot be assembled by humans
	all c : Component, h : Human, wo : Workstation | c in workstation.wo
  
}
    S70 in valid iff {
	// Dangerous components cannot be assembled by humans
  all c : Component | Dangerous in c implies Human not in c.workstation

}
    S71 in valid iff {
	// Dangerous components cannot be assembled by humans
  all c : Component | Dangerous in c implies Human not in c.workstation.workers

}
    S72 in valid iff {
	// Dangerous components cannot be assembled by humans
	all c : Component | c in Dangerous => c.workstation.workers = Human
}
    S73 in valid iff {
	// Dangerous components cannot be assembled by humans
	all c: Component | c in Dangerous implies all ws: Workstation | c.workstation != ws or no h: Human | h not in ws.workers
//) | no ws: Workstation and all h: Human | h not in ws.workers
}
    S74 in valid iff {
	// Dangerous components cannot be assembled by humans
	all c: Component | c in Dangerous implies all ws: Workstation | c.workstation = ws and no h: Human | h not in ws.workers
//) | no ws: Workstation and all h: Human | h not in ws.workers
}
    S75 in valid iff {
	// Dangerous components cannot be assembled by humans
	all c: Component | c in Dangerous implies all ws: Workstation | c.workstation = ws and no h: Human | h in ws.workers
}
    S76 in valid iff {
	// Dangerous components cannot be assembled by humans
  
  all d:Dangerous, ws:Workstation, r:Robot | d.workstation.workers in Robot 

}
    S77 in valid iff {
	// Dangerous components cannot be assembled by humans
	not(all c:Component, ws: Workstation| c in Dangerous & (ws.workers & Human))
}
    S78 in valid iff {
	// Dangerous components cannot be assembled by humans
	all c:Component, ws: Workstation|
  	 (c in Dangerous and no(ws.workers & Human))
}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, S74, S75, S76, S77, S78 extends Formula {}

run {
    #valid.Oracle = 1
    #(Instance - valid.Oracle) = 1
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 12 Atom, exactly 4 WorkstationAtom, exactly 4 WorkerAtom, exactly 4 ProductAtom,
       exactly 2 Instance, 6 Int
