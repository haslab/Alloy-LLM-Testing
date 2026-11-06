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
    Oracle in valid iff {
	// Components built of dangerous parts are also dangerous
	all c: Component | some (c.parts & Dangerous) implies c in Dangerous
}
    S1 in valid iff {
	// Components built of dangerous parts are also dangerous
  all c:Component| some p:Product | (p in Dangerous and p in c.parts) implies c in Dangerous

}
    S2 in valid iff {
	// Components built of dangerous parts are also dangerous
    all d : Dangerous | d.parts in Dangerous
}
    S3 in valid iff {
	// Components built of dangerous parts are also dangerous
  	all c: Component | some p: c.parts | p in Dangerous implies c in Dangerous

}
    S4 in valid iff {
	// Components built of dangerous parts are also dangerous
  	all c: Component | c in Dangerous implies some p: c.parts| p in Dangerous

}
    S5 in valid iff {
	// Components built of dangerous parts are also dangerous
  	all c: Component | c in Dangerous implies some p: parts.c| p in Dangerous

}
    S6 in valid iff {
	// Components built of dangerous parts are also dangerous
  	all c: Component | c in Dangerous iff some p: c.parts | p in Dangerous
  	

}
    S7 in valid iff {
	// Components built of dangerous parts are also dangerous
  	//all c: Component | c in Dangerous implies some p: c.parts | p in Dangerous
  	all c:Component | some p: parts.c| p in Dangerous implies c in Dangerous

}
    S8 in valid iff {
	// Components built of dangerous parts are also dangerous
	all o: Component | (Dangerous in o.parts)
}
    S9 in valid iff {
	// Components built of dangerous parts are also dangerous
	all o: Component | (Dangerous in o.parts) implies o = Dangerous
}
    S10 in valid iff {
	// Components built of dangerous parts are also dangerous
	all o: Component | (Dangerous in o.^parts) implies (o in Dangerous)
}
    S11 in valid iff {
	// Components built of dangerous parts are also dangerous
	all o: Component | (o.^parts in Dangerous) implies (o in Dangerous)
}
    S12 in valid iff {
	// Components built of dangerous parts are also dangerous
  	//all c: Component | c in Dangerous implies some p: c.parts | p in Dangerous
  	all c:Component | some p: c.parts| p in Dangerous iff c in Dangerous

}
    S13 in valid iff {
	// Components built of dangerous parts are also dangerous
  	//all c: Component | c in Dangerous implies some p: c.parts | p in Dangerous
  	all c:Component | all p: c.parts| p in Dangerous iff c in Dangerous

}
    S14 in valid iff {
	// Components built of dangerous parts are also dangerous
  all c:Component | Dangerous in c.^parts implies Dangerous in c 

}
    S15 in valid iff {
	// Components built of dangerous parts are also dangerous
	//all c:Component | some e:c.^(parts)| e in Dangerous implies c in Dangerous }
	all c:Component | some (c.^(parts) & Dangerous) }
    S16 in valid iff {
	// Components built of dangerous parts are also dangerous
	//all c:Component | some e:c.^(parts)| e in Dangerous implies c in Dangerous }
	all c:Component | some (c.parts & Dangerous) }
    S17 in valid iff {
	// Components built of dangerous parts are also dangerous
	all c : Component | c in Dangerous
}
    S18 in valid iff {
	// Components built of dangerous parts are also dangerous
	all c : Component | c.parts in Dangerous 
}
    S19 in valid iff {
	// Components built of dangerous parts are also dangerous
  all c: Component | (c in Dangerous) and (c.parts in Dangerous)

}
    S20 in valid iff {
	// Components built of dangerous parts are also dangerous
	all c : Component | some d : Dangerous | d in c.^parts <=> c in Dangerous
}
    S21 in valid iff {
	// Components built of dangerous parts are also dangerous
  
	all c1,c2:Component | c1->c2 in parts and c1 in Dangerous implies c2 in Dangerous  

}
    S22 in valid iff {
	// Components built of dangerous parts are also dangerous
	all p: Product | some pp:p.parts | pp in Dangerous implies p in Dangerous
}
    S23 in valid iff {
	// Components built of dangerous parts are also dangerous
  all c:Component |
  	one p:c.^parts |
  		p in Dangerous implies c in Dangerous

}
    S24 in valid iff {
	// Components built of dangerous parts are also dangerous
    all c : Component | Dangerous in c.^(parts) implies some Dangerous

}
    S25 in valid iff {
	// Components built of dangerous parts are also dangerous
    all c : Component | (some x: c.parts | x in Dangerous) implies (Dangerous in c)

}
    S26 in valid iff {
	// Components built of dangerous parts are also dangerous
    //all c : Component | Dangerous in c.^(parts) implies Dangerous in c
  all c: Component | some p: c.parts | p in Dangerous implies Dangerous in c

}
    S27 in valid iff {
	// Components built of dangerous parts are also dangerous
    all c : Component | Dangerous in c.parts implies Dangerous in c

}
    S28 in valid iff {
	// Components built of dangerous parts are also dangerous
    all c : Component | Dangerous in c.~parts implies Dangerous in c

}
    S29 in valid iff {
	// Components built of dangerous parts are also dangerous
	all c : Component | one d : Dangerous | d in c.parts => c in Dangerous
}
    S30 in valid iff {
	// Components built of dangerous parts are also dangerous
	all c : Component | one d : Dangerous | d in c.^parts => c in Dangerous
}
    S31 in valid iff {
	// Components built of dangerous parts are also dangerous
	all c: Component | c in Dangerous iff Dangerous in c.^parts
}
    S32 in valid iff {
	// Components built of dangerous parts are also dangerous
	all c, c1 : Component | (c1 in c.^parts and c1 in Dangerous) implies c in Dangerous
}
    S33 in valid iff {
	// Components built of dangerous parts are also dangerous
  	all c : Component | some p : c.parts&Dangerous | c in Dangerous
  
}
    S34 in valid iff {
	// Components built of dangerous parts are also dangerous
  //all c : Component | Dangerous in c.parts implies c in Dangerous
	
  all c : Component | lone p : Product | p in c.parts and p in Dangerous implies c in Dangerous
}
    S35 in valid iff {
	// Components built of dangerous parts are also dangerous
	some d: Dangerous | some c: Component| d in c.parts implies c in Dangerous
}
    S36 in valid iff {
	// Components built of dangerous parts are also dangerous
    ((Component - Dangerous) -> Dangerous) not in parts

}
    S37 in valid iff {
	// Components built of dangerous parts are also dangerous
	all c : Product | (c.^parts in Dangerous) implies c in Dangerous
}
    S38 in valid iff {
	// Components built of dangerous parts are also dangerous
	all c : Component | not (c.^parts in Dangerous) implies c  in Dangerous
}
    S39 in valid iff {
	// Components built of dangerous parts are also dangerous
	all c:Component |
  		one p:c.parts|
  			p in Dangerous implies c in Dangerous
}
    S40 in valid iff {
	// Components built of dangerous parts are also dangerous
	all c: Component | (some c: Component | c.^parts in Dangerous) implies c in Dangerous
}
    S41 in valid iff {
	// Components built of dangerous parts are also dangerous
	all c: Component | (some c: Component | c.parts in Dangerous) implies c in Dangerous
}
    S42 in valid iff {
	// Components built of dangerous parts are also dangerous
	no c: Component | some c.parts & Dangerous implies c in Dangerous
}
    S43 in valid iff {
	// Components built of dangerous parts are also dangerous
	all p: Product | (p in Dangerous) <=> some p2: Product | p2 != p and p2 in p.parts and p2 in Dangerous
}
    S44 in valid iff {
	// Components built of dangerous parts are also dangerous
	Dangerous & Component.^parts = Dangerous
}
    S45 in valid iff {
	// Components built of dangerous parts are also dangerous
		all c:Component | ^parts.c in Dangerous
}
    S46 in valid iff {
	// Components built of dangerous parts are also dangerous
	all p: Product | Dangerous in p.^parts => p in Dangerous
}
    S47 in valid iff {
	// Components built of dangerous parts are also dangerous
	all c : Component, p : Product | p in Dangerous implies c in Dangerous
}
    S48 in valid iff {
	// Components built of dangerous parts are also dangerous
  	//all c: Component | some c.^parts & Dangerous => c in Dangerous
  	Dangerous in Component implies Dangerous.parts in Dangerous
}
    S49 in valid iff {
	// Components built of dangerous parts are also dangerous
	all c:Component | c in Dangerous implies parts.Product in Dangerous
}
    S50 in valid iff {
	// Components built of dangerous parts are also dangerous
  
  all c : Component | no c.((^(parts)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) & Dangerous 

}
    S51 in valid iff {
	// Components built of dangerous parts are also dangerous
  all c:Component, d:Dangerous| d.parts in c.parts implies c in d

}
    S52 in valid iff {
	// Components built of dangerous parts are also dangerous
  all c:Component, d:Dangerous| d.parts in c.parts implies c = Dangerous

}
    S53 in valid iff {
	// Components built of dangerous parts are also dangerous
  all c:Component, d:Dangerous| d.parts in c.^parts implies c = Dangerous

}
    S54 in valid iff {
	// Components built of dangerous parts are also dangerous
	all c: Component | Dangerous in c.parts implies c.parts in Dangerous
}
    S55 in valid iff {
	// Components built of dangerous parts are also dangerous
	all c: Component | one d: Dangerous| d in c.parts implies c.parts in Dangerous
}
    S56 in valid iff {
	// Components built of dangerous parts are also dangerous
  	all c : Component | c.parts in Dangerous.parts implies c in Dangerous
}
    S57 in valid iff {
	// Components built of dangerous parts are also dangerous
	all c : Component | some p : Dangerous.parts | p in c.parts implies c in Dangerous
}
    S58 in valid iff {
	// Components built of dangerous parts are also dangerous
	all c : Component | all p : Dangerous.parts | p in c.parts implies c in Dangerous
}
    S59 in valid iff {
	// Components built of dangerous parts are also dangerous
	all c : Component | one p : Dangerous.parts | p in c.parts implies c in Dangerous
}
    S60 in valid iff {
	// Components built of dangerous parts are also dangerous
  	all c : Component | some ( c.^(parts.parts) & Dangerous ) implies c in Dangerous
	
}
    S61 in valid iff {
	// Components built of dangerous parts are also dangerous
  
  all c : Component | c in Dangerous iff c.^parts in Dangerous 

}
    S62 in valid iff {
	// Components built of dangerous parts are also dangerous
	all c: Component | Dangerous in c implies Dangerous in ^parts.c
}
    S63 in valid iff {
	// Components built of dangerous parts are also dangerous
	all c: Component | (Dangerous in c) implies ^parts.c in Dangerous
}
    S64 in valid iff {
	// Components built of dangerous parts are also dangerous
	all c: Component | (Dangerous in c) implies all p : ^parts.c |
  Dangerous in p
}
    S65 in valid iff {
	// Components built of dangerous parts are also dangerous
  all c: Component | Dangerous in c.parts implies Dangerous in Component

}
    S66 in valid iff {
	// Components built of dangerous parts are also dangerous
	some c: Component | c.parts in Dangerous => c in Dangerous
}
    S67 in valid iff {
	// Components built of dangerous parts are also dangerous
	some c: Component | some (c.parts & Dangerous) => c in Dangerous
}
    S68 in valid iff {
	// Components built of dangerous parts are also dangerous
  	all c : Component | some d : Dangerous | Dangerous = c.parts implies c in Dangerous

}
    S69 in valid iff {
	// Components built of dangerous parts are also dangerous
  	all c : Component, p : Product | (c.parts in Dangerous) iff (p in Dangerous)

}
    S70 in valid iff {
	// Components built of dangerous parts are also dangerous
  all c: Component|one c.parts & Dangerous implies c in Dangerous

}
    S71 in valid iff {
	// Components built of dangerous parts are also dangerous
  some c : Component.parts | all c1 : Component | c1 in c 

}
    S72 in valid iff {
	// Components built of dangerous parts are also dangerous
  some c : Component.parts | all c1 : Component | c in c1 and c in Dangerous implies c1 in Dangerous

}
    S73 in valid iff {
	// Components built of dangerous parts are also dangerous
  //some c : Component.parts | all c1 : Component | c in c1 and c in Dangerous implies c1 in Dangerous
  some c : Component | c in Dangerous

}
    S74 in valid iff {
	// Components built of dangerous parts are also dangerous
	all c : Component, p : Product | c in p.parts implies (c in Dangerous and p in Dangerous)
}
    S75 in valid iff {
	// Components built of dangerous parts are also dangerous
	all c : Component | some (c.parts & Dangerous) implies no (c.parts & (Product - Dangerous))
}
    S76 in valid iff {
	// Components built of dangerous parts are also dangerous
	(Dangerous <: parts) in Dangerous -> some Product
}
    S77 in valid iff {
	// Components built of dangerous parts are also dangerous
	all c:Component | c.^parts not in Dangerous
}
    S78 in valid iff {
	// Components built of dangerous parts are also dangerous
  	all c : Component | c in Dangerous implies (some p : c.^parts | p in Dangerous)

}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, S74, S75, S76, S77, S78 extends Formula {}

run {
    #valid.Oracle = 2
    #(Instance - valid.Oracle) = 2
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 12 Atom, exactly 4 WorkstationAtom, exactly 4 WorkerAtom, exactly 4 ProductAtom,
       exactly 4 Instance, 6 Int
