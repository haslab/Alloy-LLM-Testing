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
    Oracle in valid iff {
	// Components cannot be their own parts
	all c: Component | c not in c.^parts
}
    S1 in valid iff {
  // Components cannot be their own parts
  all c: Component | c not in c.parts
}
    S2 in valid iff {
	// Components cannot be their own parts

}
    S3 in valid iff {
	// Components cannot be their own parts
  all c : Component| no (Component & c.parts)

}
    S4 in valid iff {
	// Components cannot be their own parts
no disj c, p: Component | c in p.parts
}
    S5 in valid iff {
	// Components cannot be their own parts
  	one c:Component | c not in c.parts

}
    S6 in valid iff {
	// Components cannot be their own parts
  	some c:Component | c not in c.parts

}
    S7 in valid iff {
	// Components cannot be their own parts
	no c:Component | c not in parts.c
}
    S8 in valid iff {
	// Components cannot be their own parts
  //all c:Component | some c.parts
	//all c:Component | c not in c.parts
 Component not in Component.parts
}
    S9 in valid iff {
	// Components cannot be their own parts
  //all c:Component | some c.parts
	one c:Component | c not in c.parts
  no Component.parts
 //Component not in Component.parts
}
    S10 in valid iff {
	// Components cannot be their own parts
	all c: Component | no c.parts
  
}
    S11 in valid iff {
	// Components cannot be their own parts
  //all c:Component | some c.parts
	all c1, c2:Component | c1=c2 iff c1 not in c2.parts
  //no Component.parts
 //Component not in Component.parts
}
    S12 in valid iff {
	// Components cannot be their own parts
	all c: Component | c not in c.parts and c not in c.parts.parts
}
    S13 in valid iff {
	// Components cannot be their own parts
  all c:Component | all p: c.parts | c not in p iff p not in parts.c
	//all c1, c2:Component | c1=c2 implies c1 not in c2.parts
  //no Component.parts
 //Component not in Component.parts
}
    S14 in valid iff {
	// Components cannot be their own parts
  all c:Component | some p: c.parts | c not in p iff p not in parts.c
	//all c1, c2:Component | c1=c2 implies c1 not in c2.parts
  //no Component.parts
 //Component not in Component.parts
}
    S15 in valid iff {
	// Components cannot be their own parts
  all c:Component | some p: c.parts | c not in p and p not in parts.c
	//all c1, c2:Component | c1=c2 implies c1 not in c2.parts
  //no Component.parts
 //Component not in Component.parts
}
    S16 in valid iff {
	// Components cannot be their own parts
	no c: Component, d: Dangerous | c in Component
}
    S17 in valid iff {
	// Components cannot be their own parts
     all c : Component | one c & Component.parts 
}
    S18 in valid iff {
	// Components cannot be their own parts
	all c : Component | c not in c.parts
  	all c1 : Component | all c2 : Component | c1 in c2.parts implies c2 in c1.parts
}
    S19 in valid iff {
	// Components cannot be their own parts
  	all c1 : Component | all c2 : Component | c1 in c2.parts implies c2 in c1.parts
}
    S20 in valid iff {
	// Components cannot be their own parts
	Component.parts != Component
}
    S21 in valid iff {
	// Components cannot be their own parts
	all c: Component | c.parts != c
}
    S22 in valid iff {
	// Components cannot be their own parts
  	all x,y,z: Component| (y in x.parts and z in y.parts ) implies x not in (z.parts) 

}
    S23 in valid iff {
	// Components cannot be their own parts
	one c: Component | c not in c.^(parts)
}
    S24 in valid iff {
	// Components cannot be their own parts
  	all p : Product | not p in p.parts implies p in Component
}
    S25 in valid iff {
	// Components cannot be their own parts
	all p : Product | (no p.parts & p) implies (p in Component or p in Dangerous)
}
    S26 in valid iff {
	// Components cannot be their own parts
	all p : Product | (no p.parts & p) implies (p in Component and p in Dangerous)
}
    S27 in valid iff {
	// Components cannot be their own parts
	all p : Product | (no p.^parts & p) implies (p in Component and p in Dangerous)
}
    S28 in valid iff {
	// Components cannot be their own parts
	all c : Component | c.parts = c.^parts-c 
}
    S29 in valid iff {
	// Components cannot be their own parts
  	lone c: Component | c not in c.parts

}
    S30 in valid iff {
	// Components cannot be their own parts
	(Component <: parts) not in ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)
}
    S31 in valid iff {
	// Components cannot be their own parts
	(Component <: parts :> Component) not in ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)
}
    S32 in valid iff {
	// Components cannot be their own parts
	all c : Component | c.parts not in Component
}
    S33 in valid iff {
	// Components cannot be their own parts
	Component.parts not in Component
}
    S34 in valid iff {
	// Components cannot be their own parts
	all p: Product | no (p & p.parts) iff p in Component
}
    S35 in valid iff {
	// Components cannot be their own parts
	all p: Product |
  		some c: Component | p=c implies p not in c.parts
}
    S36 in valid iff {
	// Components cannot be their own parts
	all p: Product | 
  		(p in Component) implies (some c: Component |  p not in c.parts)
}
    S37 in valid iff {
	// Components cannot be their own parts
  	all c : Component | Component not in c.parts

}
    S38 in valid iff {
	// Components cannot be their own parts
  
  all p : Product, c : Component  | p->c not in parts implies p = c

}
    S39 in valid iff {
	// Components cannot be their own parts
	all c : Component | some p : Product | p.parts not in c
  }
    S40 in valid iff {
	// Components cannot be their own parts
	all p: Product | no p.((^(parts)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
}
    S41 in valid iff {
	// Components cannot be their own parts
	all p: Product | p in p.parts
}
    S42 in valid iff {
	// Components cannot be their own parts
  
  all c : Component | parts.~parts not in ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)

}
    S43 in valid iff {
	// Components cannot be their own parts
  
  all c : Component | ^parts.~parts not in ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)

}
    S44 in valid iff {
	// Components cannot be their own parts
	//no (^parts & iden)
  	Component <: ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden) not in ^parts
}
    S45 in valid iff {
	// Components cannot be their own parts
  all c, c1, c2: Component | (c1 in c.parts implies c not in c1.parts) or (c in c1.parts and c1 in c2.parts implies c2 not in c.parts)

}
    S46 in valid iff {
	// Components cannot be their own parts
  all c, c1, c2: Component | (c1 in c.parts implies c not in c1.parts) and (c in c1.parts and c1 in c2.parts implies c2 not in c.parts)

}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46 extends Formula {}

run {
    #valid.Oracle = 1
    #(Instance - valid.Oracle) = 1
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 12 Atom, exactly 4 WorkstationAtom, exactly 4 WorkerAtom, exactly 4 ProductAtom,
       exactly 2 Instance, 6 Int
