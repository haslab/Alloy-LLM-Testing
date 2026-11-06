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
    // Earlier requirement 7, required in every Instance.
{
	// Dangerous components cannot be assembled by humans
	all c: (Component & Dangerous) | no c.workstation.workers & Human
}
    // Earlier requirement 8, required in every Instance.
{
	// The workstations form a single line between begin and end
  
  	all w : Workstation | w in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  
  	all w : Workstation - end | one w.succ
  
  	no end.succ
	
}
    Oracle in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c : Component, p : c.parts & Component | c.workstation in p.workstation.^succ
}
    S1 in valid iff {
	// The parts of a component must be assembled before it in the production line

}
    S2 in valid iff {
	// The parts of a component must be assembled before it in the production line
  all c: Component | let
		ws = c.workstation,
		prevParts = (ws.succ.parts - c.parts) | 
		prevParts not in ws.parts

}
    S3 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c: Component | all p: c.parts | p.workstation in c.workstation.^succ
}
    S4 in valid iff {
	// The parts of a component must be assembled before it in the production line
  all c : Component |no c.parts.workstation & c.workstation.^succ
}
    S5 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all a, b: Component | a in b.parts implies b in a.workstation.^succ
}
    S6 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c: Component, p: c.parts |
        all ws: c.workstation, wsPart: p.workstation |
            wsPart in ws.(~succ) 
}
    S7 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c : Component | no(parts.c.workstation & c.workstation.^succ)
}
    S8 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c : Component, p : (c.parts) | no( c.workstation.succ & p.workstation.succ)
}
    S9 in valid iff {
	// The parts of a component must be assembled before it in the production line
	// all c : Component | one (c.workstation).succ => 
  all c : Component | all c1 : c.parts & Component | one c1.workstation and c1.workstation != end => no c.workstation
}
    S10 in valid iff {
	// The parts of a component must be assembled before it in the production line
	// all c : Component | one (c.workstation).succ => 
  // all c : Component | one c.workstation implies (all c1 : (^parts).c & Component | c1.workstation != c.workstation)
  all c : Component | c.workstation != begin => all p : c.parts & Component | p.workstation = end
}
    S11 in valid iff {
	// The parts of a component must be assembled before it in the production line
	// all c : Component | one (c.workstation).succ => 
  all c : Component | c.workstation != end => all c1 : parts.c & Component | c1.workstation != c.workstation and c1.workstation = begin
}
    S12 in valid iff {
	// The parts of a component must be assembled before it in the production line
	// all c : Component | one (c.workstation).succ => 
  all c : Component, c1 : parts.c & Component | (one c.workstation.succ and c1.workstation = begin) or (c.workstation = end and c1.workstation != begin)
}
    S13 in valid iff {
	// The parts of a component must be assembled before it in the production line
	// all c : Component | one (c.workstation).succ => 
  all c : Component, c1 : parts.c & Component | (one c.workstation.succ and no c1.workstation) or (c.workstation = end and c1.workstation != begin)
}
    S14 in valid iff {
	// The parts of a component must be assembled before it in the production line
	// all c : Component | one (c.workstation).succ => 
  all c : Component, c1 : parts.c & Component | (one c.workstation.succ and c1.workstation = begin) or (no c.workstation and one c1.workstation)
}
    S15 in valid iff {
	// The parts of a component must be assembled before it in the production line
	// all c : Component | one (c.workstation).succ => 
  all c : Component | c.workstation != begin => all c1 : parts.c & Component | c1.workstation = end
}
    S16 in valid iff {
	// The parts of a component must be assembled before it in the production line
	// all c : Component | one (c.workstation).succ => 
  all c : Component | c.workstation = begin => all c1 : c.parts & Component | c1.workstation = begin or no c1.workstation
}
    S17 in valid iff {
	// The parts of a component must be assembled before it in the production line
	// all c : Component | one (c.workstation).succ => 
  all c : Component | c.workstation = begin => all c1 : parts.c & Component | c1.workstation = begin or no c1.workstation
}
    S18 in valid iff {
	// The parts of a component must be assembled before it in the production line
    all c : Component | c.workstation not in begin implies no c.parts.workstation

}
    S19 in valid iff {
	// The parts of a component must be assembled before it in the production line
	// all c : Component | one (c.workstation).succ => 
  all c : Component | one c.workstation implies (all c1 : (^parts).c & Component | c1.workstation = end)
}
    S20 in valid iff {
	// The parts of a component must be assembled before it in the production line
	// all c : Component | one (c.workstation).succ => 
  all c : Component | one c.workstation implies (all c1 : (^parts).c & Component | c1.workstation = end and c1.workstation != begin)
}
    S21 in valid iff {
	// The parts of a component must be assembled before it in the production line
	// all c : Component | one (c.workstation).succ => 
  all c : Component | one c.workstation implies (all c1 : (^parts).c & Component | c1.workstation != c.workstation)
}
    S22 in valid iff {
	// The parts of a component must be assembled before it in the production line
	// all c : Component | one (c.workstation).succ => 
  all c : Component | c.workstation != begin implies (all c1 : (^parts).c & Component | c1.workstation != c.workstation)
  //all c : Component | (some p : c.parts & Component | p.workstation != end) implies c.workstation = begin
}
    S23 in valid iff {
	// The parts of a component must be assembled before it in the production line

    all c: Component | all p: c.parts | (c.workstation in p.workstation.succ) or (c.workstation in begin and p.workstation in end)
}
    S24 in valid iff {
	// The parts of a component must be assembled before it in the production line

    all c: Component | all p: c.parts | (c.workstation in p.workstation.succ) or (c.workstation in end and p.workstation in begin)
}
    S25 in valid iff {
	// The parts of a component must be assembled before it in the production line

    all c: Component | all p: c.parts | ((c.workstation in p.workstation.succ) or (c.workstation in end and p.workstation in begin)) or c.workstation = p.workstation
}
    S26 in valid iff {
	// The parts of a component must be assembled before it in the production line
	(all c: Component|
  	c.parts.workstation in end iff c.workstation in begin)
}
    S27 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c: Component | all wsfromParts:c.^parts.workstation.^succ | c.workstation in wsfromParts
}
    S28 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c:Component | all p:c.parts | c.workstation not in p.^workstation
}
    S29 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c : Component | Workstation in ((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)).c.workstation 
}
    S30 in valid iff {
  // The parts of a component must be assembled before it in the production line
  all c:Component | c.workstation.succ in c.parts.workstation.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) 
}
    S31 in valid iff {
  // The parts of a component must be assembled before it in the production line
  all c:Component | some (c.parts & Component) => c.workstation in  c.parts.workstation.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))

}
    S32 in valid iff {
  // The parts of a component must be assembled before it in the production line
  all c:Component | some (c.parts & Component) => c.workstation in c.parts.workstation.^succ

}
    S33 in valid iff {
  // The parts of a component must be assembled before it in the production line
  all c:Component | some (c.parts & Component) => c.workstation.^succ in c.parts.workstation.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))

}
    S34 in valid iff {
  // The parts of a component must be assembled before it in the production line
  all c:Component | some (c.parts & Component) => c.workstation.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) in c.parts.workstation

}
    S35 in valid iff {
  // The parts of a component must be assembled before it in the production line
  all c:Component | some (c.parts & Component) => c.workstation.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) in c.((^(parts)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)).workstation

}
    S36 in valid iff {
  // The parts of a component must be assembled before it in the production line
  all c:Component | no c.parts or some (c.parts & Component) => c.parts.workstation not in c.workstation

}
    S37 in valid iff {
  // The parts of a component must be assembled before it in the production line
  all c:Component | some (c.parts & Component) => c.parts.workstation.^succ not in c.workstation.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))

}
    S38 in valid iff {
  // The parts of a component must be assembled before it in the production line
  all c:Component | some (c.parts & Component) => c.parts.workstation.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) not in c.workstation.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  Component.workstation != Component.parts.workstation

}
    S39 in valid iff {
  // The parts of a component must be assembled before it in the production line
  all c:Component | some (c.parts & Component) => c.parts.workstation.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) not in c.workstation

}
    S40 in valid iff {
  // The parts of a component must be assembled before it in the production line
  all c:Component | some (c.parts & Component) => c.workstation in c.parts.workstation

}
    S41 in valid iff {
  // The parts of a component must be assembled before it in the production line
  all c:Component | some (c.parts & Component) => c.workstation in c.^parts.workstation.^succ

}
    S42 in valid iff {
  // The parts of a component must be assembled before it in the production line
  all c:Component | some (c.parts & Component) => c.workstation in c.parts.workstation.^succ && c.workstation not in c.parts.workstation

}
    S43 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c: Component | c.workstation not in begin
}
    S44 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c: Component | Workstation in c.workstation => all p: c.parts | Workstation in c
}
    S45 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c: Component | one ws1: Workstation | ws1 in c.workstation => all p: c.parts | one ws2: Workstation | ws2 in p.workstation
}
    S46 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c: Component | one ws1: Workstation | ws1 in c.workstation => all p: c.parts | one ws2: Workstation | ws2 in p.workstation or p in Material
}
    S47 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c: Component | one ws1: Workstation | ws1 in c.workstation => all p: c.^parts | one ws2: Workstation | ws2 in p.workstation or p in Material
}
    S48 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c: Component | one ws: Workstation | ws in c.workstation => all p: c.parts | ws in p.workstation.^succ
}
    S49 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c: Component | one ws: Workstation | ws in c.workstation => all p: c.parts | ws in p.workstation.^succ or p in Material
}
    S50 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c : Component | c.parts.workstation in c.workstation 
}
    S51 in valid iff {
	// The parts of a component must be assembled before it in the production line
	no Workstation
}
    S52 in valid iff {
	// The parts of a component must be assembled before it in the production line
	some Component.parts
}
    S53 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c : Component | c in Component.parts implies end not in c.workstation
}
    S54 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c : Component | parts.c in Component implies c.~parts.workstation in c.workstation.~succ 
}
    S55 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c: Component, p: c.parts | c.workstation.succ in p.workstation
}
    S56 in valid iff {
	// The parts of a component must be assembled before it in the production line
  	all c: Component, p: Component |
  		p in c.^parts => p.workstation in c.workstation.~succ
}
    S57 in valid iff {
	// The parts of a component must be assembled before it in the production line
  	all c: Component, p: Component |
  		p in c.^parts => p.workstation in c.workstation.succ
}
    S58 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c: Component, p: c.parts | p.workstation in (begin.^succ & c.workstation)

}
    S59 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c : Component | c.workstation = begin or c.workstation in c.parts.workstation.^succ
}
    S60 in valid iff {
  // The parts of a component must be assembled before it in the production line
  all c: Component, p: c.parts, ws_c: c.workstation, ws_p: p.workstation |
    ws_p in end and ws_p in ws_c.^succ
}
    S61 in valid iff {
  	// The parts of a component must be assembled before it in the production line
  	all c: Component, p: c.parts, ws_c: c.workstation, ws_p: p.workstation |
    	ws_p in ws_c.^succ and ws_p in begin.^succ and ws_c in begin.^succ
}
    S62 in valid iff {
  	// The parts of a component must be assembled before it in the production line
  	all c: Component, p: c.parts, ws_c: c.workstation | one ws_e : end |
    ws_e in ws_c.^succ 
}
    S63 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c: Component | all c_parts: (c.parts & Component) | 
  		some c.workstation implies 
  			some (c_parts.workstation & end) and no (c_parts.workstation & begin)
}
    S64 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c : Component | no c.parts or c.parts in Material or c.parts.workstation not in (c.workstation + c.workstation.^succ) or lone Workstation
}
    S65 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c : Component | (no c.parts or c.parts in Material or no (c.parts.workstation & (c.workstation + c.workstation.^succ)) or lone Workstation) and one c.workstation
}
    S66 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c:Component, ws:Workstation | (ws in (c.parts).workstation) or (ws in (c.parts).workstation.^succ) implies some none
}
    S67 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c:Component, ws:Workstation | ws in ((c.parts).workstation & (c.parts).workstation.^succ) implies some none
}
    S68 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c:Component, ws:Workstation | c.parts in Component and ws in (c.parts).workstation implies ws in (c.workstation & c.workstation.^succ) 
  }
    S69 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c:Component, ws:Workstation | c.parts in Component and ws in (c.parts).workstation and ws in (c.parts).workstation implies ws in c.workstation 

}
    S70 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c:Component, ws:Workstation | ws in (c.parts).workstation and ws in (c.parts).workstation.^succ implies ws in c.workstation 

}
    S71 in valid iff {
	// The parts of a component must be assembled before it in the production line
	  all c: Component, ws: Workstation, p: c.parts | ws in p.workstation or ws in p.workstation.^succ implies ws in c.workstation
}
    S72 in valid iff {
	// The parts of a component must be assembled before it in the production line
  all c1 : Component, c2 : Component  | c1.parts in c2.^parts implies c1.workstation not in c2.workstation.^succ

}
    S73 in valid iff {
	// The parts of a component must be assembled before it in the production line
  all c1 : Component, c2 : Component  | c1.parts in c2.parts implies c1.workstation not in c2.workstation.succ

}
    S74 in valid iff {
	// The parts of a component must be assembled before it in the production line
  all c1 : Component, c2 : Component  | c1 in c2.parts implies c1.workstation not in c2.workstation.succ

}
    S75 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c : Component |  c.workstation in c.parts.workstation.succ or c.parts.workstation = 	none
}
    S76 in valid iff {
	// The parts of a component must be assembled before it in the production line
	some c: Component, p: c.parts |
        some ws: c.workstation, wsPart: p.workstation |
            wsPart in ws.(~succ)
}
    S77 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all m:Material | some c:Component | m in c.parts and c.workstation = none
}
    S78 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all m:Material | m in Component.parts
}
    S79 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c: Component | c.^parts.workstation != none implies c.workstation in c.^parts.workstation.succ
}
    S80 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c: Component | c.^parts.workstation != none implies
  		c.workstation in c.^parts.workstation.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
}
    S81 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all p: Product | 
		some p.parts => 
			all c: p.parts |
				c.workstation = p.workstation.~succ
}
    S82 in valid iff {
	no c: Component | all p: c.parts |
		c.workstation in p.workstation.^succ
	// The parts of a component must be assembled before it in the production line
}
    S83 in valid iff {
	// The parts of a component must be assembled before it in the production line
	no c: Component | all p: c.parts |
		c.workstation in (p.workstation.~succ)
}
    S84 in valid iff {
	// The parts of a component must be assembled before it in the production line
	no c: Component | all p: c.parts |
		some p.workstation & c.workstation.^succ
}
    S85 in valid iff {
	// The parts of a component must be assembled before it in the production line
      all c: Component | all p: c.parts | p.workstation.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) in c.workstation


}
    S86 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c : Component | not c.workstation.^succ = c.parts.workstation 
}
    S87 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c : Component | no (c.parts & Component) or not (c.parts & Component).workstation = c.workstation.^succ
}
    S88 in valid iff {
	// The parts of a component must be assembled before it in the production line
	all c : Component | no (c.parts & Component) or (not (c.parts & Component).workstation = c.workstation.^succ and not (c.parts & Component).workstation = c.workstation)
}
    S89 in valid iff {
	// The parts of a component must be assembled before it in the production line
	//all c : Component | no (c.parts & Component) or (not (c.parts & Component).workstation = c.workstation.^succ and not (c.parts & Component).workstation = c.workstation)
  
  all c : Component | c.workstation = (c.parts & Component).workstation.^succ or 
  no c.parts & Component
}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, S74, S75, S76, S77, S78, S79, S80, S81, S82, S83, S84, S85, S86, S87, S88, S89 extends Formula {}

run {
    #valid.Oracle = 2
    #(Instance - valid.Oracle) = 2
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 12 Atom, exactly 4 WorkstationAtom, exactly 4 WorkerAtom, exactly 4 ProductAtom,
       exactly 4 Instance, 6 Int
