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
    Oracle in valid iff {
	// The workstations form a single line between begin and end
  
  	all w : Workstation | w in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  
  	all w : Workstation - end | one w.succ
  
  	no end.succ
	
}
    S1 in valid iff {
	// The workstations form a single line between begin and end
	one w: Workstation {
      no succ.w
      all k: Workstation - w | one k.succ
    }   
}
    S2 in valid iff {
	// The workstations form a single line between begin and end
	one first: Workstation, latest: Workstation {
      no succ.first
      no latest.succ
      all k: Workstation - first - latest | one k.succ
    }   
}
    S3 in valid iff {
	// The workstations form a single line between begin and end
	one first: Workstation, latest: Workstation {
      no succ.first
      no latest.succ
      all k: Workstation - first | one k.succ
    }   
}
    S4 in valid iff {
	// The workstations form a single line between begin and end
  	begin not in Workstation.^succ
  	(Workstation-begin) in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  	all w:Workstation | w not in w.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  	no end.succ
}
    S5 in valid iff {
	// The workstations form a single line between begin and end
	all ws: Workstation - end |
  		one ws.succ
  
    end.succ = none
  
  	succ.begin = none
  
  
  }
    S6 in valid iff {
	// The workstations form a single line between begin and end
  	//all w1 : Workstation | all w2 : Workstation | all w3 : Workstation |
  	//w1.succ = w2 and w2.succ = w3 implies w3.succ != (w1 or w2)
    //all w : Workstation |  w not in  w.^succ
  
  	
  
    no end.succ 
  
    no begin.~succ 
  
  	end in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))

  	all w : Workstation | w in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  
  	
}
    S7 in valid iff {
	// The workstations form a single line between begin and end
    succ in Workstation -> lone Workstation
    one w : Workstation | no w.succ
    all w : Workstation | not w in w.^succ
}
    S8 in valid iff {
	// The workstations form a single line between begin and end
    succ in Workstation -> lone Workstation
    one w : Workstation | no w.succ
//    all w : Workstation | not w in w.^succ
}
    S9 in valid iff {
	// The workstations form a single line between begin and end
    all ws : Workstation | ws in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
}
    S10 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | one begin.^succ & w
}
    S11 in valid iff {
	// The workstations form a single line between begin and end
  
  	Workstation in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  	no end.succ

}
    S12 in valid iff {
	// The workstations form a single line between begin and end
  no end.succ
  Workstation in begin.^succ
}
    S13 in valid iff {
	// The workstations form a single line between begin and end
	end in begin.^succ

}
    S14 in valid iff {
	// The workstations form a single line between begin and end
	end in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))

}
    S15 in valid iff {
	// The workstations form a single line between begin and end
	end in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) and end != begin

}
    S16 in valid iff {
	// The workstations form a single line between begin and end
	succ in (Workstation one -> one Workstation) and end in begin.^succ

}
    S17 in valid iff {
	// The workstations form a single line between begin and end
	(succ in (Workstation lone -> lone Workstation)) and (end in begin.^succ)

}
    S18 in valid iff {
	// The workstations form a single line between begin and end
	all disj w1, w2: Workstation | w1 in w2.^succ or w2 in w1.^succ

}
    S19 in valid iff {
	// The workstations form a single line between begin and end
	all w1, w2: Workstation | w1 in w2.^succ or w2 in w1.^succ

}
    S20 in valid iff {
	// The workstations form a single line between begin and end
	all disj w1, w2: Workstation | w1 not in w1.^succ and (w1 in w2.^succ or w2 in w1.^succ)

}
    S21 in valid iff {
	// The workstations form a single line between begin and end
	all ws : Workstation | ws not in ws.^succ
  	all ws1, ws2 : Workstation | ws1 != ws2 implies ws1 in ws2.^succ or ws2 in ws1.^succ
}
    S22 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | w not in w.^succ
}
    S23 in valid iff {
	// The workstations form a single line between begin and end
	all ws:Workstation | ws not in ws.^succ
	end in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
	all ws:Workstation | begin in ((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)).ws
  	
}
    S24 in valid iff {
	// The workstations form a single line between begin and end
  	all w: (Workstation+begin+end) | w in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  	all w: (Workstation+begin+end) | w not in end.^succ
  	all w: (Workstation+begin+end) | w not in w.^succ
}
    S25 in valid iff {
	// The workstations form a single line between begin and end
  	Workstation in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
    all wo : Workstation | (wo.succ != none => wo not in wo.^succ and #wo.succ = 1)
  	//all wo : Workstation | wo.succ = none => wo = end
}
    S26 in valid iff {
	// The workstations form a single line between begin and end
  	succ in (Workstation lone -> lone Workstation)
	and (all w: Workstation | w  in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))) // initial element
	//and ( no end.^succ ) // final element

}
    S27 in valid iff {
	// The workstations form a single line between begin and end
	// ** partly done in sig Workstation.succ
  some ws : Workstation | ws.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) = Workstation
  no ws : Workstation | ws->ws in succ
}
    S28 in valid iff {
	// The workstations form a single line between begin and end
	// ** partly done in sig Workstation.succ
  begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) = Workstation
  no ws : Workstation | ws->ws in succ
}
    S29 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: Workstation | one b: begin, e: end | (e in ws.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) or e=ws) and (ws in b.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) or b=ws) and ws not in ws.succ
}
    S30 in valid iff {
	// The workstations form a single line between begin and end
	// ** partly done in sig Workstation.succ
	begin != end
  begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) = Workstation
  no ws : Workstation | ws->ws in succ
}
    S31 in valid iff {
	// The workstations form a single line between begin and end
	// ** partly done in sig Workstation.succ
	begin = end iff one Workstation
  begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) = Workstation
  no ws : Workstation | ws->ws in succ
}
    S32 in valid iff {
	// The workstations form a single line between begin and end
  all w: Workstation | (w not in end) implies one w.succ
}
    S33 in valid iff {
	// The workstations form a single line between begin and end
  all w: Workstation | w not in end implies one w.succ
  no end.succ
  all w: Workstation | w not in w.^succ
}
    S34 in valid iff {
	// The workstations form a single line between begin and end
  Workstation - begin = begin.^succ
}
    S35 in valid iff {
	// The workstations form a single line between begin and end
  all w: Workstation - end | one w.succ
  no end.succ

}
    S36 in valid iff {
	// The workstations form a single line between begin and end
  one begin.succ
  all w: Workstation | w not in end implies one w.succ
  no end.succ
  all w: Workstation | w not in w.^succ
}
    S37 in valid iff {
	// The workstations form a single line between begin and end
  all w: Workstation | one w.succ
}
    S38 in valid iff {
	// The workstations form a single line between begin and end
  all w: Workstation |  #w.succ = 1 and (w != begin implies w in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)))

}
    S39 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation | w in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  
      // Todas as workstations exceto a última tem exatamente uma a seguir
      all w : Workstation - end | one w.succ
  
      // A última workstation não tem nenhuma a seguir
      //no end.succ
  
}
    S40 in valid iff {
	// The workstations form a single line between begin and end
  (end in begin.^(succ) or begin = end) and all ws : Workstation | ws.succ != ws 
}
    S41 in valid iff {
	// The workstations form a single line between begin and end
	
}
    S42 in valid iff {
	// The workstations form a single line between begin and end
  	all disj a, b: Workstation | a.succ = b implies a not in b.^succ

}
    S43 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: Workstation | ws.succ != ws
  	all disj a, b: Workstation | a.succ = b implies a not in b.^succ

}
    S44 in valid iff {
	// The workstations form a single line between begin and end
//  	all ws: Workstation | ws.succ != ws
  	all ws: Workstation | ws not in end implies one ws.succ
  	all ws: Workstation | ws in begin implies ws.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) = Workstation
  	all disj a, b: Workstation | a.succ = b implies a not in b.^succ

}
    S45 in valid iff {
	// The workstations form a single line between begin and end
  	all w: Workstation | lone w.succ

}
    S46 in valid iff {
	// The workstations form a single line between begin and end
  	all w: Workstation | no (begin & end) implies lone w.succ

}
    S47 in valid iff {
	// The workstations form a single line between begin and end
  	all w: Workstation | no (begin & end) implies one w.succ

}
    S48 in valid iff {
	// The workstations form a single line between begin and end
  	//all w: Workstation | no (begin & end) implies lone w.succ
  all w: Workstation | lone w.succ implies no (begin & end)

}
    S49 in valid iff {
	// The workstations form a single line between begin and end
  	//all w: Workstation | no (begin & end) implies lone w.succ
  all w: Workstation | lone w.succ implies one (begin & end)

}
    S50 in valid iff {
	// The workstations form a single line between begin and end
  	//all w: Workstation | no (begin & end) implies lone w.succ
  all w: Workstation | lone w.succ iff no (begin & end)

}
    S51 in valid iff {
	// The workstations form a single line between begin and end
  	//all w: Workstation | no (begin & end) implies lone w.succ
  all w: Workstation | one w.succ implies no (begin & end)
  all w: Workstation| no w.succ implies one w

}
    S52 in valid iff {
	// The workstations form a single line between begin and end
  	//all w: Workstation | no (begin & end) implies lone w.succ
  all w: Workstation | one w.succ implies one (begin & end)
  all w: Workstation| no w.succ implies one w

}
    S53 in valid iff {
	// The workstations form a single line between begin and end
  	//all w: Workstation | no (begin & end) implies lone w.succ
  all w: Workstation | one w.succ implies one begin
  all w: Workstation| one (begin & end) implies no w.succ

}
    S54 in valid iff {
	// The workstations form a single line between begin and end
  	//all w: Workstation | no (begin & end) implies lone w.succ
  all w: Workstation | one w.succ implies some (begin & end)
  all w: Workstation| one (begin & end) implies no w.succ

}
    S55 in valid iff {
	// The workstations form a single line between begin and end
  	//all w: Workstation | no (begin & end) implies lone w.succ
  all w: Workstation | some (begin & end) implies some w.succ
  all w: Workstation| one (begin & end) implies no w.succ

}
    S56 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | w not in w.succ
}
    S57 in valid iff {
	// The workstations form a single line between begin and end
  	//all w: Workstation | no (begin & end) implies lone w.succ
  all w: Workstation | some (begin & end) implies some w.succ
  //all w: Workstation| one (begin & end) implies no w.succ
  //each workstation only has one or no succ
  //all w: Workstation | lone w.succ

}
    S58 in valid iff {
	// The workstations form a single line between begin and end
  	//all w: Workstation | no (begin & end) implies lone w.succ
  all w: Workstation | some (begin & end) implies lone w.succ and w not in w.^succ
  //all w: Workstation| one (begin & end) implies no w.succ
  //each workstation only has one or no succ
  //all w: Workstation | lone w.succ

}
    S59 in valid iff {
	// The workstations form a single line between begin and end
  not (begin.succ = end) and begin.^(succ) = end  or begin = end
}
    S60 in valid iff {
	// The workstations form a single line between begin and end
  	//all w: Workstation | no (begin & end) implies lone w.succ
  all w: Workstation | some (begin & end) implies some w.succ
  all w: Workstation | w not in w.^succ
  //all w: Workstation| one (begin & end) implies no w.succ
  //each workstation only has one or no succ
  //all w: Workstation | lone w.succ

}
    S61 in valid iff {
	// The workstations form a single line between begin and end
	
	(all ws: Workstation| ws not in ws.succ) and
	end in begin.^succ 
	
}
    S62 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | w not in w.succ
  	one e: end, b: begin | (e = b) or (e in b.^succ)
}
    S63 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | w not in w.succ
  	all e: end, b: begin | ((e = b) and (#Workstation =< 1)) or (e in b.^succ)
}
    S64 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | w not in w.succ
  	one e: end, b: begin | ((e = b) and (#Workstation > 1)) or (e in b.^succ)
}
    S65 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | w not in w.^succ
  	all e: end, b: begin | ((e = b) and (#Workstation =< 1)) or (e in b.^succ)
}
    S66 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | w not in w.^{succ}
  	all e: end, b: begin | (e in b.^succ)
}
    S67 in valid iff {
	// The workstations form a single line between begin and end
	//all w: Workstation | w not in w.^{succ}
  	all e: end, b: begin | e = b
  	one e: end, b: begin | (e in b.^succ)
}
    S68 in valid iff {
	// The workstations form a single line between begin and end
	//all w: Workstation | w not in w.^{succ}
  	all e: end, b: begin | (e = b and no e.succ) or (e in b.^succ)
}
    S69 in valid iff {
	// The workstations form a single line between begin and end
	//all w: Workstation | w not in w.^{succ}
  	all e: end, b: begin | (e = b implies no e.succ) or (e in b.^succ)
}
    S70 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | w not in w.^succ
  	begin != end
  	no end.succ
}
    S71 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | w not in w.^succ
  	no end.succ
}
    S72 in valid iff {
	// The workstations form a single line between begin and end
	//all w: Workstation | w not in w.^succ
  	all w: begin.^succ | w not in w.^succ
  
}
    S73 in valid iff {
	// The workstations form a single line between begin and end
	all w: (Workstation+begin+end) | no begin.^succ & w
}
    S74 in valid iff {
	// The workstations form a single line between begin and end
	//all w: Workstation | w not in w.^succ
  	//all w: begin.^succ | begin not in w.^succ and w not in w.^succ and end in w.^succ
  	all w: begin.^succ | w.succ not in w.succ.^succ
  	no end.succ
  
}
    S75 in valid iff {
	// The workstations form a single line between begin and end
	//all w: Workstation | w not in w.^succ
  	//all w: begin.^succ | begin not in w.^succ and w not in w.^succ and end in w.^succ
  	all w: begin.^succ | w.succ not in w.succ.^succ
  	no end.succ
  	all w: Workstation | lone w.succ
  
}
    S76 in valid iff {
	// The workstations form a single line between begin and end
	//all w: Workstation | w not in w.^succ
  	//all w: begin.^succ | begin not in w.^succ and w not in w.^succ and end in w.^succ
  	all w: begin.^succ | w.succ not in w.succ.^succ
  	no end.succ
  	all w: Workstation - end | one w.succ
  
}
    S77 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | w not in w.^succ
  	
  	all w: Workstation - end | one s: Workstation | s in w.succ
  	
  	all e: end | all w: Workstation | w not in e.succ
  	
  	all b: begin | all w: Workstation | b not in w.succ
}
    S78 in valid iff {
	// The workstations form a single line between begin and end
  	all w : Workstation - end | one w.succ and w not in w.^succ
  	all w : Workstation - begin | one succ.w  and w not in ^succ.w
  	

  
}
    S79 in valid iff {
	// The workstations form a single line between begin and end
	all ws: Workstation | ws not in ws.^succ and (ws.succ != none iff ws != end)
  	all disj w1, w2: Workstation | w1.succ & w2.succ = none
}
    S80 in valid iff {
	// The workstations form a single line between begin and end
  all ws:Workstation | one b:begin | one e :end | ws in b.succ and e in ws.succ 
	
}
    S81 in valid iff {
	// The workstations form a single line between begin and end
  all w : Workstation | one begin.succ & w and one w.^succ & end
	
}
    S82 in valid iff {
	// The workstations form a single line between begin and end
  all w : Workstation | one begin.succ & w and one w.^succ & end and (w not in w.^succ or w in end)
	
}
    S83 in valid iff {
	// The workstations form a single line between begin and end
	one w1 : Workstation, w3 : Workstation | all w2 :  Workstation - w1 - w3 |  w2 & w3 in w1.^succ && w2 & w1 in w3.^succ && #(w2.succ) = 1
  	 
}
    S84 in valid iff {
	// The workstations form a single line between begin and end
  	all w: Workstation | all wStart: (Workstation & begin) | 
 		wStart not in w.^succ
  	all wStart: (Workstation & begin) - end | one wEnd: (Workstation & end) |
  		wEnd in wStart.^succ
  	all w: Workstation | no w.succ implies w in begin
  	all w: Workstation | w not in w.^succ
}
    S85 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: Workstation | (ws in begin.^succ or ws = begin) and (end in ws.^succ or ws = end) and ws not in ws.^succ
}
    S86 in valid iff {
	// The workstations form a single line between begin and end
	end in begin.^succ
  	all w : Workstation | one w.succ
}
    S87 in valid iff {
	// The workstations form a single line between begin and end
	end in begin.^succ
  	all w : Workstation-end | one w.succ
}
    S88 in valid iff {
	// The workstations form a single line between begin and end
	begin != end implies begin in begin.^succ
  	all w : Workstation-end | one w.succ	
}
    S89 in valid iff {
	// The workstations form a single line between begin and end
	begin != end implies begin in begin.^succ
  	begin = end implies no begin.succ
  	all w : Workstation-end | one w.succ	
}
    S90 in valid iff {
	// The workstations form a single line between begin and end
	begin = end implies one Workstation and no begin.succ
}
    S91 in valid iff {
	// The workstations form a single line between begin and end
	begin = end implies one Workstation and no begin.succ
  	begin != end implies (all w : Workstation-end | one w.succ) and (end in begin.^succ)
}
    S92 in valid iff {
	// The workstations form a single line between begin and end
	begin = end implies one Workstation and no begin.succ
  	begin != end implies (all w : Workstation-end | one w.succ) and (end in begin.^succ) and (no end.succ)
}
    S93 in valid iff {
	// The workstations form a single line between begin and end
	begin = end implies one Workstation and no begin.succ
  	begin != end implies (all w : Workstation-end | one w.succ) and (end in begin.^succ) and (all w : Workstation | w not in w.succ)
}
    S94 in valid iff {
	// The workstations form a single line between begin and end
	begin = end implies one Workstation and no begin.succ
  	begin != end implies (all w : Workstation-end | one w.succ) and (end in begin.^succ) and (all w : Workstation | w not in w.succ) and (no end.succ)
}
    S95 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation | w not in w.^succ and lone w.succ
}
    S96 in valid iff {
	// The workstations form a single line between begin and end
	begin = end implies one Workstation and no begin.succ
  	begin != end implies (all w : Workstation-end | one w.succ and begin not in w.^succ) and (end in begin.^succ) and (all w : Workstation | w not in w.succ) and (no end.succ)
}
    S97 in valid iff {
	// The workstations form a single line between begin and end
  	all w:Workstation | lone(w.succ) and not(w in w.^succ) and lone(succ.w)

}
    S98 in valid iff {
	// The workstations form a single line between begin and end
  	all w:Workstation | lone(w.succ) and lone(succ.w)

}
    S99 in valid iff {
	// The workstations form a single line between begin and end
  	all w:Workstation | lone(w.succ) and lone(succ.w) and not(w in w.succ) and not(w in succ.w)

}
    S100 in valid iff {
	// The workstations form a single line between begin and end
  	all w:Workstation | lone(w.succ + workstation.w) and lone(succ.w + workstation.w) and not(w in w.succ) and not(w in succ.w)

}
    S101 in valid iff {
	// The workstations form a single line between begin and end
	begin = end implies one Workstation and no begin.succ
	begin != end implies all w : Workstation | one w.succ and begin.^succ = Workstation
}
    S102 in valid iff {
	// The workstations form a single line between begin and end
	begin = end implies one Workstation and no begin.succ
	begin != end implies (all w : Workstation-end | one w.succ) and (begin.^succ = Workstation)
}
    S103 in valid iff {
	// The workstations form a single line between begin and end
	begin = end implies one Workstation and no begin.succ
	begin != end implies all w : Workstation-end | one w.succ 
	begin != end implies begin.^succ = Workstation - begin
}
    S104 in valid iff {
	// The workstations form a single line between begin and end
  	all w:Workstation | lone(w.succ + workstation.w) and lone(succ.w + workstation.w) and not(w in w.succ) and not(w in succ.w) and w in begin implies not w in end

}
    S105 in valid iff {
	// The workstations form a single line between begin and end
  	all w:Workstation | lone(w.succ + workstation.w) and lone(succ.w + workstation.w) and not(w in w.succ) and not(w in succ.w) and (w in begin implies not w in end)

}
    S106 in valid iff {
	// The workstations form a single line between begin and end
	begin = end implies one Workstation and no begin.succ
	begin != end implies all w : Workstation-end | one w.succ 
  	begin != end implies no end.succ
  
}
    S107 in valid iff {
	// The workstations form a single line between begin and end
  	all w : Workstation | one(begin) and one(end) and ((w in begin) implies one(w.succ)) and (not(w in begin + end) implies (one(w.succ) and one(succ.w))) and  ((w in end) implies one(succ.w)) 
}
    S108 in valid iff {
	// The workstations form a single line between begin and end
  no begin & end
	&& all w: (Workstation - end) | one w.succ
  && all w: (Workstation - begin) | one succ.w
}
    S109 in valid iff {
	// The workstations form a single line between begin and end
  	all w : Workstation | one(begin) and one(end) and ((w in begin) implies one(w.succ)) and (not(w in begin + end) implies (one(w.succ) and one(succ.w))) and  ((w in end) implies one(succ.w)) and no(begin & end) and (not(w in w.succ) and not(w in succ.w))
}
    S110 in valid iff {
	// The workstations form a single line between begin and end
  	all w : Workstation | one(begin) and one(end) and ((w in begin) implies one(w.succ)) and (not(w in begin + end) implies (one(w.succ) and one(succ.w))) and  ((w in end) implies one(succ.w)) and (not(w in w.succ) and not(w in succ.w))
}
    S111 in valid iff {
	// The workstations form a single line between begin and end
  	all w : Workstation | one(begin) and one(end) and ((w in begin) implies lone(w.succ)) and (not(w in begin + end) implies (one(w.succ) and one(succ.w))) and  ((w in end) implies lone(succ.w)) and (not(w in w.succ) and not(w in succ.w))
}
    S112 in valid iff {
	// The workstations form a single line between begin and end
  	all w : Workstation | (one(begin) and one(end) and ((w in begin) implies one(w.succ)) and (not(w in begin + end) implies (one(w.succ) and one(succ.w))) and  ((w in end) implies one(succ.w)) and (not(w in w.succ) and not(w in succ.w))) or one(Workstation)
}
    S113 in valid iff {
	// The workstations form a single line between begin and end
  	all w : Workstation | (one(begin) and one(end) and ((w in begin) implies one(w.succ)) and (not(w in begin + end) implies (one(w.succ) and one(succ.w))) and  ((w in end) implies one(succ.w)) and (not(w in w.succ) and not(w in succ.w))) or (one(Workstation) and no(w.succ) and no(succ.w)) and (w not in w.^succ)
}
    S114 in valid iff {
	// The workstations form a single line between begin and end
  	//all w1 : Workstation | all w2 : Workstation | all w3 : Workstation |
  	//w1.succ = w2 and w2.succ = w3 implies w3.succ != (w1 or w2)
    //all w : Workstation |  w not in  w.^succ
  
  	
  
    no end.succ 
  
    no begin.~succ 
  
  	Workstation->end in Workstation->begin.^succ 
  
  	all w : Workstation | w in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
}
    S115 in valid iff {
	// The workstations form a single line between begin and end
  (one disj c1, c2:Workstation | (c1 in begin) and (c2 in end) and (c1.^succ = Workstation - c1) and no(c2.succ)) or (one c1:Workstation | (c1 in begin) and (c1 in end))
}
    S116 in valid iff {
	// The workstations form a single line between begin and end
  (one disj c1, c2:Workstation | (c1 in begin) and (c2 in end) and (c1.^succ = Workstation - c1) and no(c2.succ)) or (one c1:Workstation | (c1 in begin) and (c1 in end) and no(c1.succ))
}
    S117 in valid iff {
	// The workstations form a single line between begin and end
	
  	no succ.begin
  
	no end.succ
  
  	all w : Workstation | w not in w.^succ
  	
  	all w : Workstation-begin-end | one w.succ and one succ.w
  
  	end in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  

}
    S118 in valid iff {
	// The workstations form a single line between begin and end
  	begin != end
  	no end.succ
	all w : Workstation | w in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
    all w : Workstation -end | one w.succ
}
    S119 in valid iff {
	// The workstations form a single line between begin and end
  
	all w:Workstation | w in begin implies (one w.succ and no succ.w)
	all w:Workstation | w in end implies (no w.succ and one succ.w)
	all w:Workstation | w not in (begin + end) implies (one w.succ and one succ.w and w not in w.succ and w not in succ.w)

  
  
  
  //	all w : Workstation | ((w in begin) implies (one(w.succ) and no(succ.w)) and
  // ((not(w in begin + end) implies (one(w.succ) and one(succ.w))) and
 //((w in end) implies ((one(succ.w) and no(w.succ)) and
  // not(w in succ.w))) or (one(Workstation) and no(w.succ) and no(succ.w)) and (w not in w.^succ) and (w not in succ.w)
}
    S120 in valid iff {
	// The workstations form a single line between begin and end
  
	all w:Workstation | w in begin implies (lone w.succ and no succ.w)
	all w:Workstation | w in end implies (no w.succ and lone succ.w)
	all w:Workstation | w not in (begin + end) implies (one w.succ and one succ.w and w not in w.succ and w not in succ.w)

  
  
  
  //	all w : Workstation | ((w in begin) implies (one(w.succ) and no(succ.w)) and
  // ((not(w in begin + end) implies (one(w.succ) and one(succ.w))) and
 //((w in end) implies ((one(succ.w) and no(w.succ)) and
  // not(w in succ.w))) or (one(Workstation) and no(w.succ) and no(succ.w)) and (w not in w.^succ) and (w not in succ.w)
}
    S121 in valid iff {
	// The workstations form a single line between begin and end
  	all b,e : Workstation | e in b.^succ

}
    S122 in valid iff {
	// The workstations form a single line between begin and end
  	all b,e : Workstation | e in b.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))

}
    S123 in valid iff {
	// The workstations form a single line between begin and end
  	all b,m,e : Workstation | m in b.^succ and b not in e.^succ implies e in m.^succ

}
    S124 in valid iff {
	// The workstations form a single line between begin and end
  	all b,m,e : Workstation | m in b.^succ and b not in e.^succ implies e in m.^succ and b not in m.^succ

}
    S125 in valid iff {
	// The workstations form a single line between begin and end
  	all b,m,e : Workstation | m in b.^succ and b not in e.^succ implies e in m.^succ and b not in m.^succ
  	all w : Workstation | w not in w.succ

}
    S126 in valid iff {
	// The workstations form a single line between begin and end
  	all b,m,e : Workstation | m in b.^succ and e in m.^succ implies e in b.^succ
  	all w : Workstation | w not in w.succ
    all b : begin, e : end | b not in e.succ

}
    S127 in valid iff {
	// The workstations form a single line between begin and end
  	all b,m,e : Workstation | m in b.^succ and e in m.^succ implies e in b.^succ
  	all w : Workstation | w not in w.succ
    all w : Workstation | w in begin implies w not in end
    all b : begin, e : end | b not in e.succ

}
    S128 in valid iff {
	// The workstations form a single line between begin and end
  	all b,m,e : Workstation | m in b.^succ and e in m.^succ implies e in b.^succ
  	all w : Workstation | w not in w.succ
    all w : Workstation | w in begin implies w not in end
    all b : begin, e : end | b not in e.succ
  	all e : end | no e.succ

}
    S129 in valid iff {
	// The workstations form a single line between begin and end
  	all w : Workstation | w not in w.succ
    all w : Workstation | w in begin implies w not in end
    all b : begin, e : end | b not in e.succ
  	all e : end | no e.succ
    all w : Workstation | w not in end implies one w.succ

}
    S130 in valid iff {
	// The workstations form a single line between begin and end
	no succ & ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)
  	all w : Workstation-end | one w.succ
  	no end.succ
}
    S131 in valid iff {
	// The workstations form a single line between begin and end
  
  	//desnecessário 
  	all ws : Workstation | ws not in ws.succ
  	all ws:Workstation -end | one ws.succ
  	all b : begin, ws : Workstation | b not in ws.succ
  	all e : end | no e.succ

}
    S132 in valid iff {
	// The workstations form a single line between begin and end
	all ws:Workstation | (ws not in end implies #ws.succ=1) and ws not in ws.succ
  	one ws1,ws2:Workstation | ws1 in begin and ws2 in end
}
    S133 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: Workstation | 
  		ws not in ws.succ and
  		(ws not in end implies #ws.succ = 1) and
  		begin not in ws.succ
}
    S134 in valid iff {
	// The workstations form a single line between begin and end
  	begin not in Workstation.^succ
  	end not in ^succ.Workstation
  	all s: Workstation | s not in s.^succ
  	all s: Workstation - begin - end |
  one s.^succ and one ^succ.s
  	all s: Workstation | s in begin and s in end implies no s.succ and no succ.s
  	all disj s1, s2: Workstation | s1 in begin and s2 in end implies one s1.succ and one succ.s2 
  	
}
    S135 in valid iff {
	// The workstations form a single line between begin and end
	
    all W : Workstation| one(W.succ) and W.succ != W


}
    S136 in valid iff {
	// The workstations form a single line between begin and end
	all W : Workstation | some (W.succ) implies one (W.succ) and no (W.succ & W)
}
    S137 in valid iff {
	// The workstations form a single line between begin and end
	all W : Workstation | some (W.succ) implies one (W.succ) and no (W.succ & W &begin)
  	and (one begin.succ) and (no end.succ)
}
    S138 in valid iff {
	// The workstations form a single line between begin and end
	
    all W : Workstation - (begin & end)| one (W.succ) and no (W.succ & W &begin)
  	and (no end.succ)


}
    S139 in valid iff {
	// The workstations form a single line between begin and end
	
    all W : Workstation - (begin & end)| one (W.succ) and no (W.succ & W)
  	and (no end.succ)


}
    S140 in valid iff {
	// The workstations form a single line between begin and end
	
all W : Workstation - (begin & end)| one (W.succ) and no (W.succ & W) and no (W.succ & begin) and (no end.succ)


}
    S141 in valid iff {
	// The workstations form a single line between begin and end
	
all W : Workstation - (begin & end)| no(W.succ & W) and no(W.succ & begin) and (no end.succ)


}
    S142 in valid iff {
	// The workstations form a single line between begin and end
	
    all W : Workstation - end| one(W.succ) and W.succ != W


}
    S143 in valid iff {
	// The workstations form a single line between begin and end
	
    all W : Workstation - end| one(W.succ) and W.succ != W
	and no(end.succ)

}
    S144 in valid iff {
	// The workstations form a single line between begin and end
	
    all W : Workstation - end| one(W.succ) and W.succ != W
	and end != begin

}
    S145 in valid iff {
	// The workstations form a single line between begin and end
	
    all W : Workstation - end| one(W.succ) and W.succ != W
	and end != begin and no(end.succ)

}
    S146 in valid iff {
	// The workstations form a single line between begin and end
	
    all W : Workstation - end| one(W.succ) and W.succ != W and no(end.succ) and
   no(begin & W.succ) 

}
    S147 in valid iff {
	// The workstations form a single line between begin and end
  	all w : Workstation - end | one w.succ and w not in w.succ
  	all w : Workstation - begin | one succ.w  and w not in succ.w
  	
  	no succ.begin
  	no end.succ
  
}
    S148 in valid iff {
	// The workstations form a single line between begin and end
  	all w: Workstation | w in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) and w in ^succ.end
}
    S149 in valid iff {
	// The workstations form a single line between begin and end
 // all w : Workstation | (w in begin and w in end and none = w.succ) or ((w in begin.^succ or w in begin) and w not in w.^succ and (end in w.^succ or w in end) and (one begin.^succ & w or w in begin))
	// all w : start | (one w.^succ & end and w not in w.^succ)
  all w : Workstation | ((one w.succ => end in w.^succ) or w = end) and (w = begin or w in begin.^succ)
	
}
    S150 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: Workstation | ws in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) and end in ws.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
}
    S151 in valid iff {
	// The workstations form a single line between begin and end
  (one w:Workstation | w in end) and (one w:Workstation | w in begin) and (all w:Workstation | some succ.w)

}
    S152 in valid iff {
	// The workstations form a single line between begin and end
	(begin = end or one (begin.^succ :> end)) and begin not in begin.^succ
}
    S153 in valid iff {
	// The workstations form a single line between begin and end
	(begin = end or no(Workstation - begin.^succ :> end)) and begin not in begin.^succ
}
    S154 in valid iff {
	// The workstations form a single line between begin and end
	all wstation: Workstation | wstation in end implies no wstation.succ
  	all wstation: Workstation | wstation in begin or wstation in end
}
    S155 in valid iff {
	// The workstations form a single line between begin and end
    no end.succ and all ws : Workstation | ws in (begin <: begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) :> end + begin + end) and ws not in ws.^succ
}
    S156 in valid iff {
	// The workstations form a single line between begin and end
    all ws : Workstation | ws in (begin <: begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) :> end + begin + end) and ws not in ws.^succ
}
    S157 in valid iff {
	// The workstations form a single line between begin and end
  	no ~succ[begin]
	no succ[end]
	one succ[Workstation - end]
	one ~succ[Workstation - begin]
	Workstation = begin.^succ + begin
  	

}
    S158 in valid iff {
	// The workstations form a single line between begin and end
    Workstation = begin or (all ws : Workstation | ws in (begin <: begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) :> end + begin + end) and ws not in ws.^succ)
}
    S159 in valid iff {
	// The workstations form a single line between begin and end
  all w,w1 : Workstation | w in end or w in begin or w in w1.succ
}
    S160 in valid iff {
	// The workstations form a single line between begin and end
  all w : Workstation | (w in end or w in begin) and (w not in w.succ)
}
    S161 in valid iff {
	// The workstations form a single line between begin and end
  all w : Workstation | w in end or w in begin 
}
    S162 in valid iff {
	// The workstations form a single line between begin and end
  	Workstation =  (begin <: begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) :> end + begin + end) and Workstation.^succ != Workstation
}
    S163 in valid iff {
	// The workstations form a single line between begin and end
  	Workstation =  (begin <: begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) :> end + begin + end) and Workstation.^succ != Workstation and no end.succ
}
    S164 in valid iff {
	// The workstations form a single line between begin and end
	Workstation.succ = Workstation - begin
  	succ.Workstation = Workstation - end
}
    S165 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation - end | one w.succ
  	all w : Workstation - begin | one succ.w
}
    S166 in valid iff {
	// The workstations form a single line between begin and end
  no begin & end and
  one begin and one end and
    (all w: Workstation - begin - end | one w.succ) and
    (all w: Workstation - begin - end | one w.~succ) and
    no w: Workstation | w in w.^succ and
    begin.^succ = Workstation - begin - end and
    end.~^succ = Workstation - begin - end
}
    S167 in valid iff {
	// The workstations form a single line between begin and end
  	//(one w:Workstation | w in begin) and (one w:Workstation | w in end) and (all w:Workstation | some succ.w )
  	all b:begin | all w : Workstation | w in b.(succ)

}
    S168 in valid iff {
	// The workstations form a single line between begin and end
  	//(one w:Workstation | w in begin) and (one w:Workstation | w in end) and (all w:Workstation | some succ.w )
  	//all b:begin | all w : Workstation | w in b.*(succ)
  	//all w:Workstation | w not in end implies one w.succ
  	all w:Workstation | (w not in begin and w not in end) implies w in succ.w  

}
    S169 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | ((w in end) or (w in begin) or 
(w in Workstation.succ)) and w not in w.succ
}
    S170 in valid iff {
	// The workstations form a single line between begin and end
  all w : Workstation |some w1: Workstation |(w in end or w in begin or w in w1.succ) and (w not in w.succ) and end in begin.succ
}
    S171 in valid iff {
	// The workstations form a single line between begin and end
  all w,w1 : Workstation | (w in end or w in begin) and (w not in w.succ) and (end in begin.succ) 
}
    S172 in valid iff {
	// The workstations form a single line between begin and end
  all w,w1 : Workstation | ((w in end) and (w not in w.succ) and (end in begin.succ)) or ((w in begin) and (w not in w.succ)) or (w in w1.succ) or ((w in begin) and (w in end))
}
    S173 in valid iff {
	// The workstations form a single line between begin and end
  all w,w1 : Workstation | ((w in end) and (w not in w.succ) and (end in begin.succ)) or ((w in begin) and (w not in w.succ)) or (w in w1.succ) or ((w in begin) and (w in end) and (w not in w.succ))
}
    S174 in valid iff {
	// The workstations form a single line between begin and end
  	(all b:begin | no b.succ and b in end) or (all w:Workstation | w not in end implies one w.succ)

}
    S175 in valid iff {
	// The workstations form a single line between begin and end
  	(all b:begin | b in end implies no b.succ ) or (all w:Workstation | w not in end implies one w.succ)

}
    S176 in valid iff {
	// The workstations form a single line between begin and end
  	(all b:begin | b in end implies no b.succ ) and (all w:Workstation | w not in end implies one w.succ)

}
    S177 in valid iff {
	// The workstations form a single line between begin and end
  	(all b:begin | b in end implies no b.succ )
	(all w:Workstation | w not in end implies one w.succ)
	(all w:Workstation,b:begin | w in b.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)))
	

}
    S178 in valid iff {
	// The workstations form a single line between begin and end
	Workstation in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  	((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden) not in succ
  	all wo : Workstation | wo.succ not = none => begin not = end
}
    S179 in valid iff {
	// The workstations form a single line between begin and end
  	(all b:begin | b in end implies no b.succ )
	(all w:Workstation | w not in end iff one w.succ)
	(all w:Workstation,b:begin | w in b.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)))
	

}
    S180 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | (w in end) or (w in begin) or 
(w in Workstation.succ) 
}
    S181 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: Workstation | ws not in (ws.^succ) and end in (ws.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))) 
}
    S182 in valid iff {
	// The workstations form a single line between begin and end
	begin not in Workstation.succ
  	all w: Workstation | w not in w.^succ
  	
}
    S183 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: Workstation | ws not in (ws.^succ)
  	all ws: (Workstation-begin-end) | some(ws.succ)
  	no(succ.begin) and no(end.succ)   
  	(begin != end) implies some(succ.end) and some(begin.succ)
}
    S184 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation | w not in w.^succ
  	all w : Workstation | begin in w + w.~succ
  	all w : Workstation | end in w + w.^succ
}
    S185 in valid iff {
	// The workstations form a single line between begin and end
  	all w: Workstation | all wStart: (Workstation & begin) | wStart not in w.^succ
  	all wStart: (Workstation & begin & end)-end | one wEnd: (Workstation & end) |
  		wEnd in wStart.succ
}
    S186 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation, e: end | e in w.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
}
    S187 in valid iff {
	// The workstations form a single line between begin and end
	all x: Workstation | x != end implies end in x.^succ
  	no succ.begin 
}
    S188 in valid iff {
	// The workstations form a single line between begin and end
	all x: Workstation | x != begin and x != end implies 
  							x in begin.^succ and end in x.^succ
 	
}
    S189 in valid iff {
	// The workstations form a single line between begin and end
	all x: Workstation | x != begin and x != end implies 
  							x in begin.^succ and end in x.^succ
   begin != end
 	
}
    S190 in valid iff {
	// The workstations form a single line between begin and end
  	all w : Workstation | w not in w.^succ
  	begin = end iff one Workstation
	begin != end implies all w : Workstation - {begin + end} | w in begin.^succ and end in w.^succ
}
    S191 in valid iff {
	// The workstations form a single line between begin and end
  	begin not in Workstation.^succ
  	end not in ^succ.Workstation
  	all s: Workstation | s not in s.^succ
  	all w: Workstation - begin - end |
  some w.^succ and some ^succ.w
}
    S192 in valid iff {
	// The workstations form a single line between begin and end
  	succ = none->none
}
    S193 in valid iff {
	// The workstations form a single line between begin and end
    (all w : Workstation - begin - end | w in begin.^succ and w in ^succ.end and some w.succ) and
  	(all b : begin - end   | no succ.b and some b.succ) and
  	(all e : end   - begin | no e.succ and some succ.e) and
	(all r : begin & end   | no succ.r and no r.succ)

}
    S194 in valid iff {
	// The workstations form a single line between begin and end
	
  	no (end.succ)
    no ( succ.begin )
  	
  	//all w : Workstation - begin| begin in (*(succ).w)
  
  	//all w : Workstation - end| end in w.*(succ)
  
  	all w : Workstation| w not in w.^(succ)
  
  	all w: Workstation| lone(w.succ)
}
    S195 in valid iff {
	// The workstations form a single line between begin and end
    all s: Workstation | lone s.succ
    all s: Workstation | s in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
    //end.succ = none
}
    S196 in valid iff {
	// The workstations form a single line between begin and end
	begin not in Workstation.succ
  	end in Workstation.succ
  	
}
    S197 in valid iff {
	// The workstations form a single line between begin and end
	begin not in Workstation.succ
  	end in Workstation.succ
  	all w: Workstation | w not in w.^succ
  	
}
    S198 in valid iff {
	// The workstations form a single line between begin and end
	begin not in Workstation.succ
  	all w: Workstation | w not in (w.^succ - end)
  	
}
    S199 in valid iff {
	// The workstations form a single line between begin and end
	begin not in Workstation.succ
  	some w: Workstation | w.succ = end
  	
}
    S200 in valid iff {
	// The workstations form a single line between begin and end
  	no succ.begin
  	no end.succ
  

}
    S201 in valid iff {
	// The workstations form a single line between begin and end
    all w : Workstation | w in begin or w in end or (w in begin.^succ and w in ^succ.end and w not in w.^succ and one w.succ)

}
    S202 in valid iff {
	// The workstations form a single line between begin and end
    all w : Workstation | (w = begin or w = end or (w in begin.^succ and w in ^succ.end)) and w not in w.^succ and lone w.succ

}
    S203 in valid iff {
	// The workstations form a single line between begin and end
    (all w : Workstation - begin - end | w in begin.^succ and w in ^succ.end and some w.succ) and
  	(all b : begin | no succ.b and lone b.succ) and
  	(all e : end   | no e.succ)

}
    S204 in valid iff {
	// The workstations form a single line between begin and end
  	all w:Workstation | some sub:Workstation| sub in w.succ

}
    S205 in valid iff {
	// The workstations form a single line between begin and end
	(all ws: Workstation|
  	ws not in ws.succ and
  	one ws & begin iff one end & ws.^succ)
}
    S206 in valid iff {
	// The workstations form a single line between begin and end
	(all ws: Workstation|
  	(ws in begin and no ws.succ implies ws in end) or (ws in begin and one ws.succ and ws not in ws.succ and end in (ws.^succ - ws)))
}
    S207 in valid iff {
	// The workstations form a single line between begin and end
	(all ws: Workstation|
  	(ws in begin and no ws.succ implies ws in end) and (ws in begin and one ws.succ implies end in (ws.^succ - ws)))
}
    S208 in valid iff {
	// The workstations form a single line between begin and end
	(all ws: Workstation|
  	(ws in begin and no ws.succ implies ws in end) and (ws in begin and one ws.succ and ws not in ws.succ implies end in (ws.^succ - ws)))
}
    S209 in valid iff {
	// The workstations form a single line between begin and end
	all ws:Workstation | ws not in ws.^succ
	end in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
	begin in ((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)).Workstation
  	
}
    S210 in valid iff {
	// The workstations form a single line between begin and end
  one Workstation or one begin.succ and one succ.end and (all w: Workstation - begin - end | one w.succ and one succ.w)
}
    S211 in valid iff {
	// The workstations form a single line between begin and end
  one Workstation => no succ else one begin.succ and one succ.end and (all w: Workstation - begin - end | one w.succ and one succ.w)
}
    S212 in valid iff {
	// The workstations form a single line between begin and end
  	#Workstation = 1 => begin = end and succ = none->none
}
    S213 in valid iff {
	// The workstations form a single line between begin and end
  	one Workstation
  		=> no succ
  	else (one begin.succ and one succ.end)
}
    S214 in valid iff {
	// The workstations form a single line between begin and end
  	no begin.~succ
  	no end.succ
  	all s: Workstation - end | one s.succ
  	all s: Workstation - begin | one s.~succ

}
    S215 in valid iff {
	// The workstations form a single line between begin and end
  	one Workstation
  		=> no succ
  	else (
      	(all w: Workstation | lone w.succ and w not in w.succ)
//    	and (all w: Workstation - end | one w.succ)
//  		and (all w: Workstation - begin | one succ.w)
		and (no end.succ) and (no succ.begin)
    )
}
    S216 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation |some w2: Workstation | w2 not in w
}
    S217 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation |some w2: Workstation | w2 not in w.succ
}
    S218 in valid iff {
	// The workstations form a single line between begin and end
  
  one w : Workstation | begin in w
  one w : Workstation | end in w and no w.succ
  all w : Workstation-begin-end | one succ.w and one w.succ

}
    S219 in valid iff {
	// The workstations form a single line between begin and end
  
  one w : Workstation | begin in w
  one w : Workstation | end in w and no w.succ
  all w : Workstation | no (begin & end)
  all w : Workstation-begin-end | one succ.w and one w.succ

}
    S220 in valid iff {
	// The workstations form a single line between begin and end
  
  one w : Workstation | begin in w
  one w : Workstation | end in w and no w.succ
  all w : Workstation | (one begin&w) iff no end&w
  all w : Workstation-begin-end | one succ.w and one w.succ

}
    S221 in valid iff {
	// The workstations form a single line between begin and end
	all ws: Workstation | one su:ws.succ | ws in begin implies su in end
}
    S222 in valid iff {
	// The workstations form a single line between begin and end
	all ws: Workstation | some su:ws.succ | ws = begin implies su = end
}
    S223 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | one begin.^succ
}
    S224 in valid iff {
	// The workstations form a single line between begin and end
	all w: (Workstation+begin+end) | one begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) & w
  	end in begin.^succ
}
    S225 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: Workstation | one b: begin, e: end | e in ws.^succ and ws in b.^succ
}
    S226 in valid iff {
	// The workstations form a single line between begin and end
  	all disj w1, w2: Workstation | w1 != w2 and w1 in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) and w2 in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) implies w1 in w2.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) or w2 in w1.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
}
    S227 in valid iff {
	// The workstations form a single line between begin and end
	begin.succ = end 
}
    S228 in valid iff {
	// The workstations form a single line between begin and end
  all w: Workstation - end | lone w.succ
  no end.succ

}
    S229 in valid iff {
	// The workstations form a single line between begin and end
  all w: Workstation | w = begin or lone w.succ
  no end.succ

}
    S230 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: (Workstation-begin-end) | ws not in (ws.^succ) and some(succ.ws) and end in (ws.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)))
  	no(succ.begin) and no(end.succ) and (begin != end) implies some(succ.end)  
}
    S231 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: (Workstation-begin-end) | ws not in (ws.^succ) and some(succ.ws)
  	no(succ.begin) and no(end.succ) and (begin != end) implies some(succ.end)  
}
    S232 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: (Workstation-begin-end) | ws not in (ws.^succ)
  	no(succ.begin) and no(end.succ) and (begin != end) implies some(succ.end)  
}
    S233 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: Workstation | ws not in (ws.^succ)
  	no(succ.begin) and no(end.succ) and (begin != end) implies some(succ.end)  
}
    S234 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: Workstation | ws not in (ws.^succ)
  	no(succ.begin) and no(end.succ)   
}
    S235 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: Workstation | ws not in (ws.^succ)
  	no(succ.begin) and no(end.succ)   
  	(begin != end) implies some(succ.end)
}
    S236 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: Workstation | ws not in (ws.^succ)
  	all ws: (Workstation-begin-end) | some(ws.succ)
  	no(succ.begin) and no(end.succ)   
  	(begin != end) implies some(succ.end)
}
    S237 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: Workstation | ws not in (ws.^succ)
  	all ws: (Workstation-begin-end) | one(ws.succ)
  	no(succ.begin) and no(end.succ)   
  	(begin != end) implies one(succ.end) and one(begin.succ)
}
    S238 in valid iff {
	// The workstations form a single line between begin and end
  all w : Workstation | w in end implies no(w.succ)
  all w : Workstation | w in begin implies some(w.succ)
  all w : Workstation | (w not in end) and ( w not in begin) implies one(w.succ) 

}
    S239 in valid iff {
	// The workstations form a single line between begin and end
  no end.succ
  one begin.succ
  all w:Workstation | not (w in begin or w in end) implies one w.succ

}
    S240 in valid iff {
	// The workstations form a single line between begin and end
  all w : Workstation | w in end implies no(w.succ)
  all w1 : Workstation , wb: begin | w1 in wb.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  all w2 : Workstation | (w2 not in end) and (w2 not in begin) implies one(w2.succ) 

}
    S241 in valid iff {
	// The workstations form a single line between begin and end
  	all w:Workstation - begin | w in begin.^succ && one begin.succ
  	no end.succ
}
    S242 in valid iff {
	// The workstations form a single line between begin and end
	all c:Component | all parts: c.parts | c.workstation in parts.workstation.succ
}
    S243 in valid iff {
	// The workstations form a single line between begin and end
	all ws:Workstation|ws in begin+end or ws in begin.^succ
}
    S244 in valid iff {
	// The workstations form a single line between begin and end
	all ws:Workstation| ws in begin or ws in begin.^succ & end
}
    S245 in valid iff {
	// The workstations form a single line between begin and end
	all ws:Workstation|ws in begin+end or ws in begin.^succ and ws not in end.^succ
}
    S246 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation | not begin in w.^succ
	all w : Workstation | begin != end implies end in w.^succ
}
    S247 in valid iff {
	// The workstations form a single line between begin and end
  	begin = end implies one Workstation
	all w : Workstation | not begin in w.^succ
	all w : Workstation | begin != end implies end in w.^succ
}
    S248 in valid iff {
	// The workstations form a single line between begin and end
  	begin = end implies one Workstation
	all w : Workstation | not begin in w.^succ
	all w : Workstation | end in w.^succ
}
    S249 in valid iff {
	// The workstations form a single line between begin and end
	all ws:Workstation| ws in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) and ws not in end.^succ or ws in begin&end
}
    S250 in valid iff {
	// The workstations form a single line between begin and end
	all ws:Workstation| (ws in begin.^succ and ws not in end.^succ) or (ws in begin&end and ws not in ws.succ)
}
    S251 in valid iff {
	// The workstations form a single line between begin and end
	all ws:Workstation| (ws in begin.^succ and ws not in end.^succ) or (ws in begin&end)
}
    S252 in valid iff {
	// The workstations form a single line between begin and end
  
    begin = end or {begin != end iff all w : Workstation | w != begin and w != end implies w in begin.^succ and end in w.^succ}
}
    S253 in valid iff {
	// The workstations form a single line between begin and end
  
    begin != end iff all w : Workstation | w != begin and w != end implies w in begin.^succ and end in w.^succ
}
    S254 in valid iff {
	// The workstations form a single line between begin and end
  	begin = end iff one Workstation
	begin != end implies all w : Workstation - {begin + end} | w in begin.^succ and end in w.^succ
}
    S255 in valid iff {
	// The workstations form a single line between begin and end
    all w: Workstation - end.succ | w in w.succ
    all w: Workstation - begin.succ | w not in w.succ
    some w: Workstation | w in begin.succ and w in end.succ
}
    S256 in valid iff {
	// The workstations form a single line between begin and end
    all w: Workstation | w in w.succ and (w not in end.succ implies w not in begin.succ)
}
    S257 in valid iff {
  // Workstations form a single line from begin to end
  all ws : Workstation | (ws = begin and ws.succ = end)
  or
  (ws = end and ws.succ = begin)
}
    S258 in valid iff {
	// The workstations form a single line between begin and end
	one wt : Workstation | all wts : Workstation | wt not in wts.^succ

}
    S259 in valid iff {
	// The workstations form a single line between begin and end
	all wt : Workstation | one wts : Workstation | wt not in wts.^succ and wt!=wts

}
    S260 in valid iff {
	// The workstations form a single line between begin and end
	 all w : Workstation | one ww : Workstation| ww in w.^succ - w

}
    S261 in valid iff {
	// The workstations form a single line between begin and end
  all ws:Workstation | one b:begin | one e :end | ws in b.succ or e in ws.succ 
}
    S262 in valid iff {
	// The workstations form a single line between begin and end
	all wk : Workstation | one wk.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
}
    S263 in valid iff {
	// The workstations form a single line between begin and end
	all wk : Workstation | one wk.^succ
}
    S264 in valid iff {
	// The workstations form a single line between begin and end
	all wk : Workstation | one b : begin | wk=b or wk in b.^succ
  	all wk : Workstation | one e : end | wk=e or e in wk.^succ
  	all wk : Workstation | wk not in wk.succ and lone wk.succ

}
    S265 in valid iff {
	// The workstations form a single line between begin and end
	all disj w1, w2 : Workstation | w1 in begin.succ.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) and w2 in end.succ.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) implies w1 in w2.succ.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) or w2 in w1.succ.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
}
    S266 in valid iff {
	// The workstations form a single line between begin and end
  	begin = end implies one Workstation 
	begin not in Workstation.succ  
  	no end.succ
  	all w : Workstation-end | one w.succ and w not in w.succ
}
    S267 in valid iff {
	// The workstations form a single line between begin and end
  	begin = end implies one Workstation 
	
  	begin not in Workstation.succ  
  	end in Workstation.succ	
  	
  	no end.succ
 		
  	all w : Workstation-end | one w.succ and w not in w.succ
}
    S268 in valid iff {
	// The workstations form a single line between begin and end
  	begin = end implies one Workstation
  	begin not in Workstation.succ  
  	begin != end implies end in Workstation.succ	
  	no end.succ
  	all w : Workstation-end-begin | one w.succ and w not in w.succ and (one s : Workstation | s.succ = w)
}
    S269 in valid iff {
	// The workstations form a single line between begin and end
  	begin = end implies one Workstation
  	begin != end implies {
      	all w : Workstation-end-begin | one w.succ 
  		all w : Workstation-end-begin | w not in w.succ 
    	all w : Workstation-end-begin | one s : Workstation | s.succ = w
    }
  
  	
}
    S270 in valid iff {
	// The workstations form a single line between begin and end
  	begin = end implies {
      	one Workstation
      	no end.succ
  	}
      
  	begin != end implies {
      	one begin.succ
      	no end.succ
      	
      	all w : Workstation-end-begin | one w.succ  
      	Workstation.succ = Workstation - begin
    }
  
  	
}
    S271 in valid iff {
	// The workstations form a single line between begin and end
  	begin = end implies {
      	one Workstation
      	no end.succ
  	}
      
  	begin != end implies {
      	one begin.succ
      	no end.succ
      	
      	all w : Workstation-end-begin | one w.succ and w not in w.succ
      	Workstation.succ = Workstation - begin
    }
  
  	
}
    S272 in valid iff {
	// The workstations form a single line between begin and end
  	begin = end implies {
      	one Workstation
      	no end.succ
  	}
      
  	begin != end implies {
      	one begin.succ
      	no end.succ
      	
      	all w : Workstation | w not in w.^succ  
    }
  
  	
}
    S273 in valid iff {
	// The workstations form a single line between begin and end
  	
    no end.succ	
  	
  	begin = end implies one Workstation
      
  	begin != end implies {
      	all w : Workstation-end | one w.succ
      	all w : Workstation | w not in w.^succ
    }
  
  	
}
    S274 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | lone w.succ
	no end.succ
  
  	begin not in Workstation.succ
}
    S275 in valid iff {
	// The workstations form a single line between begin and end
    begin.^succ = end

}
    S276 in valid iff {
	// The workstations form a single line between begin and end
    begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) = end

}
    S277 in valid iff {
	// The workstations form a single line between begin and end
    begin.^succ = end or begin = end

}
    S278 in valid iff {
	// The workstations form a single line between begin and end
    begin.^succ = end or (begin = end and no succ)

}
    S279 in valid iff {
	// The workstations form a single line between begin and end
    begin.^succ = end or (one Workstation and begin = end and no succ)

}
    S280 in valid iff {
	// The workstations form a single line between begin and end
    #Workstation > 1 => begin != end and begin.^succ = end 
  	else (one Workstation => begin = end and no succ)

}
    S281 in valid iff {
	// The workstations form a single line between begin and end
    #Workstation > 1 => begin != end and begin.^succ = end and no end.succ
  	else (one Workstation => begin = end and no succ)

}
    S282 in valid iff {
	// The workstations form a single line between begin and end
  	/* succ in Workstation one -> lone Workstation 
    #Workstation > 1 => begin != end and begin.^succ = end and no end.succ
  	else (one Workstation => begin = end and no succ)
	*/
  	^succ in begin -> end
  
}
    S283 in valid iff {
	// The workstations form a single line between begin and end
  	/* succ in Workstation one -> lone Workstation 
    #Workstation > 1 => begin != end and begin.^succ = end and no end.succ
  	else (one Workstation => begin = end and no succ)
	*/
  	#Workstation > 1 => ^succ in begin one -> one end
  	else (one Workstation => begin = end and no succ)
	
}
    S284 in valid iff {
	// The workstations form a single line between begin and end
	all wstation: Workstation | wstation in end implies no wstation.succ
  	all wstation: Workstation | wstation in begin or wstation in end
  	all wstation: Workstation | wstation in begin and wstation not in end 
  		implies end in wstation.^succ
  	all wstation: Workstation | no (wstation.succ & wstation)
}
    S285 in valid iff {
	// The workstations form a single line between begin and end
	no begin & end
    all w : Workstation | one w.succ
}
    S286 in valid iff {
	// The workstations form a single line between begin and end
	no begin & end
    all w : Workstation | lone w.succ
}
    S287 in valid iff {
	// The workstations form a single line between begin and end
    lone begin.succ and no end.succ
    all w : Workstation | lone w.succ and w not in w.^succ
    //Workstation.succ = Workstation - begin
}
    S288 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: Workstation | one b: begin, e: end | e in ws.^succ and ws in b.^succ or ws = b and ws = e
}
    S289 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: Workstation | ws in begin.^succ and end in ws.succ
}
    S290 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: Workstation | ws in begin.^succ and end in ws.^succ and one ws2 : Workstation | ws.succ = ws2
}
    S291 in valid iff {
	// The workstations form a single line between begin and end
  	// 
	all w : Workstation | w in begin + begin.^succ and end in w + w.^succ and one w.succ
}
    S292 in valid iff {
	// The workstations form a single line between begin and end
	//no succ.begin
  	//no end.succ
  	end in begin.^succ or end in begin
  	all ws:Workstation - begin - end | ws in begin.^succ
  	all w: Workstation | w not in w.^succ
  	all w: Workstation - end | lone w.succ
  	
  	
}
    S293 in valid iff {
	// The workstations form a single line between begin and end
	all ws : Workstation | begin in ws.^succ and end in ws.^succ
}
    S294 in valid iff {
	// The workstations form a single line between begin and end
	(begin.succ = end) and all ws: Workstation - end |
        one ws.succ and ws.succ in Workstation - begin
}
    S295 in valid iff {
	// The workstations form a single line between begin and end
	let line = begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) & Workstation
    {
        all ws: Workstation | ws in line and (ws != ws.succ) 
        one last: line | last.succ = end and last not in last.^succ
    }
}
    S296 in valid iff {
	// The workstations form a single line between begin and end
	all ws: Workstation | ws in begin => one ws.succ or ws in end
}
    S297 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation | begin in w implies w not in w.succ and end in w.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
}
    S298 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation | end in w implies begin in succ.w
}
    S299 in valid iff {
	// The workstations form a single line between begin and end
	some w : Workstation | begin in w implies end in w.succ
}
    S300 in valid iff {
	// The workstations form a single line between begin and end
	some w : Workstation | begin in w iff end in w.succ
}
    S301 in valid iff {
	// The workstations form a single line between begin and end
	end in Workstation.succ
}
    S302 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation | w not in w.succ and one w.succ and (begin in w implies end in w.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)))
}
    S303 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation | w not in w.^succ and lone w.succ and (begin in w implies end in w.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)))
}
    S304 in valid iff {
	// The workstations form a single line between begin and end
	some w : Workstation | w not in w.^succ and lone w.succ and (begin in w and end in w.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)))
}
    S305 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation | w not in w.^succ and lone w.succ
  	some w : Workstation | w.succ = Workstation-w and begin in w and end in w.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
}
    S306 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation | w not in w.^succ and lone w.succ
  	some w : Workstation | w.^succ = Workstation-w and begin in w and end in w.^succ
  	some w : Workstation | end in w implies no w.succ
}
    S307 in valid iff {
	// The workstations form a single line between begin and end
	some wo: Workstation | begin in wo and end in wo.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  	some wo: Workstation | end in wo and no wo.succ
}
    S308 in valid iff {
	// The workstations form a single line between begin and end
	some wo: Workstation | begin in wo and end in wo.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) and no succ.wo
  	some wo: Workstation | end in wo and no wo.succ
}
    S309 in valid iff {
	// The workstations form a single line between begin and end
  	all w : Workstation | succ.w + w.succ + w = Workstation
	some wo: Workstation | begin in succ.wo and end in wo.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) 
  	some wo: Workstation | end in wo and no wo.succ
}
    S310 in valid iff {
	// The workstations form a single line between begin and end
  	all w : Workstation | succ.w + w.succ + w = Workstation
	some wo: Workstation | begin in ((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)).wo and end in wo.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
}
    S311 in valid iff {
	// The workstations form a single line between begin and end
  	all w : Workstation | succ.w + w.succ + w = Workstation
	some wo: Workstation | begin in ((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)).wo and end in wo.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) 
  	some wo: Workstation | end in wo and no wo.succ
}
    S312 in valid iff {
	// The workstations form a single line between begin and end
  //	all w : Workstation | succ.w + w.succ + w = Workstation
	some w: Workstation  | begin not in ((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)).w
    some wo: Workstation | begin in ((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)).wo and end in wo.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) 
  	some wo: Workstation | end in wo and no wo.succ
}
    S313 in valid iff {
	// The workstations form a single line between begin and end
  //	all w : Workstation | succ.w + w.succ + w = Workstation
	some w: Workstation  | begin not in succ.w
    some wo: Workstation | begin in wo and end in wo.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) 
  	some wo: Workstation | end in wo and no wo.succ
}
    S314 in valid iff {
	// The workstations form a single line between begin and end
  	all w : Workstation | succ.w + w.succ + w = Workstation
	some w: Workstation  | begin not in succ.w
    some wo: Workstation | begin in wo and end in wo.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) 
  	some wo: Workstation | end in wo and no wo.succ
}
    S315 in valid iff {
	// The workstations form a single line between begin and end
  	all w : Workstation | succ.w + w.succ + w = Workstation
	all w: Workstation  | begin not in succ.w
    some wo: Workstation | begin in wo and end in wo.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) 
  	some wo: Workstation | end in wo and no wo.succ
}
    S316 in valid iff {
	// The workstations form a single line between begin and end
  	//all w : Workstation | succ.w + w.succ + w = Workstation
	all w: Workstation  | begin not in succ.w
    some wo: Workstation | begin in wo and end in wo.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) 
  	some wo: Workstation | end in wo and no wo.succ
}
    S317 in valid iff {
	// The workstations form a single line between begin and end
  all w : Workstation | lone w.succ and lone succ.w and w+w.^succ+^succ.w = Workstation
  some w : Workstation | (no succ.w and begin in w) or (no w.succ and end in w)  
}
    S318 in valid iff {
	// The workstations form a single line between begin and end
  all w : Workstation | lone w.succ and lone succ.w and w+w.^succ+^succ.w = Workstation
  all w : Workstation | (no succ.w and begin in w) or (no w.succ and end in w) or (begin not in w and end not in w)  
}
    S319 in valid iff {
	// The workstations form a single line between begin and end
  all w : Workstation | lone w.succ and lone succ.w and w+w.^succ+^succ.w = Workstation
  some w : Workstation | (no succ.w and begin in w) or (no w.succ and end in w) or (begin not in w and end not in w)  
}
    S320 in valid iff {
	// The workstations form a single line between begin and end
  all w : Workstation | lone w.succ and lone succ.w and w+w.^succ+^succ.w = Workstation
  all w : Workstation | begin in w implies no succ.w and end in w implies no w.succ
}
    S321 in valid iff {
	// The workstations form a single line between begin and end
  all w : Workstation | lone w.succ and lone succ.w and w+w.^succ+^succ.w = Workstation
  all w : Workstation | begin in w implies no succ.w or end in w implies no w.succ
}
    S322 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation | lone w.succ and lone succ.w// and w+w.^succ+^succ.w = Workstation
	all w : Workstation | begin in w implies no succ.w 
	all w : Workstation | end in w implies no w.succ 
}
    S323 in valid iff {
	// The workstations form a single line between begin and end
  	no s: Workstation | s -> s in workstation
  	all s: Workstation - begin - end {
      	one s.~workstation.parts.workstation
  	}

}
    S324 in valid iff {
	// The workstations form a single line between begin and end
  	//all w1 : Workstation | all w2 : Workstation | all w3 : Workstation |
  	//w1.succ = w2 and w2.succ = w3 implies w3.succ != (w1 or w2)
    //all w : Workstation |  w not in  w.^succ
  
  	
  
    no end.succ
  
    no begin.~succ 
  
  	end in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  
  	
  	//all ws : Workstation - end | one ws.succ
	all ws : Workstation - begin | one ws.~succ

	all ws : Workstation | ws in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))  // reachable from begin
  
}
    S325 in valid iff {
    // The workstations form a single line between begin and end
    all w: Workstation - begin - end | one w.~succ and one w.succ
}
    S326 in valid iff {
	// The workstations form a single line between begin and end
  all w: Workstation | w in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) + end.~succ
}
    S327 in valid iff {
    // The workstations form a single line between begin and end
    all w: Workstation - begin - end | lone w.~succ and lone w.succ
}
    S328 in valid iff {
    // The workstations form a single line between begin and end
    all w: Workstation - end |
        lone w.~succ and (w in begin.~succ or one w.succ)
}
    S329 in valid iff {
    // The workstations form a single line between begin and end
    all w: Workstation - end |
        (w in begin.~succ or one w.succ)
}
    S330 in valid iff {
    // The workstations form a single line between begin and end
    all w: Workstation - begin - end | one w.succ and one w.~succ
    no begin.~succ and no end.succ
}
    S331 in valid iff {
    // The workstations form a single line between begin and end
    all w: Workstation - begin - end | one w.succ and one w.~succ
    no begin.succ and no end.~succ
}
    S332 in valid iff {
	// The workstations form a single line between begin and end
      let line = Workstation - begin - end | all w: line | one w.succ and w not in w.succ

  

}
    S333 in valid iff {
	// The workstations form a single line between begin and end
	all ws: Workstation - end | ws in begin.^succ
}
    S334 in valid iff {
	// The workstations form a single line between begin and end
  no ws: Workstation | ws not in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) || ws not in end.^succ
}
    S335 in valid iff {
	// The workstations form a single line between begin and end
	let line = Workstation - begin - end {
        all ws: line | one ws.succ and ws.succ in line
    }
}
    S336 in valid iff {
	// The workstations form a single line between begin and end
	all ws: Workstation - end | some ws.succ
    all ws: Workstation - begin | lone ws.succ
    end not in begin.succ
}
    S337 in valid iff {
	// The workstations form a single line between begin and end
	succ in Workstation one -> one Workstation
}
    S338 in valid iff {
	// The workstations form a single line between begin and end
	end in begin.^succ
  	all w : Workstation - end | some s : Workstation | s in w.succ
}
    S339 in valid iff {
	// The workstations form a single line between begin and end
	end in begin.^succ
  	no w : Workstation | w in end.succ
  	all w : Workstation - end | some s : Workstation | s in w.succ
}
    S340 in valid iff {
	// The workstations form a single line between begin and end
	end in begin.^succ
  	no w : Workstation | w in end.succ
  	all w : Workstation - end | one s : Workstation | s in w.succ
}
    S341 in valid iff {
	// The workstations form a single line between begin and end
	end in begin.^succ
  	no w : Workstation | w in end.succ
  	no w : Workstation | begin in w.succ
  	all w : Workstation - end | one s : Workstation | s in w.succ
}
    S342 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation - end | end in w.^succ
  	all w : Workstation - begin | one s : Workstation | s in w.succ
}
    S343 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation - end | end in w.^succ
  	all w : Workstation - end | one s : Workstation | s in w.succ
}
    S344 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation - end | one w.succ
	all w: Workstation - begin | one w.~succ
  	all w: Workstation | w in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
}
    S345 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation - end | end in w.^succ
  	all w : Workstation - end | one s : Workstation | s in w.succ
  	all w : Workstation - begin | one s : Workstation | w in s.succ
  	begin = end => no s : Workstation | s in begin.succ
}
    S346 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation - end | one s : Workstation | s in w.succ
  	all w : Workstation - begin | one s : Workstation | w in s.succ
  	begin = end => no s : Workstation | s in begin.succ
}
    S347 in valid iff {
	// The workstations form a single line between begin and end
	end in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  	no end.succ
  	all w: Workstation | w.succ != w
}
    S348 in valid iff {
	// The workstations form a single line between begin and end
  	succ in Workstation lone -> lone Workstation
	end in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  	no end.succ
  	all w: Workstation | w.succ != w
}
    S349 in valid iff {
	// The workstations form a single line between begin and end
  	succ in Workstation lone -> lone Workstation
	end in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  	no succ.begin
  	no end.succ
  	all w: Workstation | w.succ != w
}
    S350 in valid iff {
	// The workstations form a single line between begin and end
	no end.succ
}
    S351 in valid iff {
	// The workstations form a single line between begin and end
  all disj ws1, ws2 : Workstation | ws1.succ != ws2.succ
  
}
    S352 in valid iff {
	// The workstations form a single line between begin and end
  all disj ws1, ws2 : Workstation | ws1.succ != ws2.succ
  all ws : Workstation | ws.succ != ws
  
}
    S353 in valid iff {
	// The workstations form a single line between begin and end
  
  begin != end and begin + begin.^succ = Workstation and end.succ = none
 
}
    S354 in valid iff {
	// The workstations form a single line between begin and end
  
  begin + begin.^succ = Workstation and end.succ = none
  no ws : Workstation | ws.succ = ws
}
    S355 in valid iff {
	// The workstations form a single line between begin and end
  
  begin + begin.^succ = Workstation and end.succ = none and
  no ws : Workstation | ws in ws.succ
}
    S356 in valid iff {
	// The workstations form a single line between begin and end
  
  begin + begin.^succ = Workstation
  all ws : Workstation | lone ws.succ and ws not in ws.succ
}
    S357 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: Workstation | ws = begin or ws = end
	all ws: Workstation | ws != end implies one ws.succ
  	all ws: Workstation | ws != begin implies no ws.succ
}
    S358 in valid iff {
	// The workstations form a single line between begin and end
	all ws: Workstation | ws = begin implies one ws.succ
  	all ws: Workstation | ws = end implies no ws.succ
  	all ws: Workstation | ws = begin implies ws not in ws.succ
}
    S359 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: Workstation | ws = begin implies ws not in ws.succ
}
    S360 in valid iff {
	// The workstations form a single line between begin and end
	all ws: Workstation | ws = begin implies lone ws.succ
  	all ws: Workstation | ws = end implies no ws.succ
  	all ws: Workstation | ws = begin implies ws not in ws.succ
}
    S361 in valid iff {
	// The workstations form a single line between begin and end
	all ws: Workstation | ws = begin implies lone ws.succ
  	all ws: Workstation | ws = end implies no ws.succ
  	all ws: Workstation | ws = begin implies ws not in ws.succ
  	all ws: Workstation | ws != begin or ws != end implies (some ws2: Workstation | ws in ws2.succ)
}
    S362 in valid iff {
	// The workstations form a single line between begin and end
	all ws: Workstation | ws = begin implies lone ws.succ
  	all ws: Workstation | ws = end implies no ws.succ
  	all ws: Workstation | ws = begin implies ws not in ws.succ
  	all ws: Workstation | ws = begin and ws = end implies one Workstation
}
    S363 in valid iff {
	// The workstations form a single line between begin and end
	all ws: Workstation | ws = begin implies lone ws.succ
  	all ws: Workstation | ws = end implies no ws.succ
  	all ws: Workstation | ws = begin implies ws not in ws.succ
  	all ws: Workstation | some ws2: Workstation | ws in ws2.succ
}
    S364 in valid iff {
	// The workstations form a single line between begin and end
	all ws: Workstation | ws = begin implies lone ws.succ
  	all ws: Workstation | ws = end implies no ws.succ
  	all ws: Workstation | ws = begin implies ws not in ws.succ
  	all ws: Workstation | ws != begin and ws != end implies ( some ws2: Workstation | ws in ws2.succ)
}
    S365 in valid iff {
	// The workstations form a single line between begin and end
	all ws: Workstation | ws = begin implies lone ws.succ
  	all ws: Workstation | ws = end implies no ws.succ
  	all ws: Workstation | ws not in ws.succ
  	all ws: Workstation | ws != begin and ws != end implies ( some ws2: Workstation | ws in ws2.succ)
}
    S366 in valid iff {
	// The workstations form a single line between begin and end
  begin.^(succ) = end or begin.succ = end or begin = end
}
    S367 in valid iff {
	// The workstations form a single line between begin and end
  begin.succ.^(succ) = end  or begin = end
}
    S368 in valid iff {
	// The workstations form a single line between begin and end
  begin.succ != begin
  begin.^(succ) = end or begin = end
}
    S369 in valid iff {
	// The workstations form a single line between begin and end
  begin.succ != begin
  begin.^(succ) = end
}
    S370 in valid iff {
	// The workstations form a single line between begin and end
  begin.succ != begin
  (begin.^(succ) = end and no (Workstation - begin.^(succ))) or begin = end
}
    S371 in valid iff {
	// The workstations form a single line between begin and end
  (end in begin.^(succ) or begin = end) and begin.succ != begin and all ws : Workstation | ws in begin.^(succ)
}
    S372 in valid iff {
	// The workstations form a single line between begin and end
  begin.succ != begin
  all ws : Workstation | ws.succ != ws and ws in begin.^(succ) 
}
    S373 in valid iff {
	// The workstations form a single line between begin and end
  begin.^(succ) = end or begin = end
  all ws : Workstation | ws.succ != ws and ws in begin.^(succ) 
}
    S374 in valid iff {
	// The workstations form a single line between begin and end
  begin.^(succ) = end or begin = end or all ws : Workstation | ws.succ != ws and ws in begin.^(succ) 
}
    S375 in valid iff {
	// The workstations form a single line between begin and end
  (end in begin.^(succ) or begin = end) and begin.succ != begin
}
    S376 in valid iff {
	// The workstations form a single line between begin and end
  	#Workstation = 1 => begin = end and succ = none->none
  	Workstation in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
}
    S377 in valid iff {
	// The workstations form a single line between begin and end
  (end = begin.^(succ) or begin = end) and begin.succ != begin 
  and all ws : Workstation | ws in (begin + begin.^(succ))
}
    S378 in valid iff {
	// The workstations form a single line between begin and end
  begin = end implies one Workstation
  (end = begin.^(succ) or begin = end) and begin.succ != begin 
  and all ws : Workstation | ws in (begin + begin.^(succ))
}
    S379 in valid iff {
	// The workstations form a single line between begin and end
  begin = end implies one Workstation or begin.^(succ) = end
  all ws : Workstation | ws.succ != ws
}
    S380 in valid iff {
	// The workstations form a single line between begin and end
  begin = end implies one Workstation
  all ws : Workstation | ws.succ != ws
  begin.^(succ) = end
}
    S381 in valid iff {
	// The workstations form a single line between begin and end
  begin = end implies one Workstation or begin.^(succ) = end
  all ws : Workstation | ws.succ != ws and ws in (begin + begin.^(succ))
}
    S382 in valid iff {
	// The workstations form a single line between begin and end
  (begin.^(succ) = end and no end.succ) or (begin = end)

  all ws : Workstation | ws in (begin + begin.^(succ))
}
    S383 in valid iff {
	// The workstations form a single line between begin and end

  (all ws : Workstation | ws = begin or ws in begin.^(succ)) and begin.^(succ) = end
}
    S384 in valid iff {
	// The workstations form a single line between begin and end

  (all ws : Workstation | ws = begin or ws in begin.^(succ)) and (begin.^(succ) = end or begin = end)
}
    S385 in valid iff {
	all w:Workstation | w in begin implies (some w2:Workstation | w->w2 in succ)   //o begin tem um succ
	all w1,w2,w3:Workstation | (w1 in begin and w1->w2 in succ and w1->w3 in succ) implies (w2=w3) //o begin tem apenas um succ

	all w:Workstation | w in end implies (some w2:Workstation | w2->w in succ)  //o end e succ de alguem
	all w1,w2,w3:Workstation | (w1 in end and w2->w1 in succ and w3->w1 in succ) implies (w2=w3) //apenas alguem tem o end como succ

	all w2:Workstation | (not w2 in begin and not w2 in end) implies (some w1,w3: Workstation | w1!=w3 and w1->w2 in succ and w2->w3 in succ)

}
    S386 in valid iff {
	all w : Workstation | not w->w in succ

	all w:Workstation | w in begin implies (some w2:Workstation | w->w2 in succ)   //o begin tem um succ
	all w1,w2,w3:Workstation | (w1 in begin and w1->w2 in succ and w1->w3 in succ) implies (w2=w3) //o begin tem apenas um succ

	all w:Workstation | w in end implies (some w2:Workstation | w2->w in succ)  //o end e succ de alguem
	all w1,w2,w3:Workstation | (w1 in end and w2->w1 in succ and w3->w1 in succ) implies (w2=w3) //apenas alguem tem o end como succ

	all w2:Workstation | (not w2 in begin and not w2 in end) implies (some w1,w3: Workstation | w1!=w3 and w1->w2 in succ and w2->w3 in succ)

}
    S387 in valid iff {
	all w : Workstation | not w->w in succ  // nada é succ de ele próprio

	all w:Workstation | w in begin implies (some w2:Workstation | w->w2 in succ)   //o begin tem um succ
	all w1,w2,w3:Workstation | (w1 in begin and w1->w2 in succ and w1->w3 in succ) implies (w2=w3) //o begin tem apenas um succ
	all w1,w2:Workstation | (w1 in begin and w2!=w1) implies (not w2->w1 in succ) //ninguem tem o begin como succ

	all w:Workstation | w in end implies (some w2:Workstation | w2->w in succ)  //o end e succ de alguem
	all w1,w2,w3:Workstation | (w1 in end and w2->w1 in succ and w3->w1 in succ) implies (w2=w3) //apenas alguem tem o end como succ
	all w1,w2:Workstation| (w2 in end and w1!=w2) implies (not w2->w1 in succ) //o end nao tem ninguem como succ


	all w2:Workstation | (not w2 in begin and not w2 in end) implies (some w1,w3: Workstation | w1!=w3 and w1->w2 in succ and w2->w3 in succ)

}
    S388 in valid iff {
	some w1,w2 : Workstation | w1 in begin and w2 in end  //existe um begin e um end
	all w1,w2 : Workstation | (w1 in begin and w2 in begin) implies (w1=w2) //so existe um begin
	all w1,w2 : Workstation | (w1 in end and w2 in end) implies (w1=w2) //so existe um end

	all w : Workstation | not w->w in succ  // nada é succ de ele próprio
	all w1,w2:Workstation | (w1 in begin and w2!=w1) implies (not w2->w1 in succ) //ninguem tem o begin como succ
	all w1,w2:Workstation| (w2 in end and w1!=w2) implies (not w2->w1 in succ) //o end nao tem ninguem como succ

	//se algo não é begin ou end, entao é succ de alguem e tem alguem como succ
	all w2:Workstation | (not w2 in begin and not w2 in end) implies (some w1,w3: Workstation | w1!=w3 and w1->w2 in succ and w2->w3 in succ)
	all w1,w2,w3:Workstation | (w1->w2 in succ and w1->w3 in succ) implies (w2=w3)  // cada elem tem apenas um succ
	all w1,w2,w3:Workstation | (w2->w1 in succ and w3->w1 in succ) implies (w2=w3)  // cada elem e succ apenas de algum ele  

}
    S389 in valid iff {
	some w1,w2 : Workstation | w1 in begin and w2 in end  //existe um begin e um end
	all w1,w2 : Workstation | (w1 in begin and w2 in begin) implies (w1=w2) //so existe um begin
	all w1,w2 : Workstation | (w1 in end and w2 in end) implies (w1=w2) //so existe um end

	all w : Workstation | not w->w in succ  // nada é succ de ele próprio
	all w1,w2:Workstation | (w1 in begin and w2!=w1) implies (not w2->w1 in succ) //ninguem tem o begin como succ
	all w1,w2:Workstation| (w2 in end and w1!=w2) implies (not w2->w1 in succ) //o end nao tem ninguem como succ

	//se algo não é begin ou end, entao é succ de alguem e tem alguem como succ
	all w2:Workstation | (not w2 in begin and not w2 in end) implies (some w1,w3: Workstation | w1!=w3 and w1->w2 in succ and w2->w3 in succ)
	all w1,w2,w3:Workstation | (w1->w2 in succ and w1->w3 in succ) implies (w2=w3)  // cada elem tem apenas um succ
	all w1,w2,w3:Workstation | (w2->w1 in succ and w3->w1 in succ) implies (w2=w3)  // cada elem e succ apenas de algum elem

	all w1,w2:Workstation | (w1!=w2 and ((w1 in begin and w2 in end) or (w1 in end and w2 in begin))) implies ((w1->w2 in succ)or(w2->w1 in succ)) 

}
    S390 in valid iff {
	some w1,w2 : Workstation | w1 in begin and w2 in end  //existe um begin e um end
	all w1,w2 : Workstation | (w1 in begin and w2 in begin) implies (w1=w2) //so existe um begin
	all w1,w2 : Workstation | (w1 in end and w2 in end) implies (w1=w2) //so existe um end

	all w : Workstation | not w->w in succ  // nada é succ de ele próprio
	all w1,w2:Workstation | (w1 in begin and w2!=w1) implies (not w2->w1 in succ) //ninguem tem o begin como succ
	all w1,w2:Workstation| (w2 in end and w1!=w2) implies (not w2->w1 in succ) //o end nao tem ninguem como succ

	//se algo não é begin ou end, entao é succ de alguem e tem alguem como succ
	//all w2:Workstation | (not w2 in begin and not w2 in end) implies (some w1,w3: Workstation | w1!=w3 and w1->w2 in succ and w2->w3 in succ)

	all x:Workstation | some y,z:Workstation | (not x in begin and not x in end and y!=z and y!=x and z!=x) implies (y->x in succ and x->z in succ) 	

	all w1,w2,w3:Workstation | (w1->w2 in succ and w1->w3 in succ) implies (w2=w3)  // cada elem tem apenas um succ
	all w1,w2,w3:Workstation | (w2->w1 in succ and w3->w1 in succ) implies (w2=w3)  // cada elem e succ apenas de algum elem

	//se apenas existe begin e end, entao o end e succ do being ()
	all w1,w2:Workstation | (w1!=w2 and ((w1 in begin and w2 in end) or (w1 in end and w2 in begin))) implies ((w1->w2 in succ)or(w2->w1 in succ)) 

}
    S391 in valid iff {
	some w1,w2 : Workstation | w1 in begin and w2 in end  //existe um begin e um end
	all w1,w2 : Workstation | (w1 in begin and w2 in begin) implies (w1=w2) //so existe um begin
	all w1,w2 : Workstation | (w1 in end and w2 in end) implies (w1=w2) //so existe um end

	all w : Workstation | not w->w in succ  // nada é succ de ele próprio
	all w1,w2:Workstation | (w1 in begin and w2!=w1) implies (not w2->w1 in succ) //ninguem tem o begin como succ
	all w1,w2:Workstation| (w2 in end and w1!=w2) implies (not w2->w1 in succ) //o end nao tem ninguem como succ

	//se algo não é begin ou end, entao é succ de alguem e tem alguem como succ
	all w2:Workstation | (not w2 in begin and not w2 in end) implies (some w1,w3: Workstation |w1->w2 in succ and w2->w3 in succ)	

	all w1,w2,w3:Workstation | (w1->w2 in succ and w1->w3 in succ) implies (w2=w3)  // cada elem tem apenas um succ
	all w1,w2,w3:Workstation | (w2->w1 in succ and w3->w1 in succ) implies (w2=w3)  // cada elem e succ apenas de algum elem

	//se apenas existe begin e end, entao o end e succ do being ()
	all w1,w2:Workstation | (w1!=w2 and ((w1 in begin and w2 in end) or (w1 in end and w2 in begin))) implies ((w1->w2 in succ)or(w2->w1 in succ)) 

}
    S392 in valid iff {
	// The workstations form a single line between begin and end
	all b : begin, w : Workstation | not b in ^succ.w  //begin nao e succ de nada
	all e : end, w : Workstation | not w in ^succ.e //end nao tem succ

	all b : begin, w : Workstation | w!=b implies w in ^succ.b //todo workstation esta na linha de succ do begin
	all e : end, w : Workstation | w!=e implies e in ^succ.w //o end esta na linha de succ de qualquer workstation

	all w : Workstation | not w in ^succ.w  //nao existem ciclos de sucessores

	all x,y,z: Workstation  | (x->y in succ and x->z in succ) implies y=z //nada tem dois succs
	all x,y,z: Workstation  | (y->x in succ and z->x in succ) implies y=z //nada é succ de duas coisas

}
    S393 in valid iff {
	// The workstations form a single line between begin and end
//nada é succ de duas coisas
  	all b:begin,e:end| b!=e implies (e in ^succ.b)

}
    S394 in valid iff {
	// The workstations form a single line between begin and end
//nada é succ de duas coisas
  	all b:begin,e:end| b!=e implies (e in ^succ.b)
  
  all w : Workstation | not w in ^succ.w  //nao existem ciclos de sucessores
  

}
    S395 in valid iff {
	// The workstations form a single line between begin and end
//nada é succ de duas coisas
  	all b:begin,e:end| b!=e implies (e in ^succ.b)
  
  all w : Workstation | not w in ^succ.w  //nao existem ciclos de sucessores
  
 	all b : begin, w : Workstation | not w->b in succ  //begin nao e succ de nada
	all e : end, w : Workstation | not e->w in succ //end nao tem succ
  

}
    S396 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation - end | one w.succ & Workstation
    all w : Workstation - begin | one w.succ & w
}
    S397 in valid iff {
	// The workstations form a single line between begin and end
  all w: Workstation | (w = end) or (some w.succ)
    all w: Workstation | (w = begin) or (some w1: Workstation | w in w1.succ)
    no w: Workstation | w in w.succ

}
    S398 in valid iff {
    // All workstations are connected in a single line between begin and end
    all w : Workstation | 
        (w in begin.succ implies one w.succ) and 
        (w in end.succ implies no w.succ) 
}
    S399 in valid iff {
  // Ensure the workstations form a single line between begin and end

  // 1. The `begin` workstation has no successors
  no w: Workstation | w in begin.succ

  // 2. The `end` workstation has no predecessors
  no w: Workstation | end in w.succ

  // 3. Each workstation (except begin and end) has exactly one predecessor
  all w: Workstation - begin - end |
    one p: Workstation | p in w.succ

  // 4. Each workstation (except begin and end) has exactly one successor
  all w: Workstation - begin - end |
    one s: Workstation | w in s.succ

  // 5. Ensure there is a path from begin to end by using a total ordering
  // Using a helper predicate to check connectivity
  all w1, w2: Workstation | 
    (w1 in w2.succ) implies (w1 != begin and w1 != end and w2 != begin and w2 != end)
}
    S400 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation | (w = begin or w in begin.^succ) and (w = end or end in w.^succ) and lone w.succ
}
    S401 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation | some w.succ implies some begin <: ((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) :> end
}
    S402 in valid iff {
	// The workstations form a single line between begin and end
  	no w : Workstation | w in w.^succ
  	all w : Workstation-begin | some w.succ 
  	all w : Workstation-end | some succ.w 
  	//some begin <: ^succ :> end
}
    S403 in valid iff {
	// The workstations form a single line between begin and end
  	no w : Workstation | w in w.^succ
  	all w : Workstation-begin | some w.succ and no succ.w
  	all w : Workstation-end | some succ.w and no w.succ
  	//some begin <: ^succ :> end
}
    S404 in valid iff {
	// The workstations form a single line between begin and end
  	no w : Workstation | w in w.^succ
  	all w : Workstation-begin-end | some w.succ and some succ.w
  	all w : begin | some w2 : Workstation | w!=w2 implies (some w.succ and no succ.w)
  	all w : end | some w2 : Workstation | w!=w2 implies (some succ.w and no w.succ)
  	some begin <: ^succ :> end
}
    S405 in valid iff {
	// The workstations form a single line between begin and end
  	no w : Workstation | w in w.^succ
  	all w : Workstation-begin-end | some w.succ and some succ.w
  	all w : begin | some w2 : Workstation | w!=w2 implies some w.succ and no succ.w
  	all w : end | some w2 : Workstation | w!=w2 implies some succ.w and no w.succ
  	//some begin <: ^succ :> end
}
    S406 in valid iff {
	// The workstations form a single line between begin and end
  let ws = Workstation {
        begin in ws and end in ws and
        (all w: ws - begin - end | one w.succ) and
        (all w: ws - begin - end | one w.~succ) and
        no w: ws | w in w.^succ
    }

}
    S407 in valid iff {
	// The workstations form a single line between begin and end
  	no w : Workstation | w in w.^succ
  	all w : Workstation-begin-end | one w.succ and one succ.w
  	all w : begin | some w2 : Workstation | w!=w2 implies (one w.succ and no succ.w)
  	all w : end | some w2 : Workstation | w!=w2 implies (one succ.w and no w.succ)
  	all b : begin, e : end | one begin <: ^succ :> end
}
    S408 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: Workstation | ws in begin and ws in end implies no ws.succ
  
	all ws: begin | one w2: Workstation | w2 in ws.succ
  
  	all ws: end | no w2: Workstation | w2 in ws.succ
}
    S409 in valid iff {
	// The workstations form a single line between begin and end
	all ws: begin | lone w2: Workstation | w2 in ws.succ
  
  	all ws: end | no w2: Workstation | w2 in ws.succ
}
    S410 in valid iff {
	// The workstations form a single line between begin and end
  	all w: Workstation - begin - end | one w.succ and one w.~succ and w in begin.^succ
}
    S411 in valid iff {
	// The workstations form a single line between begin and end
  	no begin.~succ and no end.succ
  	all w: Workstation - end | one w.succ and one w.~succ
    all w: Workstation - begin | one w.~succ
}
    S412 in valid iff {
	// The workstations form a single line between begin and end
  	all w: Workstation - end | one w.succ
    all w: Workstation - begin | one w.~succ
  	Workstation = begin.^succ
}
    S413 in valid iff {
	// The workstations form a single line between begin and end
  	all w: Workstation - begin - end | one w.succ and one w.~succ
  	one begin.succ and no begin.~succ 
  	one end.~succ and no end.succ 
  	//Workstation = begin.^succ
}
    S414 in valid iff {
	// The workstations form a single line between begin and end
    no end.succ
  	no succ.begin
    begin.succ = end or all workstation: Workstation - begin - end | 
        one p: Workstation | prev.p = workstation and
        one s: Workstation | workstation.succ = s
}
    S415 in valid iff {
	// The workstations form a single line between begin and end
    no end.succ
  	no succ.begin
    begin.succ in end or all workstation: Workstation - begin - end | 
        one p: Workstation | prev.p = workstation and
        one s: Workstation | workstation.succ = s
}
    S416 in valid iff {
	// The workstations form a single line between begin and end
    no end.succ
  	no succ.begin
    begin.succ in end or all workstation: Workstation - begin - end | 
        one p: Workstation | p.succ = workstation and
        one s: Workstation | workstation.succ = s
}
    S417 in valid iff {
	// The workstations form a single line between begin and end
  begin = end or 
    all workstation: Workstation | 
        one workstation.succ and workstation !in workstation.succ
}
    S418 in valid iff {
	// The workstations form a single line between begin and end
  no end.succ
  no succ.begin
  begin = end or 
    all workstation: Workstation | 
        one workstation.succ and workstation !in workstation.succ
}
    S419 in valid iff {
	all b : begin | b.~succ = Workstation

}
    S420 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation | w not in w.succ

  	all b : begin |
  		end in b.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) and
  		no succ.b and no end.succ

}
    S421 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation | w not in w.succ
  	all w : Workstation-begin-end | some w.succ and some succ.w

  	all b : begin |
  		end in b.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) and
  		no succ.b and no end.succ

}
    S422 in valid iff {
	// The workstations form a single line between begin and end
	
  	no succ.begin
  
	no end.succ
  
  	all w : Workstation | w not in w.succ
  	
  	all w : Workstation-begin-end | some w.succ and some succ.w
  

}
    S423 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | end in w.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) or begin in w.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
}
    S424 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | end in w.^succ or begin in w.^succ
}
    S425 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | end in w.^succ
}
    S426 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation, e: end | {
      w not in w.succ
      e in w.^succ
    }
}
    S427 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation, b: begin, e: end | {
      w not in w.succ
      e in w.^succ
      b not in e.succ
    }
}
    S428 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation, b: begin, e: end | {
      w not in w.succ
      e in w.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
      b not in e.succ
    }
}
    S429 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation, b: begin, e: end | {
      w not in w.succ
      e in w.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
      b not in w.~succ
    }
}
    S430 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation, b: begin, e: end | {
      w not in w.succ
      e in w.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
      b not in b.~succ
    }
}
    S431 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation | (w = end or some w.succ)
}
    S432 in valid iff {
	// The workstations form a single line between begin and end

  	all w : Workstation | (one w.succ) or w in end
  
  	all w : Workstation | (one succ.w) or w in begin

	all w : Workstation | w not in w.succ
}
    S433 in valid iff {
	// The workstations form a single line between begin and end
  	no w : Workstation | w in w.succ
  
  	all w : Workstation | w in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  
  	all w : Workstation - end | one w.succ
  
	
}
    S434 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation | w = end or w.^succ in w.^succ.^succ
}
    S435 in valid iff {
	// The workstations form a single line between begin and end
	all wstation: Workstation | wstation in end implies no wstation.succ
  	all wstation: Workstation | wstation in begin or wstation in end
  	all wstation: Workstation | wstation in begin implies end in wstation.^succ
}
    S436 in valid iff {
	// The workstations form a single line between begin and end
	all wstation: Workstation | wstation in end implies no wstation.succ
  	all wstation: Workstation | wstation in begin or wstation in end
  	all wstation: Workstation | wstation in begin and wstation not in end implies end in wstation.^succ
}
    S437 in valid iff {
	// The workstations form a single line between begin and end
	all wstation: Workstation | wstation in end implies no wstation.succ
  	all wstation: Workstation | wstation in begin or wstation in end
  	all wstation: Workstation | wstation in begin and wstation not in end 
  		implies end in wstation.^succ
  	one wstation: Workstation | wstation not in wstation.succ
}
    S438 in valid iff {
	// The workstations form a single line between begin and end
	all wstation: Workstation | wstation in end implies no wstation.succ
  	all wstation: Workstation | wstation in begin and wstation not in end 
  		implies end in wstation.^succ
  	all wstation: Workstation | no (wstation.succ & wstation)
}
    S439 in valid iff {
	// The workstations form a single line between begin and end
	all wstation: Workstation | wstation in end implies no wstation.succ
  	all wstation: Workstation | wstation in begin and wstation not in end 
  		implies end in wstation.^succ
  	all wstation: Workstation | no (wstation.succ & wstation)
  	all wstation: Workstation | no wstation.succ implies wstation in end
}
    S440 in valid iff {
	// The workstations form a single line between begin and end
	all wstation: Workstation | wstation in end implies no wstation.succ
  	all wstation: Workstation | wstation in begin and wstation not in end 
  		implies end in wstation.^succ
  	all wstation: Workstation | no (wstation.succ & wstation)
  	all wstation: Workstation | no wstation.succ implies wstation in end
  	all wstation: Workstation | some wstation.succ and no succ.wstation
  		implies wstation in begin
}
    S441 in valid iff {
	// The workstations form a single line between begin and end
  let ws = Workstation {
        some begin and some end and
        // begin and end are unique
        no (begin & end) and
        // all workstations are reachable from begin or can reach end
        ws = begin.^succ + end.~^succ and
        // no cycles
        no w: ws | w in w.^succ
    }
}
    S442 in valid iff {
	// The workstations form a single line between begin and end
	some succ and
    no w: Workstation | w in w.^succ and
    begin.^succ = Workstation - begin and
    end.~^succ = Workstation - end and
    (all w: Workstation - begin - end | one w.succ) and
    (all w: Workstation - begin - end | one w.~succ)
}
    S443 in valid iff {
	// The workstations form a single line between begin and end
  
  
  // Apenas `begin` não possui predecessores
    no begin.~succ
    
    // Apenas `end` não possui sucessores
    no end.succ
    
    // Não há ciclos: nenhuma estação alcança a si mesma pelo grafo de sucessão
    no w: Workstation | w in w.^succ
    
    // Todas as estações estão acessíveis a partir de `begin` e levam a `end`
    Workstation = begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) + end.~succ
}
    S444 in valid iff {
	// The workstations form a single line between begin and end
  
  
      (begin.succ = end) and
        (all w: Workstation - end | some w.succ) and
        (all w: Workstation - begin | some w.^succ)
}
    S445 in valid iff {
	// The workstations form a single line between begin and end
  all w: Workstation | (w not in begin and w not in end) implies one w.succ
  all w: Workstation | w not in w.^(succ)

}
    S446 in valid iff {
	// The workstations form a single line between begin and end
  all w: Workstation | (w not in begin and w not in end) implies one w.succ
  all w: Workstation | w not in w.^(succ)
  all b: begin | no succ.b
  all e: end | no e.succ

}
    S447 in valid iff {
	// The workstations form a single line between begin and end
	all w:Workstation | no succ.begin
  	all e:end | no e.succ
  	one succ.end
  	
}
    S448 in valid iff {
	// The workstations form a single line between begin and end
	no succ.begin
  	all e:end | no e.succ
  	some Workstation-end-begin implies one succ.end
  	
}
    S449 in valid iff {
	// The workstations form a single line between begin and end
	no succ.begin
  	all e:end | no e.succ
  	some Workstation-end-begin implies one succ.end and some begin.succ
  	
}
    S450 in valid iff {
	// The workstations form a single line between begin and end
	no succ.begin
  	all e:end | no e.succ
  	some Workstation-end-begin implies one succ.end and some begin.succ
  	end in begin.^succ
  	
}
    S451 in valid iff {
	// The workstations form a single line between begin and end
	no succ.begin
  	all e:end | no e.succ
  	some Workstation-end-begin implies one succ.end and end in begin.^succ
  	
  	
}
    S452 in valid iff {
	// The workstations form a single line between begin and end
	no succ.begin
  	all e:end | no e.succ
  	some Workstation-end-begin implies end in begin.^succ
  	
  	
}
    S453 in valid iff {
	// The workstations form a single line between begin and end
  	begin not in Workstation.^succ
  	begin.^succ = Workstation - begin
  	all w : Workstation | w not in w.succ
  	end in Workstation.^succ or lone Workstation
  	no end.succ
}
    S454 in valid iff {
	// The workstations form a single line between begin and end
	no succ.begin
  	no end.succ
  	//end in begin.^succ or end in begin
  	all ws:Workstation - begin - end | ws in begin.^succ
  	all w: Workstation | w not in w.^succ
  	all w: Workstation - end | lone w.succ
  	
  	
}
    S455 in valid iff {
	// The workstations form a single line between begin and end
	no succ.begin
  	no end.succ
  	end in begin.^succ or end in begin
  	//all ws:Workstation - begin - end | ws in begin.^succ
  	all w: Workstation | w not in w.^succ
  	all w: Workstation - end | lone w.succ
  	
  	
}
    S456 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | 
  	all wStart: (Workstation & begin) |
  	some wEnd: (Workstation & end) | 
  		wStart not in w.succ and wEnd in wStart.^succ
}
    S457 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | 
  	all wStart: (Workstation & begin) |
  	some wEnd: (Workstation & end) | 
  		wStart not in w.succ and wStart not in end implies wEnd in wStart.^succ
}
    S458 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | 
  	all wStart: (Workstation & begin) |
  	some wEnd: (Workstation & end) | 
  		wStart not in w.succ and 
  		wStart not in wStart.succ and
  		wStart not in end 
  			implies wEnd in wStart.^succ
}
    S459 in valid iff {
	// The workstations form a single line between begin and end
  	all wStart: (Workstation & begin) | wStart not in wStart.^succ
}
    S460 in valid iff {
	// The workstations form a single line between begin and end
  	all wStart: (Workstation & begin) | wStart not in wStart.^succ
  	all wStart: (Workstation & begin) | one wEnd: (Workstation & end) |
  		wEnd in wStart.succ
}
    S461 in valid iff {
	// The workstations form a single line between begin and end
  	all w: Workstation | all wStart: (Workstation & begin) | wStart not in w.^succ
  	all wStart: (Workstation & begin) | one wEnd: (Workstation & end) |
  		wEnd in wStart.succ
}
    S462 in valid iff {
	// The workstations form a single line between begin and end
  	all w: Workstation | all wStart: (Workstation & begin) | wStart not in w.^succ
  	all wStart: (Workstation & begin)-end | one wEnd: (Workstation & end) |
  		wEnd in wStart.succ
}
    S463 in valid iff {
	// The workstations form a single line between begin and end
  	all w: Workstation | all wStart: (Workstation & begin) | 
 		wStart not in w.^succ
  	all wStart: (Workstation & begin) - end | one wEnd: (Workstation & end) |
  		wEnd in wStart.succ
  	all w: Workstation | no w.succ implies w in begin
  	some w: Workstation | w not in w.^succ
}
    S464 in valid iff {
	// The workstations form a single line between begin and end
  	all w: Workstation | all wStart: (Workstation & begin) | 
 		wStart not in w.^succ
  	all wStart: (Workstation & begin) - end | one wEnd: (Workstation & end) |
  		wEnd in wStart.succ
  	all w: Workstation | no w.succ implies w in begin
  	one w: Workstation | w not in w.^succ
}
    S465 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: Workstation & end | no ws.succ
  	all ws: (Workstation & begin) - end | some ws.succ
}
    S466 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: Workstation & end | no ws.succ
  	all ws: Workstation | some ws.succ iff ws in begin-end
}
    S467 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: Workstation | no ws.succ iff ws in end
  	all ws: Workstation | some ws.succ iff ws in begin-end
}
    S468 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: Workstation | no ws.succ iff ws in end
  	all ws: Workstation | some ws.succ iff ws in begin
}
    S469 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: Workstation | no ws.succ iff ws in end
  	all ws: Workstation | some ws.succ iff ws in begin-end
  	one ws: Workstation | ws not in ws.^succ
}
    S470 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: Workstation | no ws.succ iff ws in end
  	all ws: Workstation | one ws.succ iff ws in begin-end
  	all ws: Workstation | no (ws & ws.^succ)
}
    S471 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation | begin in succ.w
  	
  	no end.succ
}
    S472 in valid iff {
	// The workstations form a single line between begin and end
  all w: Workstation | workstation not in workstation.succ

}
    S473 in valid iff {
	// The workstations form a single line between begin and end
      all w : Workstation | 
        (w != end implies one w.succ) and 
        (w != begin implies one v : Workstation | w in v.succ)

    // `begin` deve ser alcançável por todas as estações de trabalho
    all w : Workstation | w in begin.succ

}
    S474 in valid iff {
	// The workstations form a single line between begin and end
      all w : Workstation | 
        (w != end implies one w.succ) and 
        (w != begin implies one v : Workstation | w in v.succ)

    // `begin` deve ser alcançável por todas as estações de trabalho
    all w : Workstation | w = begin implies w in begin.succ

}
    S475 in valid iff {
	// The workstations form a single line between begin and end
    all w : Workstation | ( w = begin implies (some w1:Workstation | w->w1 in succ)) and (w = end implies (some w2: Workstation | w2->w in succ))

}
    S476 in valid iff {
    // Verifica que as estações de trabalho formam uma linha única entre begin e end
    all w : Workstation |
        (w = begin implies (some w1 : Workstation | w -> w1 in succ)) and
        (w = end implies (some w2 : Workstation | w2 -> w in succ)) and
        (w != begin and w != end implies (some w1 : Workstation | w -> w1 in succ) and (some w2 : Workstation | w2 -> w in succ))
}
    S477 in valid iff {
	// The workstations form a single line between begin and end
    all w : Workstation | ( w = begin implies (some w1:Workstation | w->w1 in succ)) and (w = end implies (one w2: Workstation | w2->w in succ) ) 

}
    S478 in valid iff {
	// The workstations form a single line between begin and end
  	
  	all w : Workstation | w not in w.succ
  
    all w : Workstation | ( w = begin implies (some w1:Workstation | w->w1 in succ)) and (w = end implies (one w2: Workstation | w2->w in succ) ) 

}
    S479 in valid iff {
	// The workstations form a single line between begin and end
  	
  	all w : Workstation | w -> w not in succ
  
    all w : Workstation | ( w = begin implies (one w1:Workstation | w->w1 in succ)) and (w = end implies (one w2: Workstation | w2->w in succ) ) 

}
    S480 in valid iff {
	// The workstations form a single line between begin and end
  	
  	all w : Workstation | w -> w not in succ
  
    all w : Workstation | ( w = begin implies (one w1:Workstation | w->w1 in succ)) or (w = end implies (one w2: Workstation | w2->w in succ) ) 

}
    S481 in valid iff {
	// The workstations form a single line between begin and end
  	
    // 1. Nenhuma estação pode apontar para si mesma
    all w : Workstation | w -> w not in succ

    // 2. `begin` deve ter exatamente uma estação sucessora
    one w1 : Workstation | begin -> w1 in succ

    // 3. `end` deve ter exatamente uma estação predecessora
    one w2 : Workstation | w2 -> end in succ

    // 4. Todas as estações intermediárias devem ter exatamente uma predecessora e uma sucessora
    all w : Workstation - begin - end |
        (one w1 : Workstation | w -> w1 in succ) and
        (one w2 : Workstation | w2 -> w in succ)

    // 5. Todas as estações devem ser acessíveis a partir de `begin`
    all w : Workstation | w in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
}
    S482 in valid iff {
	// The workstations form a single line between begin and end
  	
    // 1. Nenhuma estação pode apontar para si mesma
    all w : Workstation | w -> w not in succ

    // 2. `begin` deve ter exatamente uma estação sucessora
    one w1 : Workstation | begin -> w1 in succ

    // 3. `end` deve ter exatamente uma estação predecessora
    one w2 : Workstation | w2 -> end in succ

    // 4. Todas as estações intermediárias devem ter exatamente uma predecessora e uma sucessora
    all w : Workstation - begin - end |
        (some w1 : Workstation | w -> w1 in succ) and
        (some w2 : Workstation | w2 -> w in succ)

    // 5. Todas as estações devem ser acessíveis a partir de `begin`
    all w : Workstation | w in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
}
    S483 in valid iff {
	// The workstations form a single line between begin and end
  Workstation = begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) + end
  
  no end.succ

}
    S484 in valid iff {
	// The workstations form a single line between begin and end
  Workstation = begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) + end
  
  no end.succ
  
  all w: Workstation | lone w.succ and lone w.~succ

}
    S485 in valid iff {
	// The workstations form a single line between begin and end
  succ in begin -> end
  
  no end.succ

}
    S486 in valid iff {
	// The workstations form a single line between begin and end
	no (end & Workstation.succ)
}
    S487 in valid iff {
	// The workstations form a single line between begin and end
  	no (begin & Workstation.succ)
  	all w : Workstation | one (w.succ & end)
}
    S488 in valid iff {
	// The workstations form a single line between begin and end
  	begin not in Workstation.^succ
  	all w : (Workstation - begin) | one (w.succ & end)
  	
}
    S489 in valid iff {
	// The workstations form a single line between begin and end
  	begin not in Workstation.^succ
  	end in Workstation.^succ or begin = end
  	
}
    S490 in valid iff {
	// The workstations form a single line between begin and end
  	begin not in Workstation.^succ
  	end in Workstation.^succ or (lone Workstation)
  	
}
    S491 in valid iff {
	// The workstations form a single line between begin and end
  	begin not in Workstation.^succ
  	(end not in end.^succ and end in Workstation.^succ) or lone Workstation
  	
}
    S492 in valid iff {
	// The workstations form a single line between begin and end
  	begin not in Workstation.^succ
  	all w : Workstation | w not in w.succ
  	end in Workstation.^succ or lone Workstation
  	
}
    S493 in valid iff {
	// The workstations form a single line between begin and end
  	begin not in Workstation.^succ
  	begin.^succ = end
  	all w : Workstation | w not in w.succ
  	end in Workstation.^succ or lone Workstation
  	
}
    S494 in valid iff {
	// The workstations form a single line between begin and end
  	begin not in Workstation.^succ
  	begin.^succ = Workstation - begin
  	all w : Workstation | w not in w.succ
  	end in Workstation.^succ or lone Workstation
  	
}
    S495 in valid iff {
	// The workstations form a single line between begin and end
  	//begin not in Workstation.^succ							// No workstation has begin as succ
  	//begin.^succ = Workstation - begin						// begin has all workstations as succ
  	all w : Workstation | w not in w.succ and lone w.succ	// No workstation has itself as succ and every workstation has only one succ
  	end in Workstation.^succ or lone Workstation			// end is succ of every workstation or there is only one workstation
  	no end.succ												// end does not have any workstations as succ
}
    S496 in valid iff {
	// The workstations form a single line between begin and end
  	//begin.^succ = Workstation - begin						// begin has all workstations as succ
  	all w : Workstation | w not in w.succ and lone w.succ	// No workstation has itself as succ and every workstation has only one succ
  	no end.succ												// end does not have any workstations as succ
}
    S497 in valid iff {
	// The workstations form a single line between begin and end
  	begin.^succ = Workstation - begin						// begin has all workstations as succ
  	all w : Workstation | w not in w.succ and lone w.succ	// No workstation has itself as succ and every workstation has only one succ
  	//no end.succ												// end does not have any workstations as succ
}
    S498 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | one w2: Workstation - end - begin | w2 in w.succ
}
    S499 in valid iff {
	// The workstations form a single line between begin and end
	all ws:Workstation, s:ws.succ | begin in s and end in s
}
    S500 in valid iff {
	// The workstations form a single line between begin and end
	all ws:Workstation | one s:ws.succ | begin in s and end in s
}
    S501 in valid iff {
	// The workstations form a single line between begin and end
	all ws: Workstation | 
        one ws.succ or ws = end // Each workstation has at most one successor, except `end`
    
    // Begin has no predecessor, and all workstations are reachable from `begin`
    no ws: Workstation | ws in begin.~succ

    // All workstations are reachable from `begin`, and the line ends at `end`
    all ws: Workstation | ws in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
}
    S502 in valid iff {
  all disj ws, ws1: Workstation | ws not in ws.^succ and ws in ws1.succ or ws1 in ws.succ
	// The workstations form a single line between begin and end

}
    S503 in valid iff {
 all ws: Workstation | lone ws1 : Workstation | ws not in ws.^succ and ws1 !=ws and ws1 in ws.succ

// The workstations form a single line between begin and end

}
    S504 in valid iff {
 all ws: Workstation | lone ws1 : Workstation | ws not in ws.^succ and ws1 !=ws and ws1 not in ws1.^succ and ws1 in ws.succ

// The workstations form a single line between begin and end

}
    S505 in valid iff {
 all disj ws,ws1: Workstation| ws not in ws.^succ and ws1 not in ws1.^succ

// The workstations form a single line between begin and end

}
    S506 in valid iff {
	// The workstations form a single line between begin and end
	all ws1, ws2: Workstation | (begin in ws1 and end in ws2) implies ws1 not in ws1.succ and ws2 not in ws2.succ
}
    S507 in valid iff {
	// The workstations form a single line between begin and end
	all ws1, ws2: Workstation | (begin in ws1 and end in ws2) implies (ws1 not in ws1.succ and ws2 not in (ws2.succ + ws1.succ))
}
    S508 in valid iff {
	// The workstations form a single line between begin and end
	all ws1, ws2: Workstation | (begin in ws1 and end in ws2) implies (ws1 not in (ws1.succ + ws2.succ) and ws2 not in ws2.succ)
}
    S509 in valid iff {
	// The workstations form a single line between begin and end
	all ws1, ws2: Workstation | (begin in ws1 and end in ws2) implies (ws1 not in (ws1.succ + ws2.succ) and ws2 not in ws2.succ and ws2 in ws1.succ)
}
    S510 in valid iff {
    // 1. Every workstation except `end` has exactly one successor.
    all w : Workstation - end | #w.succ = 1
    
    // 2. `end` has no successor.
    no end.succ
    
    // 3. The `begin` workstation is reachable from itself through succ, ensuring `begin` starts the line.
    begin in Workstation.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
    
    // 4. There is a single path from `begin` to `end`, covering all workstations.
    all w : Workstation | w in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) or w = end
}
    S511 in valid iff {
	// The workstations form a single line between begin and end
	all ws: Workstation, wss: Workstation - ws |
  		ws in begin => ws not in wss.succ
  
  	all ws: Workstation |
  		ws in end => no ws.succ
}
    S512 in valid iff {
	// The workstations form a single line between begin and end
	all ws: Workstation, wss: Workstation - ws |
  		ws in begin => ws not in wss.succ
  
  	all ws: Workstation |
  		ws in end => no ws.succ
  
  	all ws: Workstation - end |
  		one ws.succ
}
    S513 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation | w not in w.^succ
  	all w : Workstation | begin in w + w.~succ
  	//all w : Workstation | end in w + w.^succ
}
    S514 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation | w not in w.^succ
  	all w : begin.^succ | end in w + w.^succ
}
    S515 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation | w not in w.^succ
  	all w : end.~succ | begin in w + w.~succ
  	all w : begin.^succ | end in w + w.^succ
}
    S516 in valid iff {
	// The workstations form a single line between begin and end
  	no begin.~succ
  	no end.^succ
  	all w : Workstation | w in begin + begin.^succ
  	all w : Workstation | w in end + end.~succ
  	all w : Workstation | w not in w.^succ
}
    S517 in valid iff {
	// The workstations form a single line between begin and end
  all wk : Workstation | one wk.succ
  all wk : Workstation | wk in begin implies some ( wk.^(succ.succ) & end )

}
    S518 in valid iff {
	// The workstations form a single line between begin and end
  all wk : Workstation | one wk.succ
  all wk : Workstation | wk in begin implies some ( wk.^(succ.succ) & end ) or wk in begin and wk in end 

}
    S519 in valid iff {
	// The workstations form a single line between begin and end
  all wk : Workstation | one wk.succ and ( wk in begin implies wk not in end ) 
  all wk : Workstation | wk in begin implies some ( wk.^(succ.succ) & end )
}
    S520 in valid iff {
	// The workstations form a single line between begin and end
  all wk : Workstation | one wk.succ and ( wk in begin implies wk not in end ) 
  all wk : Workstation | wk in begin iff some ( wk.^(succ.succ) & end )
  
}
    S521 in valid iff {
	// The workstations form a single line between begin and end
  all wk : Workstation | one wk.succ
  all wk : Workstation | wk in begin iff some ( wk.^(succ.succ) & end )
  
}
    S522 in valid iff {
	// The workstations form a single line between begin and end
  	all wk : Workstation | wk in begin iff no (wk.~succ)
	all wk : Workstation | wk in end iff no wk.succ
	all wk : Workstation | wk in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))

  
}
    S523 in valid iff {
	// The workstations form a single line between begin and end
	all ws: Workstation - begin | ws in begin.^succ
	all ws: Workstation - end | end in ws.^succ
  	no end.succ
}
    S524 in valid iff {
	// The workstations form a single line between begin and end
  all w : Workstation | no (w & w.succ) no succ.begin and no end.succ

}
    S525 in valid iff {
	// The workstations form a single line between begin and end
  all w : Workstation | no (w & w.succ) no succ.begin and no end.succ and some begin.succ and some succ.end

}
    S526 in valid iff {
	// The workstations form a single line between begin and end
	all x : begin | no succ.x
  	all x :Workstation - end | one x.succ
  	all x: end | no x.succ and x not in begin
}
    S527 in valid iff {
	// The workstations form a single line between begin and end
	all x : begin | no succ.x
  	all x :Workstation - end | one x.succ
  	all x: end | no x.succ
  	all x : Workstation | some Workstation -x implies no begin & end
}
    S528 in valid iff {
	// The workstations form a single line between begin and end
	all w1 : Workstation | one w2 : Workstation | w1 in w2.succ
}
    S529 in valid iff {
	// The workstations form a single line between begin and end
	one w : Workstation | no w.succ
  
}
    S530 in valid iff {
	// The workstations form a single line between begin and end
	one w : Workstation | no w.succ
	some w : Workstation | no w2 : Workstation | w in w2.succ
  
}
    S531 in valid iff {
	// The workstations form a single line between begin and end
	one w : Workstation | no w.succ
	one w : Workstation | no w2 : Workstation | w in w2.succ
  
  
}
    S532 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | one (w & begin) implies (some (w.succ) and one (w & end)) 
}
    S533 in valid iff {
	// The workstations form a single line between begin and end
	one w1 : Workstation | all w2 :  Workstation - w1 |  w2 in w1.^succ
  	all w : Workstation | #(w.succ) < 2
  	one w1 : Workstation | all w2 :  Workstation - w1 |  w1 in w2.^succ
  	 
}
    S534 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | no (w.succ & begin) and one (w.succ)
}
    S535 in valid iff {
	// The workstations form a single line between begin and end
	one w : Workstation | #w.succ = 0 implies Workstation in w.((^(~succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
}
    S536 in valid iff {
	// The workstations form a single line between begin and end
	one w : Workstation | #w.succ = 0 implies Workstation in w.^(~succ)
}
    S537 in valid iff {
	// The workstations form a single line between begin and end
	one w : Workstation | w.~succ = none and Workstation in w.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) 
}
    S538 in valid iff {
	// The workstations form a single line between begin and end
	one w : Workstation | let succ = w.^succ | Workstation in w+succ
}
    S539 in valid iff {
	// The workstations form a single line between begin and end
	one w : Workstation | let succ = w.^succ | Workstation in succ
}
    S540 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation | #w.succ = 1 implies (w not in w.^succ and Workstation in 	   w.^succ + w)
}
    S541 in valid iff {
	// The workstations form a single line between begin and end
	one w : Workstation | (#w.succ = 1 and #w.~succ = 0) and Workstation in 		w.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) 
}
    S542 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation | (#w.succ + #w.~succ = 1 or #w.succ + #w.~succ = 2) and 	 Workstation in w.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) + w.~((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
}
    S543 in valid iff {
	// The workstations form a single line between begin and end
 	all w: Workstation | one b: begin |one e: end | b in w.succ and e in w.succ

}
    S544 in valid iff {
	// The workstations form a single line between begin and end
 	all w: Workstation | one b: begin |one e: end | b in w.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) and e in w.succ

}
    S545 in valid iff {
	// The workstations form a single line between begin and end
  
one Workstation.succ
}
    S546 in valid iff {
	// The workstations form a single line between begin and end
  
	one Workstation-end.succ 
  	
  	no succ.end
 
}
    S547 in valid iff {
	// The workstations form a single line between begin and end
  no succ.begin
  no end.succ
  some Workstation.succ
 
}
    S548 in valid iff {
	// The workstations form a single line between begin and end
  no succ.begin
  no end.succ
  some Workstation.succ
  all e: begin | end in e.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  
 
}
    S549 in valid iff {
	// The workstations form a single line between begin and end
	all ws1 : Workstation | some ws2 : Workstation | ws2 in begin implies ws1 in ws2.^(succ)
  
  all w : Workstation - end | one w.succ
  
  no end.succ
}
    S550 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | (w not in begin and w not in end) implies some w.succ
}
    S551 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | (w not in begin) and (w not in end) implies one w.succ
}
    S552 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | (w not in begin) and (w not in end) implies one w.succ
  	all w: Workstation | w not in w.succ
}
    S553 in valid iff {
	// The workstations form a single line between begin and end
	all ws:Workstation | one b:Workstation | one e:Workstation |
  		ws in b.^succ and e in b.^succ
}
    S554 in valid iff {
	// The workstations form a single line between begin and end
	all ws:Workstation | one b:begin |
  		b.^succ & ws.^succ = ws.^succ
}
    S555 in valid iff {
	// The workstations form a single line between begin and end
	Workstation in begin.^succ
  	Workstation in end.^(~succ)
  	
  	all ws:Workstation - begin - end | one s:Workstation | one p:Workstation |
  		s = ws.succ and p = ws.~succ
}
    S556 in valid iff {
	// The workstations form a single line between begin and end
	Workstation in begin.^succ
  	Workstation in end.^(~succ)
  	
  	all ws:Workstation - end - begin | one s:Workstation | one p:Workstation |
  		s = ws.succ and p = ws.~succ
  
  	all ws:Workstation | ws not in ws.succ
}
    S557 in valid iff {
	// The workstations form a single line between begin and end
  all w: Workstation |  #w.succ = 1 and w != begin implies w in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))

}
    S558 in valid iff {
	// The workstations form a single line between begin and end
  all w: Workstation |  w!= end implies #w.succ = 1 and (w != begin implies w in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)))

}
    S559 in valid iff {
	// The workstations form a single line between begin and end
  all w: Workstation | ( w!= end implies #w.succ = 1) and (w != begin implies w in begin.^succ) and w.succ != w

}
    S560 in valid iff {
	// The workstations form a single line between begin and end
	all ws: Workstation - begin |
  		ws in begin.^(succ) and 
  		Workstation - begin.^(succ) = none
}
    S561 in valid iff {
	// The workstations form a single line between begin and end
	all ws1, ws2: Workstation | ws2 not in ws1.succ.^succ
}
    S562 in valid iff {
	// The workstations form a single line between begin and end
	all ws1, ws2: Workstation | ws2 not in ws1.succ.^succ
  	end.succ = none
}
    S563 in valid iff {
	// The workstations form a single line between begin and end
	all ws1, ws2: Workstation | ws2 not in ws1.succ.^succ
  	end.succ = none
  	begin & end = none
}
    S564 in valid iff {
	// The workstations form a single line between begin and end
	all ws: Workstation | ws.succ != none iff ws != end
  	all disj w1, w2: Workstation | w1.succ != w2.succ
}
    S565 in valid iff {
	// The workstations form a single line between begin and end
	all ws: Workstation | ws not in ws.^succ and ws.succ != none iff ws != end
  	all disj w1, w2: Workstation | w1.succ != w2.succ
}
    S566 in valid iff {
	// The workstations form a single line between begin and end
	all ws: Workstation | ws not in ws.^succ and (ws.succ != none iff ws != end)
  	all disj w1, w2: Workstation | w1.succ != w2.succ
}
    S567 in valid iff {
	// The workstations form a single line between begin and end
  	#begin.succ = 1
  	#end.succ = 0
	all ws: Workstation | ws not in ws.^succ and (ws.succ != none iff ws != end)
  	all disj w1, w2: Workstation | w1.succ & w2.succ = none
}
    S568 in valid iff {
	// The workstations form a single line between begin and end
	all ws: Workstation | end in ws.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) and (ws.succ != none iff ws not in end)
  	all disj w1, w2: Workstation | w1.succ & w2.succ = none
}
    S569 in valid iff {
	// The workstations form a single line between begin and end
  	begin = end or
	all ws: Workstation | ws.succ != none iff ws not in end
}
    S570 in valid iff {
	// The workstations form a single line between begin and end
  	begin = end or
	all ws: Workstation | (#ws.succ = 1 iff ws not in end) and ws not in ws.^succ 
}
    S571 in valid iff {
	// The workstations form a single line between begin and end
  	all ws: Workstation | 
  		ws not in ws.^succ and
  		ws not in end implies #ws.succ = 1
}
    S572 in valid iff {
	// The workstations form a single line between begin and end
	all ws:Workstation | #ws.succ=1 and ws not in ws.succ
  	one disj ws1,ws2:Workstation | ws1 in begin and ws2 in end
}
    S573 in valid iff {
	// The workstations form a single line between begin and end
	all ws:Workstation | (ws not in end implies #ws.succ=1) and ws not in ws.succ and
  							(ws not in begin implies ws in Workstation.succ)
  	one ws1,ws2:Workstation | ws1 in begin and ws2 in end
}
    S574 in valid iff {
	// The workstations form a single line between begin and end
	all ws : Workstation | ws in begin.^(succ) 
  	all wsend : Workstation | end in wsend.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
}
    S575 in valid iff {
	// The workstations form a single line between begin and end
	all ws : Workstation | ws in begin.^(succ) 
  	all wsend : Workstation | end in wsend.^(succ)
  	begin.succ != end
}
    S576 in valid iff {
	// The workstations form a single line between begin and end
	all ws : Workstation | ws in begin.^(succ) 
  	all wsend : Workstation | end in wsend.^(succ)
  	begin & end != none
}
    S577 in valid iff {
	// The workstations form a single line between begin and end
	all ws : Workstation | ws in begin.^(succ) 
  	all wsend : Workstation | end in wsend.^(succ)
  	begin & end != none implies #(begin.succ) = 0
}
    S578 in valid iff {
	// The workstations form a single line between begin and end
end in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  all ws : Workstation | ws != end implies one ws.succ
  all ws : Workstation | ws != begin implies one pre : Workstation | ws in pre.succ
}
    S579 in valid iff {
	// The workstations form a single line between begin and end
	end in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  	begin in ((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)).end
  	all wo : Workstation | wo.succ not = none => begin not = end
}
    S580 in valid iff {
	// The workstations form a single line between begin and end
  	succ not in ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)
}
    S581 in valid iff {
	// The workstations form a single line between begin and end
  	succ - ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden) = succ
  	Workstation in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  	begin.succ not = none => end in begin.^succ
  	((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden) not in ^succ
}
    S582 in valid iff {
	// The workstations form a single line between begin and end
  	succ - ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden) = succ
  	Workstation in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  	begin.succ not = none => end in begin.^succ
  	all wo : Workstation | wo not in wo.^succ
}
    S583 in valid iff {
	// The workstations form a single line between begin and end
  	all disj wo1, wo2 : Workstation | wo1.succ not = none => wo2 in wo1.^succ and wo1 not in wo1.^succ
}
    S584 in valid iff {
	// The workstations form a single line between begin and end
  	end in begin.^succ
  	all disj wo1, wo2 : Workstation | wo1.succ not = none => wo2 in wo1.^succ and wo1 not in wo1.^succ
}
    S585 in valid iff {
	// The workstations form a single line between begin and end
  	begin not = end => end in begin.^succ
  	all disj wo1, wo2 : Workstation | wo1.succ not = none => wo2 in wo1.^succ and wo1 not in wo1.^succ
}
    S586 in valid iff {
	// The workstations form a single line between begin and end
  	#Workstation = 1 => begin = end and succ = none->none
  	end in begin.^succ
}
    S587 in valid iff {
	// The workstations form a single line between begin and end
  	#Workstation = 1 => begin = end and succ = none->none
  	#Workstation != 1 => end in begin.^succ
}
    S588 in valid iff {
	// The workstations form a single line between begin and end
  	#Workstation = 1 => begin = end and succ = none->none
  	Workstation in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  	Workstation in (begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) & ((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)).end)
}
    S589 in valid iff {
	// The workstations form a single line between begin and end
  	Workstation in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
    all wo : Workstation | (wo.succ not = none => wo not in wo.^succ) and wo.succ = none => wo = end
}
    S590 in valid iff {
	// The workstations form a single line between begin and end
  	Workstation in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
    all wo : Workstation | (wo.succ != none => wo not in wo.^succ)
  	one wo : Workstation | wo.succ = none => wo = end
}
    S591 in valid iff {
	// The workstations form a single line between begin and end
  	Workstation in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
    //all wo : Workstation | (wo.succ != none => wo not in wo.^succ and #wo.succ = 1)
  	//all wo : Workstation | wo.succ = none => wo = end
  	all wo : Workstation-begin-end | one wo.succ
}
    S592 in valid iff {
	// The workstations form a single line between begin and end
  	Workstation in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
    //all wo : Workstation | (wo.succ != none => wo not in wo.^succ and #wo.succ = 1)
  	//all wo : Workstation | wo.succ = none => wo = end
  	all wo : Workstation-begin-end | one wo.succ and wo not in wo.^succ
}
    S593 in valid iff {
	// The workstations form a single line between begin and end
  	Workstation-begin in begin.^succ
    //all wo : Workstation | (wo.succ != none => wo not in wo.^succ and #wo.succ = 1)
  	//all wo : Workstation | wo.succ = none => wo = end
  	all wo : Workstation-end | one wo.succ and wo not in wo.^succ
}
    S594 in valid iff {
	// The workstations form a single line between begin and end
  all b : begin | some succ.b

}
    S595 in valid iff {
	// The workstations form a single line between begin and end
	end in begin.^succ and end.succ = none
}
    S596 in valid iff {
	// The workstations form a single line between begin and end
  	all w: Workstation | w != end implies one w.succ and w != begin implies one succ.w

}
    S597 in valid iff {
	// The workstations form a single line between begin and end
  ^succ = (Workstation -> Workstation) - (end -> Workstation) - ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)

}
    S598 in valid iff {
	// The workstations form a single line between begin and end
  ((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) = ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden) + (Workstation -> end) and no end.succ and no succ.begin

}
    S599 in valid iff {
	// The workstations form a single line between begin and end
	begin != end implies end in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) else no begin.succ
}
    S600 in valid iff {
	// The workstations form a single line between begin and end
	no succ.begin
	no end.succ
	all w : Workstation | w in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
	all disj w1, w2: Workstation | w1 in w2.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) implies w2 not in w1.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) 
}
    S601 in valid iff {
	// The workstations form a single line between begin and end
	(all ws : Workstation | ws.succ != ws) and end = begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
}
    S602 in valid iff {
	// The workstations form a single line between begin and end
	(all ws : Workstation | (one ws2 : Workstation | ws.succ = ws2) or ws = end) and no ws : Workstation | ws.succ = begin
}
    S603 in valid iff {
	// The workstations form a single line between begin and end
	(all ws : Workstation | (one ws2 : Workstation | ws != ws2 and ws.succ = ws2) or ws = end) and no ws : Workstation | ws.succ = begin
}
    S604 in valid iff {
	// The workstations form a single line between begin and end
	// Only 'begin' has no predecessor
  no w: Workstation - begin | some w.~succ
  
  // Only 'end' has no successor
  no w: Workstation - end | some w.succ

  // Every workstation (except end) has at most one successor
  all w: Workstation - end | lone w.succ

  // Every workstation (except begin) has at most one predecessor
  all w: Workstation - begin | lone w.~succ
}
    S605 in valid iff {
	// The workstations form a single line between begin and end
	// Only 'begin' has no predecessor
  no w: Workstation - begin | one w.~succ
  
  // Only 'end' has no successor
  no w: Workstation - end | one w.succ

  // Every workstation (except end) has at most one successor
  all w: Workstation - end | lone w.succ

  // Every workstation (except begin) has at most one predecessor
  all w: Workstation - begin | lone w.~succ
  
  all w: Workstation | w not in w.succ
}
    S606 in valid iff {
	// The workstations form a single line between begin and end
  // Every workstation (except end) has at most one successor
  all w: Workstation - end | lone w.succ

  // Every workstation (except begin) has at most one predecessor
  all w: Workstation - begin | lone w.~succ
  
  all w: Workstation | w not in w.succ
}
    S607 in valid iff {
	// The workstations form a single line between begin and end
	no begin.~succ and no end.succ and one (Workstation - (begin + end)).succ and one (Workstation - (begin + end)).~succ
}
    S608 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation | 
		// begin has no predecessor and end has no successor
		(w = begin) iff no w.~succ and
		(w = end) iff no w.succ and
		no w & w.^succ
}
    S609 in valid iff {
	// The workstations form a single line between begin and end
  	all w : Workstation - end | one w.succ
  	all w : Workstation - begin | one succ.w
	one Workstation implies no Workstation.succ
}
    S610 in valid iff {
	// The workstations form a single line between begin and end
  	(all w : Workstation - end | one w.succ and all w : Workstation - begin | one succ.w) or no succ.begin and no end.succ
  	
}
    S611 in valid iff {
	// The workstations form a single line between begin and end
  	all w : Workstation - end | one w.succ and no end.succ
  	all w : Workstation - begin | one succ.w and no succ.begin
  	
  	
}
    S612 in valid iff {
	// The workstations form a single line between begin and end
	(Workstation & begin).^succ in (Workstation & end) 
}
    S613 in valid iff {
	// The workstations form a single line between begin and end
	all ws:Workstation | ws not in ws.^succ
	(Workstation & begin).^succ in (Workstation & end) 
}
    S614 in valid iff {
    // The workstations form a single line between begin and end
    all ws: Workstation | ws != end implies some s: Workstation | ws.succ = s
    all ws: Workstation | ws != begin implies some p: Workstation | p.succ = ws
}
    S615 in valid iff {
	// The workstations form a single line between begin and end
	all w:Workstation | one w.succ or one succ.w
}
    S616 in valid iff {
	// The workstations form a single line between begin and end
	all w:Workstation | (one w.succ) or (one succ.w)
	all w:Workstation | w.succ not in w
}
    S617 in valid iff {
	// The workstations form a single line between begin and end

  all b:begin, e:end | b.^succ in ^succ.e
  
}
    S618 in valid iff {
	// The workstations form a single line between begin and end
	all w:Workstation | (one w.succ) or (one succ.w)
	all w:Workstation | w not in w.succ
}
    S619 in valid iff {
	// The workstations form a single line between begin and end
	all w:Workstation | (one w.succ) or (one succ.w)
	all w:Workstation | w not in w.^succ
}
    S620 in valid iff {
	// The workstations form a single line between begin and end

  begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) in ((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)).end
  
}
    S621 in valid iff {
	// The workstations form a single line between begin and end

  begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) in ((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)).end and end != begin
  
}
    S622 in valid iff {
	// The workstations form a single line between begin and end

  Workstation in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)) & succ.end
  
}
    S623 in valid iff {
	// The workstations form a single line between begin and end
	all ws:Workstation | ws not in ws.^succ and lone ws.succ and lone succ.ws
	end in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
	//all ws:Workstation | begin in *succ.ws
  	no end.succ
 
}
    S624 in valid iff {
	// The workstations form a single line between begin and end
	all ws:Workstation | ws not in ws.^succ and lone ws.succ and lone succ.ws
	no succ.begin
  	no end.succ
 
}
    S625 in valid iff {
	// The workstations form a single line between begin and end
  one end.succ

}
    S626 in valid iff {
	// The workstations form a single line between begin and end
	all w:Workstation | lone w.succ and w not in w.^succ and (one w.succ or one succ.w)
}
    S627 in valid iff {
	// The workstations form a single line between begin and end
	all disj w1, w2:Workstation | w1 in w2.^succ implies w1 != w2
  	all w:Workstation - end | one w.succ
  	all w:Workstation - begin | one ~succ.w
}
    S628 in valid iff {
	// The workstations form a single line between begin and end
  	all ws:Workstation-begin | one succ.ws
  	all ws:Workstation-end | one succ.ws
  	

}
    S629 in valid iff {
	// The workstations form a single line between begin and end

  Workstation in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  no end.succ 
  workstation.~workstation not in ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)
  
}
    S630 in valid iff {
	// The workstations form a single line between begin and end

  Workstation in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  no end.succ 
  succ.~succ not in ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden)
  begin != end
  
}
    S631 in valid iff {
	// The workstations form a single line between begin and end
  	all ws:Workstation-begin | one succ.ws
  	all ws:Workstation-end | one succ.ws
  	no succ.begin
  	no end.succ
  	

}
    S632 in valid iff {
	// The workstations form a single line between begin and end
  	all w: Workstation | lone w.succ
  	end = begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
}
    S633 in valid iff {
	// The workstations form a single line between begin and end
  	all w1 : Workstation | all w2 : Workstation | all w3 : Workstation |
  	w1.succ = w2 and w2.succ = w3 implies w3.succ != w1.succ

}
    S634 in valid iff {
	// The workstations form a single line between begin and end
  	//all w1 : Workstation | all w2 : Workstation | all w3 : Workstation |
  	//w1.succ = w2 and w2.succ = w3 implies w3.succ != (w1 or w2)
    //all w : Workstation |  w not in  w.^succ 
  
    no Workstation->end.succ 
  
    no Workstation->begin.~succ 
  
  	Workstation->end in Workstation->begin.^succ 
}
    S635 in valid iff {
	// The workstations form a single line between begin and end
  	all w1, w2, w3: Workstation | w2 in w1.succ and w3 in w2.succ implies w1 in begin and w3 in end


}
    S636 in valid iff {
	// The workstations form a single line between begin and end
  	all w1, w2, w3: Workstation | w1 != w2 and w2 != w3 and w1 != w3 and w2 in w1.succ and w3 in w2.succ implies w1 in begin and w3 in end


}
    S637 in valid iff {
	// The workstations form a single line between begin and end
  	all w1, w2, w3: Workstation | (w1 != w2 and w2 != w3 and w1 != w3 and w2 in w1.succ and w3 in w2.succ implies w1 in begin and w3 in end)
  all w4: Workstation | w4 not in w4.succ


}
    S638 in valid iff {
	// The workstations form a single line between begin and end
  	all w1, w2, w3: Workstation | (w1 != w2 and w2 != w3 and w1 != w3 and w2 in w1.succ and w3 in w2.succ implies w1 in begin and w3 in end)
	all w4, w5: Workstation | w4 in begin and w4 in end implies w5 not in w4.succ
	all w6: Workstation | w6 not in w6.succ


}
    S639 in valid iff {
	// The workstations form a single line between begin and end
  	all w1, w2, w3: Workstation | (w1 != w2 and w2 != w3 and w1 != w3 and w2 in w1.succ and w3 in w2.succ implies w1 in begin and w3 in end)
	all w4, w5: Workstation | w5 in w4.succ implies w5 not in begin and w4 not in end
	all w6: Workstation | w6 not in w6.succ


}
    S640 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | lone w1, w2: Workstation | w in w1.succ and w2 in w.succ

}
    S641 in valid iff {
	// The workstations form a single line between begin and end
	all w: Workstation | lone w1, w2: Workstation | w in w1.succ and w2 in w.succ and no end.succ and no succ.begin 

}
    S642 in valid iff {
	// The workstations form a single line between begin and end
  all w : Workstation - end | one w.succ and (w.succ != w)
  all w : Workstation - begin | one succ.w and (w.succ != w)
  
  
  

}
    S643 in valid iff {
	// The workstations form a single line between begin and end
	all w : Workstation | w in begin.((^(succ)) + ((this.@Workstation + this.@Worker + this.@Product + Int + String) <: iden))
  	end not in end.succ
  	all w : Workstation | lone w.succ
}
    S644 in valid iff {
	// The workstations form a single line between begin and end
	succ in (Workstation - end) lone -> lone Workstation 
  	
  	
}
    S645 in valid iff {
	// The workstations form a single line between begin and end
	succ in (Workstation - end) lone -> lone Workstation and
  	(begin.^succ = end or begin = end)
  	
  	
}
    S646 in valid iff {
	// The workstations form a single line between begin and end
	succ in (Workstation - end) lone -> lone (Workstation - begin) and
  	(begin.^succ = end or begin = end)
  	
  	
}
    S647 in valid iff {
	// The workstations form a single line between begin and end
	succ in (Workstation - end) lone -> lone (Workstation - begin) and
  	((begin.^succ = end and all ws : Workstation | begin.^succ = ws) or begin = end)
  	
  	
}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, S74, S75, S76, S77, S78, S79, S80, S81, S82, S83, S84, S85, S86, S87, S88, S89, S90, S91, S92, S93, S94, S95, S96, S97, S98, S99, S100, S101, S102, S103, S104, S105, S106, S107, S108, S109, S110, S111, S112, S113, S114, S115, S116, S117, S118, S119, S120, S121, S122, S123, S124, S125, S126, S127, S128, S129, S130, S131, S132, S133, S134, S135, S136, S137, S138, S139, S140, S141, S142, S143, S144, S145, S146, S147, S148, S149, S150, S151, S152, S153, S154, S155, S156, S157, S158, S159, S160, S161, S162, S163, S164, S165, S166, S167, S168, S169, S170, S171, S172, S173, S174, S175, S176, S177, S178, S179, S180, S181, S182, S183, S184, S185, S186, S187, S188, S189, S190, S191, S192, S193, S194, S195, S196, S197, S198, S199, S200, S201, S202, S203, S204, S205, S206, S207, S208, S209, S210, S211, S212, S213, S214, S215, S216, S217, S218, S219, S220, S221, S222, S223, S224, S225, S226, S227, S228, S229, S230, S231, S232, S233, S234, S235, S236, S237, S238, S239, S240, S241, S242, S243, S244, S245, S246, S247, S248, S249, S250, S251, S252, S253, S254, S255, S256, S257, S258, S259, S260, S261, S262, S263, S264, S265, S266, S267, S268, S269, S270, S271, S272, S273, S274, S275, S276, S277, S278, S279, S280, S281, S282, S283, S284, S285, S286, S287, S288, S289, S290, S291, S292, S293, S294, S295, S296, S297, S298, S299, S300, S301, S302, S303, S304, S305, S306, S307, S308, S309, S310, S311, S312, S313, S314, S315, S316, S317, S318, S319, S320, S321, S322, S323, S324, S325, S326, S327, S328, S329, S330, S331, S332, S333, S334, S335, S336, S337, S338, S339, S340, S341, S342, S343, S344, S345, S346, S347, S348, S349, S350, S351, S352, S353, S354, S355, S356, S357, S358, S359, S360, S361, S362, S363, S364, S365, S366, S367, S368, S369, S370, S371, S372, S373, S374, S375, S376, S377, S378, S379, S380, S381, S382, S383, S384, S385, S386, S387, S388, S389, S390, S391, S392, S393, S394, S395, S396, S397, S398, S399, S400, S401, S402, S403, S404, S405, S406, S407, S408, S409, S410, S411, S412, S413, S414, S415, S416, S417, S418, S419, S420, S421, S422, S423, S424, S425, S426, S427, S428, S429, S430, S431, S432, S433, S434, S435, S436, S437, S438, S439, S440, S441, S442, S443, S444, S445, S446, S447, S448, S449, S450, S451, S452, S453, S454, S455, S456, S457, S458, S459, S460, S461, S462, S463, S464, S465, S466, S467, S468, S469, S470, S471, S472, S473, S474, S475, S476, S477, S478, S479, S480, S481, S482, S483, S484, S485, S486, S487, S488, S489, S490, S491, S492, S493, S494, S495, S496, S497, S498, S499, S500, S501, S502, S503, S504, S505, S506, S507, S508, S509, S510, S511, S512, S513, S514, S515, S516, S517, S518, S519, S520, S521, S522, S523, S524, S525, S526, S527, S528, S529, S530, S531, S532, S533, S534, S535, S536, S537, S538, S539, S540, S541, S542, S543, S544, S545, S546, S547, S548, S549, S550, S551, S552, S553, S554, S555, S556, S557, S558, S559, S560, S561, S562, S563, S564, S565, S566, S567, S568, S569, S570, S571, S572, S573, S574, S575, S576, S577, S578, S579, S580, S581, S582, S583, S584, S585, S586, S587, S588, S589, S590, S591, S592, S593, S594, S595, S596, S597, S598, S599, S600, S601, S602, S603, S604, S605, S606, S607, S608, S609, S610, S611, S612, S613, S614, S615, S616, S617, S618, S619, S620, S621, S622, S623, S624, S625, S626, S627, S628, S629, S630, S631, S632, S633, S634, S635, S636, S637, S638, S639, S640, S641, S642, S643, S644, S645, S646, S647 extends Formula {}

run {
    #valid.Oracle = 4
    #(Instance - valid.Oracle) = 4
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 12 Atom, exactly 4 WorkstationAtom, exactly 4 WorkerAtom, exactly 4 ProductAtom,
       exactly 8 Instance, 6 Int
