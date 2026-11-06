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
    Oracle in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all ws: Workstation | some ws.workers
  	all w: Worker | one ws: Workstation | w in ws.workers
}
    S1 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	(all w : Workstation | some w.workers) and (all w1 : Worker | w1 in Workstation.workers)
}
    S2 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  	all ws: Workstation | ws.workers in Workstation and all w: ws.workers | w in ws


}
    S3 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all u: Worker | one w: Workstation | u in w.workers
}
    S4 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  all wst : Workstation | some wst.workers and one workers.wst 

}
    S5 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  	some w1: Worker | Workstation.workers = w1
}
    S6 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	some Workstation.workers
}
    S7 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	some Workstation.workers
  	all w : Worker | w in Workstation.workers
}
    S8 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	some Workstation.workers
  	all x: Worker | one workers.x
}
    S9 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all w : Workstation | some(w.workers)
  	all w : Worker | lone(workers.w)
}
    S10 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	workers in (Workstation lone -> one Worker )
}
    S11 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all w : Worker | lone wo: Workstation | w in Workstation.workers and w in wo.workers
}
    S12 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	
}
    S13 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	workers in (Workstation some -> lone Worker)
}
    S14 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	workers in (Workstation one -> one Worker)
}
    S15 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all w:Worker | w in Workstation.workers
  	//one Worker in Workstation
}
    S16 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all w : Workstation | some w.workers and one ~workers.w
}
    S17 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all w: Worker, k: Workstation | w in k.workers
}
    S18 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all w: Worker, k: Workstation | some k.workers
}
    S19 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all k: Workstation | some k.workers
  	all w: Worker, k: Workstation | w in k.workers
}
    S20 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all k: Workstation | some k.workers
  	some w: Worker, k1: Workstation, k2: Workstation | (w not in k1.workers) and (w not in k2.workers)
}
    S21 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all k: Workstation | some k.workers
  	//all w: Worker | all disj k1: Workstation, k2: Workstation | (w in k1.workers) implies (w not in k2.workers)
}
    S22 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  	all wo: Workstation, wor: Worker | some workstation.workers and one workers.wor
}
    S23 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  all wst : Workstation , w : Worker| some wst.workers and one workers.wst 

}
    S24 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  	all wo: Workstation, wor: Worker | some wo.workers and one workers.wor
}
    S25 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  	all wo: Workstation, wor: Worker | one wo.workers and one workers.wor
}
    S26 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  	all w : Worker, ws : Workstation | ws in workers.w and lone ws.workers

}
    S27 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all ws : Workstation |
		one ws.workers and
		all w : Worker | w in Worker and w in ws.workers
}
    S28 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  all w:Workstation | some ws:Worker | ws in w.workers 
  all ws:Worker | one w:Workstation | w.workers in ws

}
    S29 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all s : Workstation, w : Worker | some Workstation.workers
}
    S30 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	some Workstation.workers
  	all w : Human | w in Workstation.workers
}
    S31 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all s : Workstation, w: Worker | some s.workers and some workers.w 
}
    S32 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  	all ws : Workstation | all w : Worker | w in ws.workers
  	all w : Worker | one ws : Workstation | ws in workers.w
  	

}
    S33 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  	all w : Worker, ws : Workstation | ws in workers.w and some ws.workers and some ws.succ.workers

}
    S34 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  	all w : Worker, ws : Workstation | ws in workers.w and ws.workers in w and some ws.succ.workers

}
    S35 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	some Workstation.workers
  	one workers.Worker
}
    S36 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  	all x : Workstation | some Worker 
    all x : Worker | one Workstation

}
    S37 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  	all x : Workstation | some Worker 

}
    S38 in valid iff {
	// Every workstation has workers and every worker works in one workstation

  all w : Worker, s : Workstation | some s.workers and one workers.w
  all s : Workstation | s.succ in Workstation-s
  
}
    S39 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all ws : Workstation |
		one ws.workers and
		all w : Worker | w in Worker-Robot and w in ws.workers
}
    S40 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all wk : Workstation | all w : Worker | some wk.workers and (w in wk.workers <=> w not in wk.workers.^(succ)) and (wk not in wk.succ)
}
    S41 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all x: Workstation | x.workers != none
  	all x: Worker | some y: Workstation | x in y.workers implies
  									x not in (Workstation - y).workers

}
    S42 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all w : Workstation | some w1 : Worker | w1 in w.workers
  	one w : Workstation | all w1 : Worker | w1 in w.workers
}
    S43 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	(all w: Workstation | some w.workers)
	&& (all w: Worker | one (Workstation->Worker).w)
}
    S44 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	(all w: Workstation | some w.workers)
	&& (all w: Worker | one (Workstation->workers).w)
}
    S45 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all ws: Workstation | ws.workers in Worker
	all w: Worker | one Workstation.workers
	all sw: Workstation.succ | sw.workers in Worker
}
    S46 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  all w : Workstation | some w.workers
  all w : Worker | one s : Workstation | w in s.workers implies w not in (Workstation-s).workers
}
    S47 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  	all ws : Workstation | some w : ws.workers | ws in workers.w and 
  	all w1 : Worker | one ws : Workstation | ws in workers.w

}
    S48 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	one ws : Workstation | all w : Worker | one ws1 : Workstation | some w1 : Worker | w1 in ws1 and w in ws
}
    S49 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	one ws : Workstation | all w : Worker | one ws1 : Workstation | some w1 : Worker | w1 in ws1.workers and w in ws.workers
}
    S50 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	one ws : Workstation | all w : Worker | all ws1 : Workstation | some w1 : Worker | w1 in ws1.workers and w in ws.workers
}
    S51 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all ws : Workstation | some ws.workers
	one Workstation.workers
}
    S52 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  	one ws : Workstation | all w : Worker | w in ws.workers

}
    S53 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  	all wt : Workstation | one w : Worker | w in wt.workers
  	one wt : Workstation | all w : Worker | w in wt.workers

}
    S54 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  	all wt : Workstation | some w : Worker | w in wt.workers
  	some wt : Workstation | all w : Worker | w in wt.workers

}
    S55 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all wo: Worker | wo in Workstation.workers
  	all w: Workstation | some wo: Worker | w.workers = wo
}
    S56 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all w: Worker |  w in Workstation.workers
  	some w: Worker | lone ws: Workstation | ws.workers = w
  }
    S57 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	// all w: Worker |  w in Workstation.workers
  	some w: Worker | lone ws: Workstation | ws.workers = w
}
    S58 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	//all y: Worker |  one x: Workstation | x in workers.y implies
	//all x: Workstation | one y: Worker | x in workers.y
	one x: Workstation, y: Worker | some x implies y in x.workers
//	all x: Workstation, y: Worker | some x implies some y
	all x: Workstation, y: Worker | some y implies one x
  
  	all y: Worker | one x: Workstation | some y implies y in x.workers
  

  
}
    S59 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all w: Worker | some w2: Worker |  w in Workstation.workers and Workstation.workers = w2
}
    S60 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all w: Worker | some w2: Worker | lone w3: Workstation |  w in Workstation.workers and w3.workers = w2
}
    S61 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  	all w: Workstation | #(w.workers) > 0 and #(w.workers & Human)  > 0 
  	all disj w1,w2: Workstation |  #(w1.workers & w2.workers) = 0

}
    S62 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  	all w: Workstation | #(w.workers) > 0 and #(w.workers & Human) > 0 
  	all disj w1,w2: Workstation |  #(w1.workers & w2.workers) = 0
  	no w: Worker | some ws: Workstation | w not in ws.workers

}
    S63 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  	all w: Workstation | #(w.workers) > 0 and #(w.workers & Human) > 0 
  	all disj w1,w2: Workstation |  #(w1.workers & w2.workers) = 0
  	no w: Worker | lone ws: Workstation | w not in ws.workers

}
    S64 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all w : Workstation | one w2 : Workstation | all ws : Worker | some w.workers and w2.workers = ws
}
    S65 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all x: Workstation| some x.workers implies #x.workers > 1 
}
    S66 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all w : Worker | lone x:Workstation| w in Workstation.workers
}
    S67 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all w : Workstation, u: Worker | some w.workers or one workers.u
}
    S68 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  
  all ws : Workstation, w : Worker | one (ws.workers)

}
    S69 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  
  all ws : Workstation, w : Worker |  some (ws.workers)  and one workers.w and some ws.succ

}
    S70 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  
  all ws : Workstation, w : Worker |  one (ws.workers)  and some workers.w 

}
    S71 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all ws: Workstation, w: Worker | one ws1: Workstation | (ws -> w in workers) implies w in ws1 
}
    S72 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  
  all wo : Workstation | (lone w : Worker | wo-> w in workers )

  all w : Worker | (one wo : Workstation | wo -> w in workers)

}
    S73 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all w : Workstation | #(w.workers) > 1
}
    S74 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all w : Workstation | #(w.workers) > 1
  
    all w: Worker | one work : Workstation | w in work.workers
}
    S75 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  all ws: Workstation, w: Worker | (ws in ws.succ) implies (w in ws.workers)

}
    S76 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  all ws: Workstation, w: Worker | (ws in ws.succ) implies (w in ws.workers) 
  all w: Worker | one ws: Workstation | w in ws.workers
}
    S77 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  all ws: Workstation, w: Worker | (ws in ws.succ) implies (w in ws.workers) 
  all w: Worker | some ws: Workstation | w in ws.workers
}
    S78 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  all ws: Workstation | #ws.workers>0 and no ws1: Workstation | ws1 != ws and #(ws.workers & ws1.workers) =0

}
    S79 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	Workstation.workers != none implies Workstation.workers = Worker
}
    S80 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all w : Workstation, we : Worker | some w.workers and lone we.~workers
}
    S81 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	workers.Worker = Workstation and #workers = #Worker
}
    S82 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	one workers
}
    S83 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	one x: Workstation| one y: Worker | y in x.workers and x in workers.y
}
    S84 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all x: Workstation, y:Worker | one x.workers iff one workers.y  
}
    S85 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all x: Workstation, y:Worker | some x.workers iff one workers.y  
}
    S86 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all x: Workstation, y:Worker | some x.workers implies one workers.y
}
    S87 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all x: Workstation, y:Worker | some x.workers implies x in workers.y and y in x.workers
}
    S88 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all x: Workstation| one y: Worker | some x.workers and one workers.y
}
    S89 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all x: Workstation| one y: Worker | x in x.workers implies some x.workers and one workers.y
}
    S90 in valid iff {
	// Every workstation has workers and every worker works in one workstation
	all x: Workstation| one y: Worker | x in workers.y implies some x.workers and one workers.y
}
    S91 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  all w:Workstation | some w.succ

}
    S92 in valid iff {
	// Every workstation has workers and every worker works in one workstation
  all w:Workstation | some w.succ
  all w:Worker | one ww: Workstation | w in ww.workers

}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, S74, S75, S76, S77, S78, S79, S80, S81, S82, S83, S84, S85, S86, S87, S88, S89, S90, S91, S92 extends Formula {}

run {
    #valid.Oracle = 3
    #(Instance - valid.Oracle) = 3
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 12 Atom, exactly 4 WorkstationAtom, exactly 4 WorkerAtom, exactly 4 ProductAtom,
       exactly 6 Instance, 6 Int
