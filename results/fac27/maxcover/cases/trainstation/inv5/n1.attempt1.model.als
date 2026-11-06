abstract sig Atom {}
sig TrackAtom, SignalAtom extends Atom {}
abstract sig Formula {}
one sig Oracle extends Formula {}
sig detected in Formula {}
sig Instance {
    valid : set Formula,
    Track : set TrackAtom,
    Junction : set TrackAtom,
    Entry : set TrackAtom,
    Exit : set TrackAtom,
    Signal : set SignalAtom,
    Semaphore : set SignalAtom,
    Speed : set SignalAtom,
    succs : TrackAtom -> TrackAtom,
    signals : TrackAtom -> SignalAtom
} {
    succs in Track -> Track
    signals in Track -> Signal
    Junction + Entry + Exit in Track
    Semaphore + Speed in Signal
    no Semaphore & Speed
    // Earlier requirement 0, required in every Instance.
{
	// The station has at least one entry and one exit
	some Entry and some Exit
}
    // Earlier requirement 1, required in every Instance.
{
	// Signals belong to one track
  all s: Signal | one t: Track | s in t.signals
}
    // Earlier requirement 2, required in every Instance.
{
	// Exit tracks are those without successor
  	all t : Track | t in Exit iff no t.succs

}
    // Earlier requirement 3, required in every Instance.
{
	// Entry tracks are those without predecessors
	all t : Track | no succs.t iff t in Entry
}
    Oracle in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t: Track | #(succs.t) > 1 <=> t in Junction
}
    S1 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t: Track | #(succs.t) > 1 => t in Junction
}
    S2 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	all disj a, b, c: Track | c in (b.succs & c.succs) implies c in Junction
}
    S3 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	all disj a, b, c: Track | a in (b.succs & c.succs) implies a in Junction
}
    S4 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	all disj a, b, c: Track | a in (b.succs & c.succs) implies a in Junction else a not in Junction
}
    S5 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t: Junction | some succs.t
}
    S6 in valid iff {
	// Junctions are the tracks with more than one predecessor
	//all t: Junction | some disj t1: Track, t2: Track | one t1 
  	all t: Junction | #succs.t > 1
}
    S7 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	all t : Track | #succs.t > 1 and t in Junction
}
    S8 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t: Track | some disj a, b: Track | t in (a.succs & b.succs) implies t in Junction 
}
    S9 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t: Track | some disj a, b: Track | t in (a.succs & b.succs) implies t in Junction else t not in Junction
}
    S10 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t: Track | some disj a, b: Track | t in (a.succs + b.succs) implies t in Junction else t not in Junction
}
    S11 in valid iff {
	// Junctions are the tracks with more than one predecessor
  // Perguntar Alcino
  
  all j: Junction | some s1,s2:Track -j  | j in s1.succs and j in s2.succs and not (s1=s2)

}
    S12 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t: Track {
  		(t in Junction) iff (
      	some disj t1, t2: Track | t != t1 and t != t2 and t in t1.succs and t in t2.succs
      )
  }
}
    S13 in valid iff {
	// Junctions are the tracks with more than one predecessor
    Junction = {x: Track | #{x: Track | x in (this.@Track + this.@Signal + Int + String).succs} > 1 }

}
    S14 in valid iff {
	// Junctions are the tracks with more than one predecessor

}
    S15 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t: Junction | all disj t1: Track, t2: Track | (t in t1.succs) and (t in t2.succs)
  	//all t: Junction | #succs.t > 1
}
    S16 in valid iff {
    // Junctions are the tracks with more than one predecessor
      all t:Track | some succs.t iff t in Junction

}
    S17 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	some t: Track | t in Junction iff some t.~succs

}
    S18 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t: Track | some succs.t implies t in Junction 
}
    S19 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	//all t: Track | some t.~succs implies t in Junction
  	all t: Track | #(t.^succs) > 1 implies t in Junction

}
    S20 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t: Junction | #(t.succs) > 1
}
    S21 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t : Track | (t in Junction) implies some(t.succs)
}
    S22 in valid iff {
	// Junctions are the tracks with more than one predecessor
    all t: Track | #(~succs.t) > 1 <=> t in Junction

}
    S23 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	all t: Junction | #(t.^succs) > 1
	//all t: Junction | all tr: Track and #(tr.^succs) > 1
}
    S24 in valid iff {
	// Junctions are the tracks with more than one predecessor
  all j : Junction | some succs.j and Entry in (((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))).j and Exit in j.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))

}
    S25 in valid iff {
	// Junctions are the tracks with more than one predecessor
  all j : Junction | some succs.j - j

}
    S26 in valid iff {
	// Junctions are the tracks with more than one predecessor
  // all j : Junction | some succs.j - j
  all j : Junction | all disj s1,s2 : Track | s1 in succs.j and s2 in succs.j

}
    S27 in valid iff {
	// Junctions are the tracks with more than one predecessor
  // all j : Junction | some succs.j - j
  some Junction and all j : Junction | some disj s1,s2 : Track | s1 in succs.j and s2 in succs.j

}
    S28 in valid iff {
	// Junctions are the tracks with more than one predecessor
  // all j : Junction | some succs.j - j
  (all t : Track - Junction, j : Junction | lone succs.t and some disj t1,t2 : Track | j in t1.succs and j in t2.succs) 

}
    S29 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t : Track | lone (succs.t) => t not in Junction
  	all t : Track | some(succs.t) => t in Junction
 }
    S30 in valid iff {
	// Junctions are the tracks with more than one predecessor{
 	all j: Junction | some j.succs & Junction
}
    S31 in valid iff {
	// Junctions are the tra^cks with more than one predecessor
	all t : Track | no(succs.t) => t in Junction
  	all t : Track | some(succs.t) => t  not in Junction
}
    S32 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t : Track | (t in Junction) <=> (some t1, t2 : Track | t1 != t2 and t in t1.^succs and t in t2.^succs)
}
    S33 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t : Track | (t in Junction) <=> (some t1, t2 : Track | t1 != t2 and t in t1.^succs and t in t2.^succs and t not in t.^succs)
}
    S34 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t : Track | (t in Junction) <=> (some t1, t2 : Track | t1 != t2 and t in t1.^succs and t in t2.^succs and t1 not in t2.^succs and t2 not in t1.^succs)
}
    S35 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t : Track | (t in Junction) implies (some t1, t2 : Track | t1 != t2 and t in t1.^succs and t in t2.^succs and t1 not in t2.^succs and t2 not in t1.^succs)
}
    S36 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t : Track | (t in Junction) implies (some t1, t2 : Track | t in t1.^succs and t in t2.^succs and t1 not in t2.^succs and t2 not in t1.^succs)
}
    S37 in valid iff {
	// Junctions are the tracks with more than one predecessor
	not ( lone ( ^(succs).Junction) )
}
    S38 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t: Track | some t2: Track | some t3: Track | t in Junction iff t in t2.^succs and t2 != t3 and t in t3.^succs
}
    S39 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all j : Junction| not ( one ( ^(succs).j) )
}
    S40 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all j: Junction | #(succs.j) > 1 and no j & succs.j
}
    S41 in valid iff {
	// Junctions are the tracks with more than one predecessor
	(all t: Track - Entry| lone succs.t) and all j : Junction | some disj t1, t2 : Track | j in t1.succs and j in t2.succs
}
    S42 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t: Track | some ts: Track-t | t in Junction iff ts in t.^succs
}
    S43 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all x: Track | x in Junction iff (all disj y, z: Track | y in succs.x and z in succs.x)
}
    S44 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t: Track | some t2: Track | some t3: Track | t in Junction iff t != t2 and t in t2.^succs and t != t3 and t in t3.^succs and t2 != t3
}
    S45 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t:Track | some disj t1,t2:Track | t in Junction iff t1!=t and t in t1.^succs and t2!=t and t in t2.^succs
}
    S46 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t: Track | some t2: Track | one t3: Track | t in Junction iff t in t2.^succs and t in t3.^succs and t2 != t3
}
    S47 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	some succs.Junction
  	

}
    S48 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	some succs.Junction
  	all t: Track | some succs.t implies t in Junction
  
  	

}
    S49 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	some succs.Junction
  	all t: Track | (some succs.t and succs.t!= t )implies t in Junction
  
  	

}
    S50 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	some succs.Junction
  	all t: Track | (some succs.t and t not in succs.t) implies t in Junction
  
  	

}
    S51 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	some succs.Junction
  	all t: Track | #succs.t > 1 implies t in Junction
  
  	

}
    S52 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t:Track | t in Junction iff some t1,t2:Track | t1 in t.^succs and t2 in t.^succs and t1!=t2 
}
    S53 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t: Track | (t in Junction) implies some(succs.t) and t not in ^succs.t
}
    S54 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t: Track | (t in Junction) implies some(succs.t)
  	all t: Track | t not in t.^succs
}
    S55 in valid iff {
	// Junctions are the tracks with more than one predecessor
    all t: Track | #(t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))) > 1 <=> t in Junction

}
    S56 in valid iff {
	// Junctions are the tracks with more than one predecessor
  all t:Track | t in Junction iff t not in Entry or t not in Exit

}
    S57 in valid iff {
	// Junctions are the tracks with more than one predecessor
  all t:Track | t in Junction iff t in Track.^succs and t not in Exit


}
    S58 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t : Track | some j1, j2 : Track | t in Junction iff j2 in j1.succs and t in j2.succs and t != j1 and t != j2 
}
    S59 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t:Track | t in Junction iff some t1,t2:Track | t1!=t and t in t1.^succs and t2!=t and t in t2.^succs and t1!=t2 
}
    S60 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t:Track | some disj t1,t2:Track | t in Junction iff t in t1.^succs and t2!=t1 and t in t2.^succs
}
    S61 in valid iff {
	// Junctions are the tracks with more than one predecessor
  all t : Track | (lone t1 : Track | t in t1.succs) iff t in Junction

}
    S62 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t : Track-Entry-Exit | some(succs.t) and t not in t.^succs
}
    S63 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all j : Junction | all disj t1, t2 : Track | (j in t1.succs) and (j in t2.succs)
  	all j : Track - Junction | lone(j.succs)
}
    S64 in valid iff {
	// Junctions are the tracks with more than one predecessor
  all t: Track | t in Junction iff some( succs.t + t.succs)

}
    S65 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	all t : Track | t in Junction iff t in Track.succs.succs
}
    S66 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all j: Junction | some t: Track | j in t.succs.succs
}
    S67 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	all t: Track | t in Junction => some t2: Track | t in t2.succs.succs and t != t2
}
    S68 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all j:Junction | some t:Track - j | j in t.succs and some t2:Track | t in t2.succs
}
    S69 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	all t: Track | t in Junction => some t2: Track | t in t2.succs and some t3: t2.succs | t in t3.succs
}
    S70 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	all t: Track | t in Junction => one e: Entry | t in e.succs.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))
}
    S71 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	all t: Track | t in Junction <=> some (succs.succs.t - t)
}
    S72 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	all disj t1, t2: Track | t1 in Junction <=> some t3: t2.succs | t1 in t3.succs
}
    S73 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	all disj t1, t2: Track | t1 in Junction => some t3: t2.succs | t1 in t3.succs
}
    S74 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t : Track | t in Junction <=> some (Track.^succs - t)
}
    S75 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t : Junction | some (Track.succs - t)
}
    S76 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t : Track | no succs.succs.t implies t in Junction
  	all e : Entry | no succs.succs.e
}
    S77 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t : Track | some (succs.t-t) implies t in Junction
  	all e : Junction | some succs.e
}
    S78 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t : Track | t in Junction iff some succs.t-t
}
    S79 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	no Junction
	all t : Track | some (succs.succs.t-t) implies t in Junction
  	all e : Junction | some (succs.succs.e-e)
}
    S80 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	all disj t1,t2 : Track | some (t1.succs&t2.succs) implies t1.succs in Junction
  	//all e : Junction | some (succs.succs.e-e)
}
    S81 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	all disj t1,t2 : Track | some (t1.succs&t2.succs) iff (t1.succs&t2.succs) in Junction
}
    S82 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	all j : Junction | some disj t1,t2 : Track | t1+t2 = succs.j 
}
    S83 in valid iff {
	// Junctions are the tracks with more than one predecessor
    all disj t1,t2 : Track | (t1.succs&t2.succs) in Junction
  	all j : Junction | some disj t1,t2 : Track | t1+t2 = succs.j 
}
    S84 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	some disj t1,t2 : Track | all j: Junction | t1+t2 in succs.j
  	all disj t1,t2 : Track | (t1.succs&t2.succs) in Junction
}
    S85 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t : Track | t in Junction implies some t.succs.succs
}
    S86 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	all j : Junction | some j.~succs.~succs && not (j in j.~succs)
}
    S87 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	all j : Junction | (j.~succs = j.~succs - j) && not (one j.~succs)
}
    S88 in valid iff {
	// Junctions are the tracks with more than one predecessor
  
  	all t: Track | t not in t.succs
  	all e: Junction | some t1,t2: Track | e in t1.succs and e in t2.succs and 		not(t1 = t2)
}
    S89 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all disj p1, p2, j : Track | j in p1.^succs and j in p2.^succs implies j in Junction
}
    S90 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all j : Junction | some disj p1, p2 : Track | j not in j.^succs and j in p1.succs & p2.succs
}
    S91 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all j : Junction | some p1, p2 : Track | p1 = j and p2 != j and j in p1.succs and j in p2.succs
}
    S92 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all j : Junction | some disj t,t2 : Track | j in t.succs&t2.succs
  	all disj t,t2,j : Track | j in t.succs&t2.succs implies j in Junction
}
    S93 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	no t : Track | t in t.^succs
	all j : Junction | some disj t,t2 : Track | j in t.succs&t2.succs
  	//all disj t,t2,j : Track | j in t.succs&t2.succs implies j in Junction
}
    S94 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	all j : Junction | some j.succs
	all t : Track | some t.succs implies t in Junction
}
    S95 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t:Track | #(succs.t)>2 implies t in Junction
}
    S96 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t1, t2, t3: Track | t2 != t3 and t2 in t1.succs and t3 in t1.succs implies t1 in Junction
}
    S97 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	#succs.Junction > 1
	all t : Track | #succs.t > 1 implies t in Junction
}
    S98 in valid iff {
	// Junctions are the tracks with more than one predecessor
  
  all j : Junction | (some t:Track - Junction | t->j in succs) 

}
    S99 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t : Track | t in Junction iff some succs.t and t not in ^succs.t
}
    S100 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t : Track | some t.succs implies t in Junction
}
    S101 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	some Junction.succs
	all t : Track | some t.succs implies t in Junction
}
    S102 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	all t: Track | all t2,t3: Track| t in Junction iff 
  	(t in t2.succs and t in t3.succs)

}
    S103 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	all t: Track | t in Junction iff Track.succs.succs != none

}
    S104 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	all t: Track | some disj t1,t2: Track | t in Junction iff (t1 in t2.succs and t in t1.succs and (t!=t1 or t!=t2))

}
    S105 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	all t: Track | some disj t1,t2: Track | t in Junction iff (t1 in t2.succs and t in t1.succs and t!=t1 and t!=t2)

}
    S106 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	all j : Junction | some succs.j and j not in succs.j

}
    S107 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all j:Junction | some t1,t2:Track | t1.succs = t2 and t2.succs = j
}
    S108 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all j:Junction | some t1,t2:Track | t1 != t2 and t2 != j and t1.succs = t2 and t2.succs = j
}
    S109 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t : Track | lone (succs.t) implies t not in Junction
  	all t : Junction | some t1, t2 : Track | t1 in t.^succs and t2 in t.^succs  
}
    S110 in valid iff {
	// Junctions are the tracks with more than one predecessor
  all t: Track | t in Junction iff some t1,t2: Track | t1 != t2 and t2 in t1.succs and t in t2.succs

}
    S111 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all disj j, t : Track | j in t.succs and j in (Track - j).succs implies j in Junction
}
    S112 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all disj j, t : Track | j in t.succs and j in (Track - j).succs implies j in Junction
  	
  	all j : Junction, t : Track | j in t.succs and j in (Track - j).succs 
}
    S113 in valid iff {
	// Junctions are the tracks with more than one predecessor
	//all disj j, t : Track | j in t.succs and j in (Track - j).succs implies j in Junction
  	
  	all j : Junction, t : Track | j in t.succs implies j in (Track - j).succs 
}
    S114 in valid iff {
	// Junctions are the tracks with more than one predecessor
	no e : Track-Entry-Junction | #e.~succs = 1
  	all e : Entry | #e.~succs = 0
  	all j : Junction | #j.succs > 1
}
    S115 in valid iff {
	// Junctions are the tracks with more than one predecessor
	no e : Track-Entry-Junction | #e.~succs = 1
  	all e : Entry | #e.~succs = 0
  	all j : Junction | #j.~succs > 1
}
    S116 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all e : Track-Entry-Junction | #e.~succs = 1
  	all e : Entry | #e.~succs = 0
  	all j : Junction | #j.succs > 1
}
    S117 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t1,t2,t3: Track | (t2 in Junction) iff (t1.succs = t2) and (t2.succs=t3)
	
}
    S118 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all disj t1,t2,t3: Track | (t2 in Junction) iff (t1.succs = t2) and (t2.succs=t3) 
	
}
    S119 in valid iff {
	// Junctions are the tracks with more than one predecessor
  all e:Exit | one succs.e

}
    S120 in valid iff {
	// Junctions are the tracks with more than one predecessor
  all t:Track | t in Exit implies lone succs.t  

}
    S121 in valid iff {
	// Junctions are the tracks with more than one predecessor
  all t:Track| t not in Junction implies lone succs.t
  all j:Junction | some succs.j
}
    S122 in valid iff {
	// Junctions are the tracks with more than one predecessor
  all t:Track| t not in Junction implies lone succs.t
  all j:Junction | some succs.j - j
}
    S123 in valid iff {
	// Junctions are the tracks with more than one predecessor
  all t:Track| t not in Junction implies lone succs.t
  all j:Junction | some succs.j -j.^(succs)
}
    S124 in valid iff {
	// Junctions are the tracks with more than one predecessor
  	/*all j:Track | j in Junction iff some disj t1,t2:Track | j in t1.succs and j in t2.succs*/
  	all j:Track | j in Junction iff 
  			let n = {t:Track | j in t.succs} | #n>2
}
    S125 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t:Track | t in Junction iff (some t1,t2:Track|t1.succs=t and t2.succs=t)
}
    S126 in valid iff {
	// Junctions are the tracks with more than one predecessor
//	all t:Track | t in Junction iff #(t.~succs)>1
  	all t:Track | t in Junction iff (some disj t1,t2:Track | t1.succs=t and t2.succs=t)
}
    S127 in valid iff {
	// Junctions are the tracks with more than one predecessor
//	all t:Track | t in Junction iff #(t.~succs)>1
  	all disj t1,t2,t3:Track |(t1 in Junction iff t2.succs=t1 and t3.succs=t1)
}
    S128 in valid iff {
	// Junctions are the tracks with more than one predecessor
//	all t:Track | t in Junction iff #(t.~succs)>1
  	all t:Track | some t1:Track | t in Junction iff t1.succs=t
}
    S129 in valid iff {
	// Junctions are the tracks with more than one predecessor
	#succs.Junction > 1
}
    S130 in valid iff {
	// Junctions are the tracks with more than one predecessor
	#succs.Track > 1
}
    S131 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t:Track | lone succs.t implies t in Junction
}
    S132 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t: Junction | some t.succs
  	and
  	all t: Track | some t.succs implies t in Junction
}
    S133 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t: Junction | some t.~succs and not one t.~succs
  	and
  	all t: Track | (some t.~succs and not one t.~succs) implies t in Junction
}
    S134 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t1, t2, t3: Track | (t1 != t2 and t1 != t3 and t2 != t3 and t2 in t1.succs and t3 in t1.succs) implies t1 in Junction
}
    S135 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t : Track | t in Junction <=> some t.succs.succs
}
    S136 in valid iff {
	// Junctions are the tracks with more than one predecessor
	all t : Track | t in Junction <=> some t.succs.succs and t.succs.succs != t
}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, S74, S75, S76, S77, S78, S79, S80, S81, S82, S83, S84, S85, S86, S87, S88, S89, S90, S91, S92, S93, S94, S95, S96, S97, S98, S99, S100, S101, S102, S103, S104, S105, S106, S107, S108, S109, S110, S111, S112, S113, S114, S115, S116, S117, S118, S119, S120, S121, S122, S123, S124, S125, S126, S127, S128, S129, S130, S131, S132, S133, S134, S135, S136 extends Formula {}

run {
    #valid.Oracle = 1
    #(Instance - valid.Oracle) = 1
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 8 Atom, exactly 4 TrackAtom, exactly 4 SignalAtom,
       exactly 2 Instance, 6 Int
