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
    // Earlier requirement 4, required in every Instance.
{
	// Junctions are the tracks with more than one predecessor
	all t: Track | #(succs.t) > 1 <=> t in Junction
}
    // Earlier requirement 5, required in every Instance.
{
	// Entry tracks must have a speed signal
  	all t:Entry | some (t.signals & Speed)  

}
    // Earlier requirement 6, required in every Instance.
{
	// The station has no cycles
	all t: Track | t not in t.^succs

}
    // Earlier requirement 7, required in every Instance.
{
	// It should be possible to reach every exit from every entry
  	all ex: Exit | all en: Entry | ex in en.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))

}
    Oracle in valid iff {
	// Tracks not followed by junctions do not have semaphores
  	all t : Track | no (Junction&t.succs) implies no (Semaphore&t.signals)

}
    S1 in valid iff {
	// Tracks not followed by junctions do not have semaphores

}
    S2 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | t.succs not in Junction => no (Semaphore & t.signals)
}
    S3 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | t.succs not in Junction <=> no (t.signals & Semaphore)
}
    S4 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  	all t: Track | (all s: Semaphore | s in t.signals) implies (t.succs in Junction)

}
    S5 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  	all t : Track | Junction not in t.succs implies Semaphore not in t.signals

}
    S6 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track | 
  		no j: Junction | j in t.succs implies no s: Semaphore | s in t.signals
}
    S7 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  	all t:Track | all t1: t.succs | t1 in Junction implies some (t1.signals & Semaphore) 

}
    S8 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track |  no t.signals & Semaphore => no Junction & t.succs
}
    S9 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  	// Tracks followed by junctions do have semaphores
	
  all t : Track| t.succs != none and some(t.succs & Junction) implies no(t.signals & Semaphore)
}
    S10 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | t.succs not in Junction => t.signals not in Semaphore
}
    S11 in valid iff {
    // Tracks not followed by junctions do not have semaphores
      all t:Track | all t1:t.succs | not t1 in Junction implies some (t1.signals & Semaphore)
  //all t:Track | all t1:t.succs | 
  	

}
    S12 in valid iff {
    // Tracks not followed by junctions do not have semaphores
      all t:Track | all t1:t.succs | t1 not in Junction implies no (t1.signals & Semaphore)
  //all t:Track | all t1:t.succs | 
  	

}
    S13 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | t.succs in Junction => t.signals not in Semaphore
}
    S14 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Entry | t.succs not in Junction => no (Semaphore & t.signals)
}
    S15 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Entry | no t.succs & Junction => no (Semaphore & t.signals)
}
    S16 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t:Track|all j :Junction| j not in t.succs implies no s:Semaphore| s in t.signals
}
    S17 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  all t : Track | no (succs.t & Junction) implies no (Semaphore & t.signals)
  
  

}
    S18 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  all t : Track | no (succs.t & Junction) iff no (Semaphore & t.signals)
  
  

}
    S19 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : (Track-Junction).succs | no t.signals & Semaphore
}
    S20 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | t.succs not in Junction implies no t.signals
}
    S21 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | t.succs not in Junction iff no t.signals
}
    S22 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | t.^succs not in Junction iff no t.signals
}
    S23 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) not in Junction iff no t.signals
}
    S24 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | t.succs not in Junction iff (not t.signals in Semaphore)
}
    S25 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all track: Track | Junction in track.succs implies all signal: track.signals | signal not in Semaphore
}
    S26 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track, s: Semaphore | t.^succs not in Junction implies s not in t.signals
}
    S27 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track | no s: Semaphore | t.succs not in Junction implies s not in t.signals
}
    S28 in valid iff {
    // Tracks not followed by junctions do not have semaphores
    all t: Track - Junction | no t.signals & Semaphore
}
    S29 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track, s: Semaphore | t.^succs not in Junction implies t.signals not in Semaphore
}
    S30 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track | t.^succs not in Junction implies t.signals not in Semaphore
}
    S31 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track, s: Semaphore | t not in Junction or t.^succs not in Junction implies s not in t.signals
}
    S32 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track, j: Junction|
  		j not in t.^succs implies (all s: t.signals | s not in Semaphore)
}
    S33 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track, s: Semaphore | t.succs not in Junction implies t.signals not in Semaphore
}
    S34 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track | t not in Junction and t.succs not in Junction implies t.signals not in Semaphore
}
    S35 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track, j: Junction | t.succs != j implies t.signals not in Semaphore
}
    S36 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track, j: Junction | t.^succs not in Junction implies t.signals not in Semaphore
}
    S37 in valid iff {
	// Tracks not followed by junctions do not have semaphores
     all t: Track, j: Junction | no s: Semaphore | t in t.^succs and j in t.^succs implies s not in j.signals

}
    S38 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: (Track-Entry-Exit) | (t.succs not in Junction) implies no(t.signals & Semaphore)
}
    S39 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track | (t.succs not in Junction) or no(t.succs) implies no(t.signals & Semaphore)
}
    S40 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track | (t.succs not in Junction) implies no(t.signals & Semaphore)
	all t: Track | no(t.succs) implies no(t.signals & Semaphore)
}
    S41 in valid iff {
	// Tracks not followed by junctions do not have semaphores
    all t: Track | no(t.succs & Junction) <=> no(t.signals & Semaphore)
}
    S42 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t:Track|all j :Junction| j not in t.succs iff no s:Semaphore| s in t.signals
}
    S43 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  all t : Track, j : Junction | t not in Junction and j not in t.^succs implies all s : Semaphore | s not in t.signals
}
    S44 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  all t : Track | t not in Junction and no t.^succs & Junction implies no s : Semaphore | s in t.signals
}
    S45 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | t not in Junction and no t.succs & Junction implies no s : Semaphore | s in t.signals
}
    S46 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track | no t.succs & Junction implies t.signals not in Semaphore
}
    S47 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  	all t: Track | ((no t2: Track | t2 in t.succs) or (no j: Junction | j in t.succs)) => no s: Semaphore | s not in t.signals
}
    S48 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t:Track | no t.succs & Junction implies some t.signals & Semaphore
}
    S49 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  all t : Track | Junction not in t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) implies no(t.signals & Semaphore)

}
    S50 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  all t : Track | (Junction not in t.succs or t in Entry and t in Exit) implies no(t.signals & Semaphore)

}
    S51 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  	all disj t1, t2 : Track | t2 in t1.succs and t2 not in Junction implies all s : Signal | s in Semaphore and s not in t1.signals
  
   // all t : Track | no (t.succs & Junction) implies no (Semaphore & t.signals)
}
    S52 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  	all disj t1, t2 : Track | t2 in t1.succs and t2 not in Junction implies some s : Signal | s in Semaphore and s not in t1.signals
  
   all t : Track | no (t.succs & Junction) implies no (Semaphore & t.signals)
}
    S53 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  	all disj t1, t2 : Track | t2 in t1.succs and t2 not in Junction implies no s : Signal | s in Semaphore and s not in t1.signals
  
   all t : Track | no (t.succs & Junction) implies no (Semaphore & t.signals)
}
    S54 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | t.succs not in Junction iff Semaphore not in t.signals
}
    S55 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t:Track|all j:Junction| all s:Semaphore | j not in t.^succs => s not in t.succs.signals
}
    S56 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  	all t: Track | no j: Junction | (j in t.succs or no t.succs) => no s: Semaphore | s in t.signals
}
    S57 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t:Track | some j:Junction | j not in t.succs => (no s : Semaphore | s in t.signals)
}
    S58 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | t.succs in Junction implies one (t.signals & Semaphore)
}
    S59 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | t.succs in Junction implies lone (t.signals & Semaphore)
}
    S60 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  	all t : Track, j : Junction | t.succs != j => no s : Semaphore | s in t.signals

}
    S61 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  	all t : Track, j : Junction | no t.succs & Junction => no s : Semaphore | s in t.signals

}
    S62 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  	//all t : Track | no t.succs & Junction => no s : Semaphore | s in t.signals
	all t : Track, j : Junction | t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) != j => no s : Semaphore | s in t.signals
}
    S63 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  	//all t : Track | no t.succs & Junction => no s : Semaphore | s in t.signals
	all t : Track, j : Junction, suc : t.succs | suc != j => no s : Semaphore | s in t.signals
}
    S64 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  all t: Track | no Junction & t.^succs => no t.signals & Semaphore

}
    S65 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  all t: Track | no Junction & t.^succs <=> no t.signals & Semaphore

}
    S66 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track |  no t.signals & Semaphore => no Junction & t.^succs
}
    S67 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  all t: Track | some t.signals & Semaphore => no Junction & t.^succs

}
    S68 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track | Junction not in t.^succs => Semaphore not in t.signals
}
    S69 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track | Junction not in t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) => Semaphore not in t.signals
}
    S70 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track | Junction in t.succs => Semaphore in t.signals
}
    S71 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track | {
      Junction in t.succs => Semaphore in t.signals
      Junction not in t.succs => Semaphore not in t.signals
    }
}
    S72 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track | {
      Junction in t.^succs => Semaphore in t.signals
      Junction not in t.^succs => Semaphore not in t.signals
    }
}
    S73 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track, j: Junction {
      //j in t.succs => Semaphore in t.signals
      //j not in t.succs => Semaphore not in t.signals
      t not in Junction.~succs => Semaphore not in t.signals
    }
}
    S74 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track | some j: Junction | {
      j not in t.succs => Semaphore not in t.signals
  	}
}
    S75 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track | some j: Junction | no s: Semaphore {
      j not in t.succs => s in t.signals
  	}
}
    S76 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track | Junction in t.succs implies Semaphore not in t.signals
}
    S77 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track, j: Junction|
  		j not in t.^succs implies (some s: t.signals | s not in Semaphore)
}
    S78 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track, j: Junction|
  		t not in Entry and t not in Exit and j not in t.^succs implies (all s: t.signals | s not in Semaphore)
}
    S79 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | no Semaphore & t.signals iff t.succs in Junction
}
    S80 in valid iff {
	// Tracks not followed by junctions do not have semaphores

  all t : Track | t.succs in Junction iff t.signals not in Semaphore
}
    S81 in valid iff {
	// Tracks not followed by junctions do not have semaphores

  all t : Track - Junction, s:Signal | t in Track.^succs implies Semaphore not in (Track - Junction).signals
}
    S82 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : succs.Track - succs.Junction | no t.signals & Semaphore 
}
    S83 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | t in Junction implies t.succs.signals in Semaphore
}
    S84 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	
  all t : Track |(Semaphore & t.signals) = none iff Junction not in t.succs 
}
    S85 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	
  all t : Track |(t.succs & Junction) = none iff Semaphore not in t.signals 
}
    S86 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t:Track, j:Junction| some s:t.signals | j in t.succs implies s in Semaphore
  
}
    S87 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t:Track, j:Junction| some s:t.signals | j in t.^succs implies s in Semaphore
  
}
    S88 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t:Track | some s:t.signals, j:Junction | j in t.^succs implies s in Semaphore
  
}
    S89 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t:Track | some s:t.signals, j:Junction | j not in t.^succs implies s not in Semaphore
  
}
    S90 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t:Track, j:Junction  | some s:t.signals| j not in t.^succs implies s not in Semaphore
  
}
    S91 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t:Track | some s:t.signals| t.^succs not in Junction implies s not in Semaphore
  
}
    S92 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t:Track | all s:t.signals| t.^succs not in Junction and t not in Junction implies s not in Semaphore
  
}
    S93 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t:Track | all s:t.signals| t.succs not in Junction and t not in Junction implies s not in Semaphore
  
}
    S94 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t:Track | all s:t.signals| t.succs not in Junction or t not in Junction implies s not in Semaphore
  
}
    S95 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t:Track | t.^succs not in Junction implies t.signals not in Semaphore
  all t:Track | no t.succs implies t.signals not in Semaphore
  
}
    S96 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	//all t:Track | t.^succs not in Junction implies t.signals not in Semaphore
  	all t:Track | no t.succs implies t.signals not in Semaphore
  
}
    S97 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t:Track | t.^succs not in Junction implies no t.signals & Semaphore

  	all t:Track | no t.succs implies no t.signals & Semaphore
  
}
    S98 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t:Track | t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) not in Junction implies no t.signals & Semaphore

  	all t:Track | no t.succs implies no t.signals & Semaphore
  
}
    S99 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t:Track | t.^succs not in Junction implies no t.signals & Semaphore

  	all t:Track | no t.succs implies no t.signals & Semaphore
  
  	all t:Track | some s:t.signals | some (t.^succs & Junction) implies s in Semaphore
  
}
    S100 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track | one j: Junction | j not in t.succs implies (Semaphore not in t.signals)
}
    S101 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  all x: Track | Junction in x.succs iff x.signals & Semaphore = none 

}
    S102 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track - Junction | not t.signals in Semaphore
}
    S103 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | t.succs not in Junction implies no s : t.signals | s not in Semaphore
}
    S104 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | no j : t.succs | j in Junction implies no t.signals & Semaphore
}
    S105 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | no j : t.succs | no s : t.signals| j in Junction implies s in Semaphore
}
    S106 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | no j : t.succs | j in Junction implies not t.signals in Semaphore
}
    S107 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all j : Junction | no j.signals
}
    S108 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | all j: Junction | all s: Signal | s in t.signals and j in t.succs implies t in Junction
}
    S109 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : succs.(Track-Junction) + Entry | no Semaphore & t.signals
}
    S110 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : succs.(Track-Junction) + Entry + Exit| no Semaphore & t.signals
}
    S111 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | no t.succs and t not in Junction implies no (t.signals & Semaphore)	
  //	all t : Track | no (t.succs & Junction) implies no (t.signals & Semaphore)	
}
    S112 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track |all j : Junction | no (t.succs) implies no (t.signals & Semaphore)	
 }
    S113 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | Semaphore in t.succs.signals implies some t.succs & Junction
}
    S114 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | Semaphore in t.succs.signals & t.signals implies some t.succs & Junction
}
    S115 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | Semaphore in t.succs.signals  implies t.succs in Junction
}
    S116 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track | some succs.t implies (succs.t not in Junction => no t.signals)
}
    S117 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track | some succs.t => (succs.t not in Junction and no t.signals)
}
    S118 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track | all j: Junction | (j not in succs.t) implies no (t.signals & Semaphore)
}
    S119 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  
  all t : Track | t.succs not in Junction implies (t.succs).signals not in Semaphore 

}
    S120 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  	all t: Track | ( no ( t.succs & Junction ) ) implies no t.signals

}
    S121 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track-Exit | Junction not in t.succs implies Semaphore not in t.signals
}
    S122 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  all t : Track | t.succs in Junction => Speed not in t.signals  

}
    S123 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  all t : Track | Junction in t.succs => Speed not in t.signals  

}
    S124 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  all t : Track | Junction not in t.succs => Speed not in t.signals  

}
    S125 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | some j: Junction |all s: Signal | j not in t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) and s in t.signals implies s not in Semaphore
  
  	//all t : Track | no (t.succs & Junction) implies no (t.signals & Semaphore)	

}
    S126 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  all t: Track | not Semaphore in t.signals iff not Junction in succs.t 
}
    S127 in valid iff {
	// Tracks not followed by junctions do not have semaphores
all disj x,y:Track-Exit, s:Semaphore | y in Junction and x->y in succs implies x->s in signals
}
    S128 in valid iff {
	// Tracks not followed by junctions do not have semaphores
all disj x,y:Track, s:Semaphore | y in Junction and x->y in succs implies x->s in signals else x->s not in signals
}
    S129 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t:Track | t.signals in Semaphore => t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) in Junction
}
    S130 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t:Track | t.signals in Semaphore => t in Junction.succs
}
    S131 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t:Track, j:Junction | t->j in succs => t.signals not in Semaphore
}
    S132 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  	no Junction => no Semaphore
	all t:Track, j:Junction | t->j in succs => t.signals not in Semaphore
}
    S133 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  	no Junction => no Semaphore
	all t:Track, j:Junction | j->t in succs => t.signals not in Semaphore
}
    S134 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  	no Junction => no Semaphore
	all t:Track-Junction, j:Junction | j->t in succs => t.signals not in Semaphore
}
    S135 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  	// no Junction => no Semaphore
	all t:Track-Junction, j:Junction | j->t in ^succs => t.signals not in Semaphore
}
    S136 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  	no Junction => no Semaphore
	all disj t:Track, j:Junction | j->t not in ^succs => t.signals not in Semaphore
}
    S137 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  	no Junction => no Semaphore
	all disj t:Track | t not in Junction.^succs => t.signals not in Semaphore
}
    S138 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t:Track| no t1:Track | t1 in Junction and t1 in t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) 
  				iff (Semaphore & t.signals = none)
}
    S139 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all j : Junction | some j.succs.signals & Semaphore
}
    S140 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | some t.succs & Junction implies some t.succs.signals & Semaphore  
}
    S141 in valid iff {
	// Tracks not followed by junctions do not have semaphores
  all t : Track, s : Semaphore | t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) not in Junction implies s not in t.signals

}
    S142 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t : Track | no (t.succs & Junction) implies no t.signals - Semaphore
}
    S143 in valid iff {
	// Tracks not followed by junctions do not have semaphores
	all t: Track | some j: Junction, s: Signal | j not in t.succs implies s not in t.signals
}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, S74, S75, S76, S77, S78, S79, S80, S81, S82, S83, S84, S85, S86, S87, S88, S89, S90, S91, S92, S93, S94, S95, S96, S97, S98, S99, S100, S101, S102, S103, S104, S105, S106, S107, S108, S109, S110, S111, S112, S113, S114, S115, S116, S117, S118, S119, S120, S121, S122, S123, S124, S125, S126, S127, S128, S129, S130, S131, S132, S133, S134, S135, S136, S137, S138, S139, S140, S141, S142, S143 extends Formula {}

run {
    #valid.Oracle = 1
    #(Instance - valid.Oracle) = 1
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 8 Atom, exactly 4 TrackAtom, exactly 4 SignalAtom,
       exactly 2 Instance, 6 Int
