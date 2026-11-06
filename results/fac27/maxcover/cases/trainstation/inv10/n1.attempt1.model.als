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
    // Earlier requirement 8, required in every Instance.
{
	// Tracks not followed by junctions do not have semaphores
  	all t : Track | no (Junction&t.succs) implies no (Semaphore&t.signals)

}
    Oracle in valid iff {
	// Every track before a junction has a semaphore
  	all t: Track | some (Junction&t.succs) implies some (Semaphore&t.signals)

}
    S1 in valid iff {
	// Every track before a junction has a semaphore

}
    S2 in valid iff {
	// Every track before a junction has a semaphore
	all t: Track | some j: Junction, s: Semaphore | (j in t.succs) implies (s in t.signals)
}
    S3 in valid iff {
	// Every track before a junction has a semaphore
	all t: Track | some j: Junction | one s: Semaphore | (j in t.succs) implies (s in t.signals)
}
    S4 in valid iff {
	// Every track before a junction has a semaphore
	all t: Track, j: Junction {
      j in t.succs => Semaphore in t.signals
    }
}
    S5 in valid iff {
	// Every track before a junction has a semaphore
  	all j: Junction| all jp: j.~succs| all t: Track| t in jp iff Semaphore in t.signals

}
    S6 in valid iff {
	// Every track before a junction has a semaphore
  	all t : Track | some(succs.t & Junction) implies some(t.signals & Semaphore)
  

}
    S7 in valid iff {
	// Every track before a junction has a semaphore
	all t : Track | some(t.succs & Junction) implies one(t.signals & Semaphore)
}
    S8 in valid iff {
	// Every track before a junction has a semaphore
	all t: Track | succs.t in Junction => some t.signals&Semaphore
}
    S9 in valid iff {
	// Every track before a junction has a semaphore
	all t: Track | (t.succs in Junction) => some (t.signals&Semaphore)
}
    S10 in valid iff {
	// Every track before a junction has a semaphore
	all j : Junction | all t : Track | j in t.^succs implies (some s:Semaphore | t->s in signals)
}
    S11 in valid iff {
	// Every track before a junction has a semaphore
  	all t: Track | some s: Semaphore | some t.succs and t.succs in Junction implies s in t.signals

}
    S12 in valid iff {
	// Every track before a junction has a semaphore
	all t:Track | t.succs = Junction implies some t.signals & Semaphore
}
    S13 in valid iff {
	// Every track before a junction has a semaphore
    all t: Track | Junction in succs.t implies some s:t.signals | s in Semaphore

}
    S14 in valid iff {
	// Every track before a junction has a semaphore
    all t : Track | t.succs in Junction implies t.signals in Semaphore
}
    S15 in valid iff {
	// Every track before a junction has a semaphore
	all t: Track | Junction in t.succs => one s: Semaphore | s in t.signals
}
    S16 in valid iff {
	// Every track before a junction has a semaphore
	all t: Track | one j: Junction| j in t.succs => one s: Semaphore | s in t.signals
}
    S17 in valid iff {
	// Every track before a junction has a semaphore
	all t: Track | one j: Junction| j in t.succs => some s: Semaphore | s in t.signals
}
    S18 in valid iff {
	// Every track before a junction has a semaphore
	all t: Track | some j: Junction | j in t.succs => some s: Semaphore | s in j.signals
}
    S19 in valid iff {
	// Every track before a junction has a semaphore
	all t : Track | t.succs in Junction implies lone (t.signals & Semaphore)
}
    S20 in valid iff {
	// Every track before a junction has a semaphore
	all t : Track, j : Junction | t.succs = j implies one s : Semaphore | s in t.signals
}
    S21 in valid iff {
	// Every track before a junction has a semaphore
	all t : Track, j : Junction | t.succs = j implies some s : Semaphore | s in t.signals
}
    S22 in valid iff {
	// Every track before a junction has a semaphore
	some succs.Junction.signals & Semaphore
}
    S23 in valid iff {
	// Every track before a junction has a semaphore
	some {t: Track | some t.succs & Junction }
}
    S24 in valid iff {
	// Every track before a junction has a semaphore
	all t: Track, s: Semaphore | some j: Junction | {
      j in t.succs => s in t.signals
  	}
}
    S25 in valid iff {
	// Every track before a junction has a semaphore
	all t: Track | some j: Junction | {
      j in t.succs => Semaphore in t.signals
  	}
}
    S26 in valid iff {
	// Every track before a junction has a semaphore
	all t: (Junction.succs) | Semaphore in t.signals
}
    S27 in valid iff {
	// Every track before a junction has a semaphore
  
  all j : Junction | succs.j.signals in Semaphore

}
    S28 in valid iff {
	// Every track before a junction has a semaphore
  
  all t : Track | (some succs.t & Junction) implies one Semaphore
  
}
    S29 in valid iff {
	// Every track before a junction has a semaphore
	all t: Track | all j: t.succs | some s: Semaphore | j in Junction implies s in t.signals
}
    S30 in valid iff {
	// Every track before a junction has a semaphore
	all t: Track | all j: t.succs | one s: Semaphore | j in Junction implies s in t.signals
}
    S31 in valid iff {
	// Every track before a junction has a semaphore
	all t: Track | all j: t.succs | some s: t.signals | j in Junction implies s in Semaphore
}
    S32 in valid iff {
	// Every track before a junction has a semaphore
	all t: Track | Junction in t.succs iff Semaphore in t.signals
}
    S33 in valid iff {
	// Every track before a junction has a semaphore
  all t : Entry |Junction in t.succs implies Semaphore in t.signals

}
    S34 in valid iff {
	// Every track before a junction has a semaphore
  all t: Entry | some t.succs & Junction implies some t.signals & Semaphore


}
    S35 in valid iff {
	// Every track before a junction has a semaphore
   all t1, t2: Track |
        t2 in Junction and t2 in t1.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) 
            implies all t: (t1.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) - t2.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))) | some t.signals & Semaphore
}
    S36 in valid iff {
	// Every track before a junction has a semaphore
   all t: Track | some  s: t.signals |
        some ( Junction & t.succs )
            implies s in Semaphore
  
  //all t: Track | some (t.succs & Junction) implies some s: Semaphore | s in t.signals
}
    S37 in valid iff {
	// Every track before a junction has a semaphore
  
  all t: Track | some s: Semaphore | some (t.succs & Junction) implies s in t.signals
}
    S38 in valid iff {
	// Every track before a junction has a semaphore
   all t: Track | some  s: t.signals |
        t in Junction and t in t.succs 
            implies s in Semaphore
  
  //all t: Track | some (t.succs & Junction) implies some s: Semaphore | s in t.signals
}
    S39 in valid iff {
	// Every track before a junction has a semaphore
	all t: Track | t in Junction.succs iff Semaphore in t.signals
}
    S40 in valid iff {
	// Every track before a junction has a semaphore
	one t: Track | t in Junction.succs implies Semaphore in t.signals
}
    S41 in valid iff {
	// Every track before a junction has a semaphore
	all t: Track |one s: Semaphore| t in Junction.succs implies s in t.signals
}
    S42 in valid iff {
	// Every track before a junction has a semaphore
	all t: Track |(all j: Junction | t in j.succs) implies (all s: Semaphore | s in t.signals)
}
    S43 in valid iff {
	// Every track before a junction has a semaphore

  //all x: Track |  not (Junction & x.succs = none) implies not (Semaphore & x.signals = none)
  
  all x: Junction | not (Semaphore & succs.x.signals = none)

}
    S44 in valid iff {
	// Every track before a junction has a semaphore
	all t: Track | some j: Junction | (j in t.succs) => (t.signals in Semaphore)
}
    S45 in valid iff {
	// Every track before a junction has a semaphore
  all t: Track | some s: Semaphore | Junction in succs.t implies s in t.signals
}
    S46 in valid iff {
	// Every track before a junction has a semaphore
  	all t : Track | some (succs.t & Junction) implies some (succs.t.signals & Semaphore) 
}
    S47 in valid iff {
	// Every track before a junction has a semaphore
	all t: Track, j: Junction | j in t.succs implies some s: Signal | s in t.signals

}
    S48 in valid iff {
	// Every track before a junction has a semaphore
	all t: Track, j: Junction | j in t.succs implies one s: Signal | s in t.signals

}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48 extends Formula {}

run {
    #valid.Oracle = 1
    #(Instance - valid.Oracle) = 1
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 8 Atom, exactly 4 TrackAtom, exactly 4 SignalAtom,
       exactly 2 Instance, 6 Int
