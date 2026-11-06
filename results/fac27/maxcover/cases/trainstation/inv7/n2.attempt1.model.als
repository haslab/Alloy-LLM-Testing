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
    Oracle in valid iff {
	// The station has no cycles
	all t: Track | t not in t.^succs

}
    S1 in valid iff {
	// The station has no cycles
  	Track in Track.^succs

}
    S2 in valid iff {
	// The station has no cycles
	
}
    S3 in valid iff {
	// The station has no cycles
	all t1: Track, t2: Track | t2 not in t1.^succs
}
    S4 in valid iff {
	// The station has no cycles
  	all t:Track | t not in t.succs 

}
    S5 in valid iff {
	// The station has no cycles
  all t : Track | all t1 : Track | t1 in t.succs implies t not in t1.succs

}
    S6 in valid iff {
	// The station has no cycles
	all t : Track | t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) != t.succs
}
    S7 in valid iff {
	// The station has no cycles
	all t : Track | t not in t.succs
  	all t : Track | t in Entry.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))
}
    S8 in valid iff {
	// The station has no cycles
	all e: Entry | no e.succs
}
    S9 in valid iff {
	// The station has no cycles
  
  all en:Entry,ex:Exit| ex not in succs.en and en not in ex.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))

}
    S10 in valid iff {
	// The station has no cycles
  
  all en:Entry,ex:Exit| ex not in en.succs

}
    S11 in valid iff {
	// The station has no cycles
  
  all t:Track | Entry not in t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) 

}
    S12 in valid iff {
	// The station has no cycles
	no disj t1, t2 : Track | t1 in t2.succs
}
    S13 in valid iff {
	// The station has no cycles
	all disj t1, t2: Track | t1 in t2.succs implies (t1.succs & t2.succs) = none
}
    S14 in valid iff {
	// The station has no cycles
	all disj t1, t2: Track | t1 in t2.succs iff (t1.succs & t2.succs) = none
}
    S15 in valid iff {
	// The station has no cycles
	all t1, t2: Track | t1 in t2.succs implies (t1.succs & t2.succs) = none
}
    S16 in valid iff {
	// The station has no cycles
	all t1, t2: Track | t1 in t2.succs implies (t1.succs.succs & t2.succs) = none
}
    S17 in valid iff {
	// The station has no cycles
	all disj t1, t2 : Track | t1 not in t2.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) iff t2 in t1.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) 
}
    S18 in valid iff {
	// The station has no cycles
	no t : Track-Entry-Exit | t in t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))
}
    S19 in valid iff {
	// The station has no cycles
  	all e : Exit, en : Entry | (en.succs in e) and (succs.e in en)

}
    S20 in valid iff {
	// The station has no cycles
  all t1,t2: Track | t1!=t2 and t1 in t2.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) implies t2 not in t1.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))

}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20 extends Formula {}

run {
    #valid.Oracle = 2
    #(Instance - valid.Oracle) = 2
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 8 Atom, exactly 4 TrackAtom, exactly 4 SignalAtom,
       exactly 4 Instance, 6 Int
