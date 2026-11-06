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
    Oracle in valid iff {
	// It should be possible to reach every exit from every entry
  	all ex: Exit | all en: Entry | ex in en.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))

}
    S1 in valid iff {
	// It should be possible to reach every exit from every entry
  	all ex: Exit | all en: Entry | ex in en.^succs

}
    S2 in valid iff {
	// It should be possible to reach every exit from every entry

}
    S3 in valid iff {
	// It should be possible to reach every exit from every entry
	all t,e,ex : Track | e in Entry and ex in Exit and e in t implies ex in t 
}
    S4 in valid iff {
	// It should be possible to reach every exit from every entry
  	all e:Entry | all ex:Exit | e in e.^(succs)

}
    S5 in valid iff {
	// It should be possible to reach every exit from every entry
  	all e:Entry | e in Exit or (all ex:Exit | ex in e.^(succs)) 

}
    S6 in valid iff {
	// It should be possible to reach every exit from every entry
  	all en: Entry, ex: Exit | ex in en.succs

}
    S7 in valid iff {
	// It should be possible to reach every exit from every entry
  	//all en: Entry, ex: Exit | ex in en.^succs
  	all ex : Exit | ex in Entry

}
    S8 in valid iff {
	// It should be possible to reach every exit from every entry
  	all en: Entry | some ex: Exit | ex in en.^succs

}
    S9 in valid iff {
	// It should be possible to reach every exit from every entry
  	all en: Entry | one ex: Exit | ex in en.^succs

}
    S10 in valid iff {
	// It should be possible to reach every exit from every entry
  	one en: Entry | all ex: Exit | ex in en.^succs

}
    S11 in valid iff {
	// It should be possible to reach every exit from every entry
  all disj t1,t2:Track | t1 in Entry and t2 in Exit implies t2 in t1.succs

}
    S12 in valid iff {
	// It should be possible to reach every exit from every entry
	all et: Entry | et.^succs = Exit
}
    S13 in valid iff {
	// It should be possible to reach every exit from every entry
  all e: Exit , t: Track - Exit | t in Entry <=> e in t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) 

}
    S14 in valid iff {
	// It should be possible to reach every exit from every entry
  all e: Exit , t: Track - Exit | t in Entry => e in t.succs 

}
    S15 in valid iff {
	// It should be possible to reach every exit from every entry
	all t : Track, e : Exit |
  		e in t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))
}
    S16 in valid iff {
	// It should be possible to reach every exit from every entry
	some exits: Exit | all entrys: Entry | exits in entrys.^succs
}
    S17 in valid iff {
	// It should be possible to reach every exit from every entry
  all e: Entry | some ex: Exit | ex in e.succs

}
    S18 in valid iff {
	// It should be possible to reach every exit from every entry
	all e1 : Entry | one e2 : Exit | e2 in e1.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))
}
    S19 in valid iff {
	// It should be possible to reach every exit from every entry
	Exit in Entry.succs
}
    S20 in valid iff {
	// It should be possible to reach every exit from every entry
  all ex: Exit, e: Entry | ex in e.succs iff (Exit not in Track and Entry not in Track)
}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20 extends Formula {}

run {
    #valid.Oracle = 1
    #(Instance - valid.Oracle) = 1
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 8 Atom, exactly 4 TrackAtom, exactly 4 SignalAtom,
       exactly 2 Instance, 6 Int
