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
    Oracle in valid iff {
	// Entry tracks must have a speed signal
  	all t:Entry | some (t.signals & Speed)  

}
    S1 in valid iff {
	// Entry tracks must have a speed signal
  	Speed in Entry.signals

}
    S2 in valid iff {
	// Entry tracks must have a speed signal
  	all e: Entry | Speed in e.signals

}
    S3 in valid iff {
	// Entry tracks must have a speed signal
	all e : Entry | some e.signals
}
    S4 in valid iff {
	// Entry tracks must have a speed signal
  	Entry = {x: Track | Track.signals in Speed}
}
    S5 in valid iff {
	// Entry tracks must have a speed signal
  	all entry: Entry | entry.signals in Speed

}
    S6 in valid iff {
	// Entry tracks must have a speed signal
//  all s:Speed, t:Track |  s in t.signals  implies t in Entry
//  all s:Speed, e: Entry, t:Track | s in e.signals implies t in Entry 
  //all s:Speed, t:Track | t in Entry implies s in t.*succs
  all t:Track| t in Entry implies t.signals in Signal
}
    S7 in valid iff {
	// Entry tracks must have a speed signal
  	all t:Track | some (t.signals&Speed)  

}
    S8 in valid iff {
	// Entry tracks must have a speed signal
  	all e: Entry | one s: Speed | s in e.signals 

}
    S9 in valid iff {
	// Entry tracks must have a speed signal
	(all t: Track| t in Entry and some t.signals)
}
    S10 in valid iff {
	// Entry tracks must have a speed signal
	(all t: Track| t in Entry iff some t.signals)
}
    S11 in valid iff {
	// Entry tracks must have a speed signal
	all e:Entry| some e.signals and e.signals in Speed 
}
    S12 in valid iff {
	// Entry tracks must have a speed signal
	all track: Entry | one track->Speed
}
    S13 in valid iff {
	// Entry tracks must have a speed signal
	all track: Entry | some track->Speed
}
    S14 in valid iff {
	// Entry tracks must have a speed signal
  	//all t: Entry | t.signals = Speed
  	signals in Entry -> Speed

}
    S15 in valid iff {
	// Entry tracks must have a speed signal
   all t : Track | one s : Speed | s in t.signals

}
    S16 in valid iff {
	// Entry tracks must have a speed signal
	all t : Entry | some t.signals & Entry
}
    S17 in valid iff {
	// Entry tracks must have a speed signal
	all t : Track | some s : t.signals |t in Entry implies s in Speed
}
    S18 in valid iff {
	// Entry tracks must have a speed signal
	all t:Track|all s:Signal| t in Entry => s in t.signals
}
    S19 in valid iff {
	// Entry tracks must have a speed signal
	all t:Track|one s:Signal| t in Entry => s in t.signals
}
    S20 in valid iff {
	// Entry tracks must have a speed signal
    signals in Entry -> one Speed
}
    S21 in valid iff {
	// Entry tracks must have a speed signal
  	all e : Entry | Speed in e.signals or Speed in e.^succs.signals

}
    S22 in valid iff {
	// Entry tracks must have a speed signal
  	all e : Entry | one s : Speed | s in e.signals or s in e.^succs.signals

}
    S23 in valid iff {
	// Entry tracks must have a speed signal
	all t : Entry | some t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)).signals & Speed
}
    S24 in valid iff {
	// Entry tracks must have a speed signal
  all t: Track | t in Entry implies (t.signals & Semaphore) != none
}
    S25 in valid iff {
	// Entry tracks must have a speed signal
	some Entry.signals & Speed
}
    S26 in valid iff {
	// Entry tracks must have a speed signal
  	all e : Entry | Signal in e.succs
}
    S27 in valid iff {
	// Entry tracks must have a speed signal
  	all e : Entry | some Speed and Speed in e.signals
}
    S28 in valid iff {
	// Entry tracks must have a speed signal
  	all e : Entry | one Speed and Speed in e.signals
}
    S29 in valid iff {
	// Entry tracks must have a speed signal
	all t : Track | t in Entry <=> some (t.signals & Speed)
}
    S30 in valid iff {
	// Entry tracks must have a speed signal
  	all t : Track | (some t.signals and t.signals in Speed)

}
    S31 in valid iff {
	// Entry tracks must have a speed signal
  all e : Entry | (one s : Signal | e->s in signals)

}
    S32 in valid iff {
	// Entry tracks must have a speed signal
	all t: Track | (Entry in t) iff Speed in t.signals
}
    S33 in valid iff {
	// Entry tracks must have a speed signal
  signals in Entry one -> Signal

}
    S34 in valid iff {
	// Entry tracks must have a speed signal
  	all t: Track | t in Entry iff Speed in t.signals 

}
    S35 in valid iff {
	// Entry tracks must have a speed signal
  	all t: Track | t in Entry and Speed in t.signals 

}
    S36 in valid iff {
	// Entry tracks must have a speed signal
  	all t: Track | one s: Speed |t in Entry implies s in t.signals

}
    S37 in valid iff {
	// Entry tracks must have a speed signal
  all x: Track | some s: Signal | s in x.signals 

}
    S38 in valid iff {
	// Entry tracks must have a speed signal
	all e : Entry | all s : e.signals | e in Speed 
}
    S39 in valid iff {
	// Entry tracks must have a speed signal
	all e: Entry | all s: Signal | s in e.signals and s in Speed
}
    S40 in valid iff {
	// Entry tracks must have a speed signal
	all t:Track | t in Entry implies no (Speed & t.signals)
}
    S41 in valid iff {
	// Entry tracks must have a speed signal
	all t : Entry | some t.^succs.signals & Speed
}
    S42 in valid iff {
	// Entry tracks must have a speed signal
  	all t : Track | (one t.signals and t.signals in Speed)

}
    S43 in valid iff {
	// Entry tracks must have a speed signal
  	all t : Track | one t.signals iff t.signals in Speed

}
    S44 in valid iff {
	// Entry tracks must have a speed signal
  	all t : Entry | one t.signals and t.signals in Speed

}
    S45 in valid iff {
	// Entry tracks must have a speed signal
	all t : Track | one s : Signal | s in t.signals implies (t in Entry)
}
    S46 in valid iff {
	// Entry tracks must have a speed signal
	all t : Track | one s : Signal | s in t.signals implies (t in Entry and s in Speed)
}
    S47 in valid iff {
	// Entry tracks must have a speed signal
  all e:Entry, s:Signal, t:Track | e in Track implies s in t.signals

}
    S48 in valid iff {
	// Entry tracks must have a speed signal
//  all s:Speed, t:Track |  s in t.signals  implies t in Entry
  all s:Speed, e: Entry, t:Track | s in e.signals implies t in Entry 

}
    S49 in valid iff {
	// Entry tracks must have a speed signal
//  all s:Speed, t:Track |  s in t.signals  implies t in Entry
//  all s:Speed, e: Entry, t:Track | s in e.signals implies t in Entry 
  all s:Speed, t:Track | t in Entry implies s in t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))

}
    S50 in valid iff {
	// Entry tracks must have a speed signal
//  all s:Speed, t:Track |  s in t.signals  implies t in Entry
//  all s:Speed, e: Entry, t:Track | s in e.signals implies t in Entry 
  //all s:Speed, t:Track | t in Entry implies s in t.*succs
  all t:Track| t in Entry iff t.signals in Signal

}
    S51 in valid iff {
	// Entry tracks must have a speed signal
//  all s:Speed, t:Track |  s in t.signals  implies t in Entry
//  all s:Speed, e: Entry, t:Track | s in e.signals implies t in Entry 
  //all s:Speed, t:Track | t in Entry implies s in t.*succs
  all t:Track, s: Signal| t in Entry implies (s in Speed or s in Semaphore)
}
    S52 in valid iff {
	// Entry tracks must have a speed signal
//  all s:Speed, t:Track |  s in t.signals  implies t in Entry
//  all s:Speed, e: Entry, t:Track | s in e.signals implies t in Entry 
  //all s:Speed, t:Track | t in Entry implies s in t.*succs
  all t:Track, s: Signal| t in Entry implies s in Speed
}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52 extends Formula {}

run {
    #valid.Oracle = 1
    #(Instance - valid.Oracle) = 1
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 8 Atom, exactly 4 TrackAtom, exactly 4 SignalAtom,
       exactly 2 Instance, 6 Int
