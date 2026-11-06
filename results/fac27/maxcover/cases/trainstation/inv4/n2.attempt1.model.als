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
    Oracle in valid iff {
	// Entry tracks are those without predecessors
	all t : Track | no succs.t iff t in Entry
}
    S1 in valid iff {
  // Entry tracks are those without predecessors
  all e: Entry | no succs.e
}
    S2 in valid iff {
	// Entry tracks are those without predecessors

}
    S3 in valid iff {
	// Entry tracks are those without predecessors
all t: Entry | no t.^succs
}
    S4 in valid iff {
	// Entry tracks are those without predecessors
	all e : Entry |all t :Track|e not in t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) 
}
    S5 in valid iff {
	// Entry tracks are those without predecessors
	all t: Track | t not in Track.succs
}
    S6 in valid iff {
	// Entry tracks are those without predecessors
	all t:Track | no succs.t implies t in Entry 
}
    S7 in valid iff {
	// Entry tracks are those without predecessors
	no t: Entry | t.succs & Entry != t.succs
}
    S8 in valid iff {
	// Entry tracks are those without predecessors
	all t: Entry | no pre: Track - Entry | t in pre.succs
}
    S9 in valid iff {
	// Entry tracks are those without predecessors
  all t: Track | t in Entry implies t in t.succs

}
    S10 in valid iff {
	// Entry tracks are those without predecessors
  all t: Track | t in Entry iff t in t.succs
  //no Entry.succs

}
    S11 in valid iff {
	// Entry tracks are those without predecessors
  all t: Track | t in Entry iff no t.succs
  //no Entry.succs

}
    S12 in valid iff {
	// Entry tracks are those without predecessors
  //all t: Track | t in Entry iff t.succs
  all t: Track| all e: Entry| t in Entry iff no e.succs

}
    S13 in valid iff {
	// Entry tracks are those without predecessors
  //all t: Track | t in Entry iff t.succs
  //all t: Track| all e: Entry| t in Entry implies no e.succs
  all t: Track| all e: Entry| no e.succs implies t in Entry

}
    S14 in valid iff {
	// Entry tracks are those without predecessors
  all t: Track | t in Entry implies t in t.succs or no t.succs
  //all t: Track| t in Entry implies no t.succs
  //all t: Track| all e: Entry| t in Entry implies no e.succs
  //all t: Track| all e: Entry| no e.succs implies t in Entry

}
    S15 in valid iff {
	// Entry tracks are those without predecessors
  all t: Track | t in Entry iff t in t.succs or no t.succs
  //all t: Track| t in Entry implies no t.succs
  //all t: Track| all e: Entry| t in Entry implies no e.succs
  //all t: Track| all e: Entry| no e.succs implies t in Entry

}
    S16 in valid iff {
	// Entry tracks are those without predecessors
  all t: Track | t in Entry iff (t in t.succs or no t.succs)
  //all t: Track| t in Entry implies no t.succs
  //all t: Track| all e: Entry| t in Entry implies no e.succs
  //all t: Track| all e: Entry| no e.succs implies t in Entry

}
    S17 in valid iff {
	// Entry tracks are those without predecessors
  //all t: Track | t in Entry iff (t in t.succs or no t.succs)
  all t: Track| t in Entry implies one t.succs
  //all t: Track| all e: Entry| t in Entry implies no e.succs
  //all t: Track| all e: Entry| no e.succs implies t in Entry

}
    S18 in valid iff {
	// Entry tracks are those without predecessors
  //all t: Track | t in Entry iff (t in t.succs or no t.succs)
  all t: Track| t in Entry implies lone t.succs
  //all t: Track| all e: Entry| t in Entry implies no e.succs
  //all t: Track| all e: Entry| no e.succs implies t in Entry

}
    S19 in valid iff {
	// Entry tracks are those without predecessors
  //all t: Track | t in Entry iff (t in t.succs or no t.succs)
  all t: Track| t in Entry iff lone t.succs
  //all t: Track| all e: Entry| t in Entry implies no e.succs
  //all t: Track| all e: Entry| no e.succs implies t in Entry

}
    S20 in valid iff {
	// Entry tracks are those without predecessors
  //all t: Track | t in Entry iff (t in t.succs or no t.succs)
  all t: Track| t in Entry implies lone t.succs
  no succs.Entry
  //all t: Track| all e: Entry| t in Entry implies no e.succs
  //all t: Track| all e: Entry| no e.succs implies t in Entry

}
    S21 in valid iff {
	// Entry tracks are those without predecessors
	all t:Track | some t.succs <=> t in Entry
}
    S22 in valid iff {
	// Entry tracks are those without predecessors
	all t: Entry | no succs.t
  	all t: (Track - Entry) | some t.succs
}
    S23 in valid iff {
	// Entry tracks are those without predecessors
  	all t : Track | all t1 : Track | t not in t1.succs => t in Entry
}
    S24 in valid iff {
	// Entry tracks are those without predecessors
  all t: Track, r: Track - t | t not in r.succs <=> t in Entry

}
    S25 in valid iff {
  
    all t : Track | no(succs.t) => t in Entry 
  	all t : Track | some(succs.t) => t not in Entry
	// Entry tracks are those without predecessors
	all disj t,t1 : Track | t in t1.succs => t not in Entry
  	all disj t,t1 : Track | t not in t1.succs => t in Entry
}
    S26 in valid iff {
	// Entry tracks are those without predecessors
	(all t: Track - Exit | some succs.t) and no succs.Entry
}
    S27 in valid iff {
	// Entry tracks are those without predecessors
	all t: Track | all succ: Track.^succs | t in Entry iff t not in succ
}
    S28 in valid iff {
	// Entry tracks are those without predecessors
	all t: Track | all succ: Track.^succs-t | t in Entry iff t not in succ
}
    S29 in valid iff {
	// Entry tracks are those without predecessors
	all t: Track | all succ: (Track-t).^succs | t in Entry iff t not in succ
}
    S30 in valid iff {
	// Entry tracks are those without predecessors
    all t: Entry | some t.succs

}
    S31 in valid iff {
	// Entry tracks are those without predecessors
  	all t: Track | no t2: Track | t in Entry iff t != t2 and t in t2.succs

}
    S32 in valid iff {
	// Entry tracks are those without predecessors
  	all t: Track, t2: Track | t != t2 and t not in t2.^succs implies t in Entry

}
    S33 in valid iff {
	// Entry tracks are those without predecessors
  	all t: Track, t2: Track | t != t2 and t not in t.^succs and t not in t2.^succs implies t in Entry

}
    S34 in valid iff {
	// Entry tracks are those without predecessors
  	all t: Track, t2: Track | t in Entry iff t not in t.^succs and t not in t2.^succs

}
    S35 in valid iff {
	// Entry tracks are those without predecessors
  	//all t: Track, t2: Track | t in Entry iff t not in t.^succs and t not in t2.^succs
	all e: Entry, t: Track | e not in t.^succs and e not in Exit and e not in Junction
}
    S36 in valid iff {
	// Entry tracks are those without predecessors
	all e : Entry, t : Track | e not in t.succs
  	all e : Entry, ex : Exit | e != ex
}
    S37 in valid iff {
	// Entry tracks are those without predecessors
  no Entry.succs 
  some succs.Entry

}
    S38 in valid iff {
	// Entry tracks are those without predecessors
  some Entry.succs 
  no succs.Entry

}
    S39 in valid iff {
	// Entry tracks are those without predecessors
   all t:Track | t in Entry iff t not in t.succs

}
    S40 in valid iff {
	// Entry tracks are those without predecessors
	all t: Track | (t not in t.^succs) <=> t in Entry
}
    S41 in valid iff {
	// Entry tracks are those without predecessors  
  	//all t: Track | t in Entry iff t not in Track.succs
  	
  	all t1: Track, t2: Track | t1 in Entry iff t1 not in t2.succs+t1.succs
  	
	//all t1: Track | t1 in Entry iff all t2: Track | t1 not in t2.succs
}
    S42 in valid iff {
	// Entry tracks are those without predecessors
  all t1,t2: Track | t1 != t2 and t1 in Entry implies t1 not in t2.succs

}
    S43 in valid iff {
	// Entry tracks are those without predecessors
	all t : Track | t in Entry implies no t.succs & Entry
}
    S44 in valid iff {
	// Entry tracks are those without predecessors
  	all t:Track | t = Entry iff #(succs.t) = 0

}
    S45 in valid iff {
	// Entry tracks are those without predecessors
	all t : Track | all t2 : Track-t | all t2 : t.succs| t in Entry implies (not t in Track.succs and not t in t2.succs)
}
    S46 in valid iff {
	// Entry tracks are those without predecessors
	all t : Track | t in Entry implies t = Track
}
    S47 in valid iff {
	// Entry tracks are those without predecessors
	all t : Track | all e : Entry | e in t implies e not in (t.succs + t.^succs)
}
    S48 in valid iff {
	// Entry tracks are those without predecessors
  	all disj t1, t2: Track | t1 not in t2.succs => t1 in Entry
}
    S49 in valid iff {
	// Entry tracks are those without predecessors
	all t : Track | t in Entry <=> t.succs not in t
}
    S50 in valid iff {
	// Entry tracks are those without predecessors
  all e: Entry | no succs.e
  all t: Track | no succs.t implies Entry in t

}
    S51 in valid iff {
	// Entry tracks are those without predecessors
    all t: Entry | some p: Track | t in p.succs

}
    S52 in valid iff {
	// Entry tracks are those without predecessors
  Track.succs !in Entry
}
    S53 in valid iff {
	// Entry tracks are those without predecessors
	no t : Track | Entry in t.succs
}
    S54 in valid iff {
	// Entry tracks are those without predecessors
	all t,tr: Track | not tr in t.succs implies t in Entry
}
    S55 in valid iff {
	// Entry tracks are those without predecessors
  all e : Entry | (one t : Track | t->e in succs)
  

}
    S56 in valid iff {
	// Entry tracks are those without predecessors
  all t : Track - Entry | one t.succs
  

}
    S57 in valid iff {
	// Entry tracks are those without predecessors
	all t: Track | (#succs.t > 1) iff t in Entry
}
    S58 in valid iff {
	// Entry tracks are those without predecessors
  all t: Track | t in Entry iff t in (Track - t).succs

}
    S59 in valid iff {
	// Entry tracks are those without predecessors
  all t: Track | t in Entry iff  #(Track - t).succs > 0 

}
    S60 in valid iff {
	// Entry tracks are those without predecessors
	Entry.succs = Track - Entry
}
    S61 in valid iff {
	// Entry tracks are those without predecessors
  all t: Track | t in Entry iff  #(Track - t).succs = 0 

}
    S62 in valid iff {
	// Entry tracks are those without predecessors
  all t: Track | t in Entry iff t not in (Track - t).succs 

}
    S63 in valid iff {
	// Entry tracks are those without predecessors
  
    all en: Entry | no {t: Track | t.succs = en}

}
    S64 in valid iff {
	// Entry tracks are those without predecessors
  no e: Entry | e in e.~succs
}
    S65 in valid iff {
	// Entry tracks are those without predecessors
    // Todas as Tracks sao reachable from the Entry
   Track in Entry.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))

}
    S66 in valid iff {
	Entry not in Track.succs

}
    S67 in valid iff {
	// Entry tracks are those without predecessors
	//t' in t.~succs
	all t : Track |  t not in t.~succs implies t in Entry
}
    S68 in valid iff {
    // Entry tracks are those without predecessors
    all t: Track | t in Entry iff t in Track.succs

}
    S69 in valid iff {
	// Entry tracks are those without predecessors
  	no succs.Entry
  	some succs.(Track-Entry)

}
    S70 in valid iff {
	// Entry tracks are those without predecessors
  	no succs.Entry
  	some succs.(Track-Entry-Exit)

}
    S71 in valid iff {
	// Entry tracks are those without predecessors
	one Exit
  	all e: Entry | all t: Track | e not in t.succs
  	all t: Track - Exit | some t.succs

}
    S72 in valid iff {
	// Entry tracks are those without predecessors
	all e: Entry | no e.succs.succs
}
    S73 in valid iff {
	// Entry tracks are those without predecessors
	one e: Entry | no succs.e
}
    S74 in valid iff {
	// Entry tracks are those without predecessors
all disj t,e:Track-Exit | e in Entry implies e not in t.succs
}
    S75 in valid iff {
	// Entry tracks are those without predecessors
	all t : Track | no succs.t implies t in Entry
  	all t : Track | some (succs.t) implies t not in Exit
}
    S76 in valid iff {
	// Entry tracks are those without predecessors
  all t:Track | no t.succs implies t in Entry

}
    S77 in valid iff {
	// Entry tracks are those without predecessors
    some e:Entry| succs.e not in Exit
    

}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, S74, S75, S76, S77 extends Formula {}

run {
    #valid.Oracle = 2
    #(Instance - valid.Oracle) = 2
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 8 Atom, exactly 4 TrackAtom, exactly 4 SignalAtom,
       exactly 4 Instance, 6 Int
