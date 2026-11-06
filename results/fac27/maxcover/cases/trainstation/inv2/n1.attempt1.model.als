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
    Oracle in valid iff {
	// Signals belong to one track
  all s: Signal | one t: Track | s in t.signals
}
    S1 in valid iff {
	// Signals belong to one track

}
    S2 in valid iff {
	// Signals belong to one track
	signals in ( Track -> lone Signal)
}
    S3 in valid iff {
	// Signals belong to one track
	all t1, t2 : Track | all s : Signal | s in t1.signals and s in t2.signals implies t1=t2
}
    S4 in valid iff {
	// Signals belong to one track
	signals in ( Track lone-> some Signal)
}
    S5 in valid iff {
	// Signals belong to one track
	signals in ( Track one -> some Signal)
}
    S6 in valid iff {
	// Signals belong to one track
  all t : Track | no (t.signals & t.succs.signals)
}
    S7 in valid iff {
	// Signals belong to one track
  all t : Track | no (t.signals & t.^succs.signals)
}
    S8 in valid iff {
	// Signals belong to one track
	all s: Signal | one Track
}
    S9 in valid iff {
	// Signals belong to one track
	all s : Signal | s in Track.signals
}
    S10 in valid iff {
	// Signals belong to one track
	Signal = (this.@Track + this.@Signal + Int + String).signals
  	Track = signals.(this.@Track + this.@Signal + Int + String)
}
    S11 in valid iff {
	// Signals belong to one track
  	no {s: Signal | #signals.s = 2}

}
    S12 in valid iff {
	// Signals belong to one track
	all t: Track | one signals.t
}
    S13 in valid iff {
	// Signals belong to one track
	all t1: Track, t2: Track | some s: Signal | !(s in t1.signals && s in t2.signals)
}
    S14 in valid iff {
	// Signals belong to one track
	all s: Signal | one Track.signals
}
    S15 in valid iff {
	// Signals belong to one track
	one(signals.Signal)
}
    S16 in valid iff {
	// Signals belong to one track

#signals.Signal =1
  Signal in Track.signals

}
    S17 in valid iff {
	// Signals belong to one track

	#signals.Signal > 0 
	Signal in Track.signals

}
    S18 in valid iff {
	// Signals belong to one track
	all s : Signal | one t : Track | s in t
}
    S19 in valid iff {
	// Signals belong to one track

	#signals.Signal = 0 or #signals.Signal = 1
	Signal in Track.signals

}
    S20 in valid iff {
	// Signals belong to one track
  	all t1,t2 : Track, s : Signal | s in t1.signals implies s not in t2.signals

}
    S21 in valid iff {
	// Signals belong to one track
  	all t1,t2 : Track, s : Signal | (s in t1.signals or s in t1.^succs.signals) implies (s not in t2.signals or s not in t2.^succs.signals)
  	all s : Signal | some t : Track | s in t.signals

}
    S22 in valid iff {
	// Signals belong to one track
  	all t1,t2 : Track, s : Signal | (s in t1.signals or s in t1.^succs.signals) implies (s not in t2.signals or s not in t2.^succs.signals)
  	some s : Signal | some t : Track | s in t.signals

}
    S23 in valid iff {
	// Signals belong to one track
  	all t1,t2 : Track, s : Signal | s in t1.((^(signals)) + ((this.@Track + this.@Signal + Int + String) <: iden)) and s in t2.((^(signals)) + ((this.@Track + this.@Signal + Int + String) <: iden)) iff t1 = t2

}
    S24 in valid iff {
	// Signals belong to one track
  all s:Signal | some disj t1,t2:Track | s in t1.signals implies s not in t2.signals

}
    S25 in valid iff {
	// Signals belong to one track
  all t: Track | one t.signals

}
    S26 in valid iff {
	// Signals belong to one track
  all t : Track | lone sem : Semaphore, speed : Speed | sem+speed in t.signals
  

}
    S27 in valid iff {
	// Signals belong to one track
  all s : Signal | one t : Track | s = t.signals
  

}
    S28 in valid iff {
	// Signals belong to one track
  	one signals.((this.@Track + this.@Signal + Int + String) <: iden)

}
    S29 in valid iff {
	// Signals belong to one track
	some t : Track | all s : Signal | s in t.signals
}
    S30 in valid iff {
	// Signals belong to one track
	all t : Track | all s : Signal | s in t.signals
}
    S31 in valid iff {
	// Signals belong to one track
		one t: Track | all s:Signal | s in t.signals 

}
    S32 in valid iff {
	// Signals belong to one track
	all t: Track | t.signals not in t.succs.signals 
}
    S33 in valid iff {
	// Signals belong to one track
	all t: Track | t.signals not in t.^succs.signals 
}
    S34 in valid iff {
	// Signals belong to one track
  	all t : Track | some t.signals

}
    S35 in valid iff {
	// Signals belong to one track
  	one t: Track | all s: Signal | s = t.signals

}
    S36 in valid iff {
	// Signals belong to one track
  	one t: Track | all s: Signal | t.signals in s

}
    S37 in valid iff {
	// Signals belong to one track
  one s: Signal | s in Track.signals

}
    S38 in valid iff {
	// Signals belong to one track
    all s: Signal | one Track.succs


}
    S39 in valid iff {
	// Signals belong to one track
  all t: Track | t.signals not in (Track - t).signals 
}
    S40 in valid iff {
	// Signals belong to one track
  one t:Track | all s:t.signals | s in t

}
    S41 in valid iff {
	// Signals belong to one track
  one t:Track | all s:t.signals | s in t.signals

}
    S42 in valid iff {
	// Signals belong to one track
  all t:Track | all s: Signal | s in t.signals or s in t.^succs.signals

}
    S43 in valid iff {
	// Signals belong to one track
	all t: Track, s: Signal | no (Signal - Track.signals) and s in t.signals implies s not in ((Track - t) <: Track).signals
}
    S44 in valid iff {
	// Signals belong to one track
	no disj t1,t2:Track| t1.signals in t2.signals
}
    S45 in valid iff {
	// Signals belong to one track
  	no s:Signal| all t:Track| s not in t.signals
	no disj t1,t2:Track| t1.signals in t2.signals
}
    S46 in valid iff {
	// Signals belong to one track
  	all s:Signal| one t:Track| s in t.signals
	no disj t1,t2:Track| t1.signals in t2.signals
}
    S47 in valid iff {
	// Signals belong to one track
	one t : Track | Signal in  t
}
    S48 in valid iff {
	// Signals belong to one track
	one t:Track | one t.signals
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
