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
    Oracle in valid iff {
	// The station has at least one entry and one exit
	some Entry and some Exit
}
    S1 in valid iff {
	// The station has at least one entry and one exit
	
}
    S2 in valid iff {
	// The station has at least one entry and one exit
  	//all t: Track | t.succs in Entry 
  	//all t: Track | t.succs in Exit
  	//some t: Track | t.succs in Exit
  some t: Track |
        some e: Entry | e in t.succs and e in t.signals and e in Exit and e in Junction
        some t: Track |some x: Exit | x in t.succs and x in t.signals and x in Entry and x in Junction
	
}
    S3 in valid iff {
  // The station has at least one entry and one exit
  all t: Track, ex: Exit, en: Entry | ex in t.succs and en in t.succs
}
    S4 in valid iff {
  // The station has at least one entry and one exit
  // Tracks
  all t: Track | Entry in t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))
}
    S5 in valid iff {
  // The station has at least one entry and one exit
  // Tracks
  all t: Track | Entry in t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) and Exit in t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))
}
    S6 in valid iff {
	// The station has at least one entry and one exit
	one {e: Exit | e in Track}
}
    S7 in valid iff {
	// The station has at least one entry and one exit
	one {e: Exit | one e.succs}
}
    S8 in valid iff {
	// The station has at least one entry and one exit
	one {e: Exit | one e.succs}
    one {e: Entry | one e.succs}
}
    S9 in valid iff {
	// The station has at least one entry and one exit
  	no {x: Entry | x = x}
    some Exit
}
    S10 in valid iff {
	// The station has at least one entry and one exit
  	all t: Track | t.succs in Entry
  	all t: Track | t.succs in Exit
	
}
    S11 in valid iff {
	// The station has at least one entry and one exit
  	some t: Track | t.succs in Entry
  	some t: Track | t.succs in Exit
	
}
    S12 in valid iff {
	// The station has at least one entry and one exit
  	all t: Track | t.succs in Entry + Exit
  	//some t: Track | t.succs in Exit
	
}
    S13 in valid iff {
	// The station has at least one entry and one exit
	Junction =  (Entry + Exit)
}
    S14 in valid iff {
	// The station has at least one entry and one exit
  	all t:Track | t in Entry and t in Exit
	
}
    S15 in valid iff {
	// The station has at least one entry and one exit
	all t : Track | all tsucc : t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) | t.signals!=t.signals-Entry and t.signals!=t.signals-Exit
}
    S16 in valid iff {
	// The station has at least one entry and one exit
  	//all t: Track | t.succs in Entry 
  	//all t: Track | t.succs in Exit
  	//some t: Track | t.succs in Exit
  all t: Track | some e: Entry |some x: Exit |e in t.succs and x in t.succs 
	
}
    S17 in valid iff {
	// The station has at least one entry and one exit
  	//all t: Track | t.succs in Entry 
  	//all t: Track | t.succs in Exit
  	//some t: Track | t.succs in Exit
  some t: Track | some e: Entry | e in t.succs 
  some t: Track |some x: Exit | x in t.succs 
	
}
    S18 in valid iff {
	// The station has at least one entry and one exit
  	//all t: Track | t.succs in Entry 
  	//all t: Track | t.succs in Exit
  	//some t: Track | t.succs in Exit
  all t: Track | all e: Entry | e in t.succs 
  all t: Track |all x: Exit | x in t.succs 
	
}
    S19 in valid iff {
	// The station has at least one entry and one exit
	Track =  (Entry + Exit)
}
    S20 in valid iff {
	// The station has at least one entry and one exit
  	all s:Signal | s in Entry and s in Exit
	
}
    S21 in valid iff {
	// The station has at least one entry and one exit
	some Entry and one Exit
}
    S22 in valid iff {
	// The station has at least one entry and one exit
   //all t : Track | one t in Entry and one t in Exit
   // some ex:Exit, e:Entry | e in Track and ex in Track
   some t: Track | t in Entry and t in Exit

	
}
    S23 in valid iff {
	// The station has at least one entry and one exit
  	some Entry implies some Exit
	
}
    S24 in valid iff {
	// The station has at least one entry and one exit
  	one Entry implies some Exit
	
}
    S25 in valid iff {
	// The station has at least one entry and one exit
	//all t: Track | some Entry->t and some Exit->t
	some t1: Entry, t2: Exit | t1 != t2
}
    S26 in valid iff {
	// The station has at least one entry and one exit
  all t : Track | some Exit & t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) and t in Entry.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))  
	
}
    S27 in valid iff {
	// The station has at least one entry and one exit
  all t : Track | some Exit & t.^succs and t in Entry.^succs  
	
}
    S28 in valid iff {
	// The station has at least one entry and one exit
  
  some Exit and some Entry and (all e : Track | some Exit & e.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) and some Entry & (((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))).e)
 	
}
    S29 in valid iff {
	// The station has at least one entry and one exit
  (all e : Entry | some Exit & e.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))) and (all e : Exit | some Entry & (((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))).e)
	
}
    S30 in valid iff {
	// The station has at least one entry and one exit
	some Entry
}
    S31 in valid iff {
	// The station has at least one entry and one exit
     some s : Track | Entry in s and Exit in s
	
}
    S32 in valid iff {
	// The station has at least one entry and one exit
     all s : Track | Entry in s and Exit in s
	
}
    S33 in valid iff {
	// The station has at least one entry and one exit
     all s : Track | some ( s.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) & Entry & Exit)
	
}
    S34 in valid iff {
	// The station has at least one entry and one exit
     all s : Track | some ( s.^(succs) & Entry & Exit)
	
}
    S35 in valid iff {
	// The station has at least one entry and one exit
	all t: Track | one en: Entry | one e: Exit | en in t.^succs+t and e in t.^succs+t
}
    S36 in valid iff {
	// The station has at least one entry and one exit
	all t: Track | some en: Entry | some e: Exit | en in t.^succs+t and e in t.^succs+t
}
    S37 in valid iff {
	// The station has at least one entry and one exit
  	all t : Track | some en : Entry, ex : Exit | en in t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) and ex in t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))
  	all t : Track | t in Entry iff t not in Exit
	
}
    S38 in valid iff {
	// The station has at least one entry and one exit
  	all t : Track | some en : Entry, ex : Exit | en in t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) and ex in t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))
  	all t : Track | t in Entry implies t not in Exit
	
}
    S39 in valid iff {
	// The station has at least one entry and one exit
  	// all t : Track | some en : Entry | en in t or en in t.^succs
	// all t : Track | some ex : Exit  | ex in t or ex in t.^succs
  	all t : Track | some en : Entry, ex : Exit | en not in t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) and ex not in t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))
	
}
    S40 in valid iff {
	// The station has at least one entry and one exit
  	// all t : Track | some en : Entry | en in t or en in t.^succs
	// all t : Track | some ex : Exit  | ex in t or ex in t.^succs
  	all t : Track | some en : Entry, ex : Exit | en not in t.^succs and ex not in t.^succs
	
}
    S41 in valid iff {
	// The station has at least one entry and one exit
  	// all t : Track | some en : Entry | en in t or en in t.^succs
	// all t : Track | some ex : Exit  | ex in t or ex in t.^succs
  	all t : Track, en : Entry, ex : Exit | en not in t.^succs and ex not in t.^succs
	
}
    S42 in valid iff {
	// The station has at least one entry and one exit
  	// all t : Track | some en : Entry | en in t or en in t.^succs
	// all t : Track | some ex : Exit  | ex in t or ex in t.^succs
  	all t : Track, en : Entry | en not in t and en not in t.^succs 
  	all t : Track, ex : Exit  | ex not in t and ex not in t.^succs
	
}
    S43 in valid iff {
	// The station has at least one entry and one exit
  	// all t : Track | some en : Entry | en in t or en in t.^succs
	// all t : Track | some ex : Exit  | ex in t or ex in t.^succs
  	all t : Track, en : Entry, ex : Exit | en not in t and en not in t.^succs and ex not in t and ex not in t.^succs
  	//all t : Track, ex : Exit  | ex not in t and ex not in t.^succs
	
}
    S44 in valid iff {
	// The station has at least one entry and one exit
  	// all t : Track | some en : Entry | en in t or en in t.^succs
	// all t : Track | some ex : Exit  | ex in t or ex in t.^succs
  	all t : Track, en : Entry, ex : Exit | !(en not in t and en not in t.^succs and ex not in t and ex not in t.^succs)
  	//all t : Track, ex : Exit  | ex not in t and ex not in t.^succs
	
}
    S45 in valid iff {
	// The station has at least one entry and one exit
	all t:Track |
  		some en:Track,e:Track |
  			en in t.succs and e in t.succs
}
    S46 in valid iff {
	// The station has at least one entry and one exit
  	all e : Entry, j : Junction | some t : Track | e in t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) and e != j
	all e : Exit,  j : Junction | some t : Track | e in t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) and e != j
}
    S47 in valid iff {
	// The station has at least one entry and one exit
  one Entry
  one Exit
	
}
    S48 in valid iff {
	// The station has at least one entry and one exit
	all t : Track | one Entry and one Exit
}
    S49 in valid iff {
	// The station has at least one entry and one exit
	all t : Track | some Entry and some Exit
}
    S50 in valid iff {
	// The station has at least one entry and one exit
  	some t : Track | t in Entry or t in Exit
	
}
    S51 in valid iff {
	all t: Track |
  		some en: Entry, e: Exit |
  			en in t.succs and e in t.succs and en != e
}
    S52 in valid iff {
  // The station has at least one entry and one exit
	all t: Track |
  		some en: Entry, e: Exit |
  			en in t.^succs and e in t.^succs
}
    S53 in valid iff {
	// The station has at least one entry and one exit
	some t: Track | some en: Entry, e: Exit | en in t.^succs and e in t.^succs
}
    S54 in valid iff {
	// The station has at least one entry and one exit
  all t : Track | one (t.^succs & Exit)
  all t : Track | one (t.^succs & Entry)
  
	
}
    S55 in valid iff {
  // The station has at least one entry and one exit
	all t: Track |
  		some en: Entry, e: Exit |
  			(t in Entry and e in t.^succs) or
  			(t in Exit and en in t.^succs)
}
    S56 in valid iff {
  // The station has at least one entry and one exit
	all t: Track |
  		some exe:Track |
  			(exe in Entry & t.^succs) or
  			(exe in Exit & t.^succs)
}
    S57 in valid iff {
	// The station has at least one entry and one exit
	all t: Track | some (t.^succs+t & Entry) and some (t.^succs+t & Exit)
}
    S58 in valid iff {
	// The station has at least one entry and one exit
	all t: Track | one en: Entry, ex: Exit | en in t.succs and ex in t.succs
}
    S59 in valid iff {
	// The station has at least one entry and one exit
	all t: Track | lone en: Entry, ex: Exit | en in t.succs and ex in t.succs
}
    S60 in valid iff {
	// The station has at least one entry and one exit
	all t: Track | lone en: Entry, ex: Exit | en in t.^succs and ex in t.^succs
}
    S61 in valid iff {
	// The station has at least one entry and one exit
	all t: Track | some en: Entry | one ex: Exit | en in t.^succs and ex in t.^succs
}
    S62 in valid iff {
	// The station has at least one entry and one exit
	all t: Track | some en: Entry | one ex: Exit | en in t.succs and ex in t.succs
}
    S63 in valid iff {
	// The station has at least one entry and one exit
	all t : Track | one en : Entry | one ex : Exit | t in en or t in ex	
}
    S64 in valid iff {
	// The station has at least one entry and one exit
	all t : Track | one en : Entry | one ex : Exit | t in succs.en or t in succs.ex	
}
    S65 in valid iff {
	// The station has at least one entry and one exit
  	one t : Track | t.succs in (Entry & Exit)
	
}
    S66 in valid iff {
	// The station has at least one entry and one exit
  	one t : Track | t in Entry or t in Exit
	
}
    S67 in valid iff {
	// The station has at least one entry and one exit
  	one t : Track | t in Entry and t in Exit
	
}
    S68 in valid iff {
	// The station has at least one entry and one exit
  	lone t : Track | t in (Entry & Exit)
	
}
    S69 in valid iff {
	// The station has at least one entry and one exit
  	lone t : Track | t not in Junction
	
}
    S70 in valid iff {
	// The station has at least one entry and one exit
  	some t: Track | t = Entry
	
}
    S71 in valid iff {
	some t : Track | t in Entry
	all t : Track | t not in Entry implies t in Exit

}
    S72 in valid iff {
	// The station has at least one entry and one exit
  	some t : Track | t in Entry implies t in Exit
	
}
    S73 in valid iff {
	// The station has at least one entry and one exit
  	one t : Track | t in Entry implies t in Exit
	
}
    S74 in valid iff {
	// The station has at least one entry and one exit
  	lone t : Track | t in Entry implies t in Exit
	
}
    S75 in valid iff {
	// The station has at least one entry and one exit
  	one t:Track | some e:Entry, ex:Exit | e in t and ex in t.succs
	
}
    S76 in valid iff {
	// The station has at least one entry and one exit
	lone Entry and lone Exit
}
    S77 in valid iff {
	// The station has at least one entry and one exit
    lone (Entry + Exit)	
}
    S78 in valid iff {
	// The station has at least one entry and one exit
	all t : Track | t!=t.succs-Entry and t!=t.succs-Exit
}
    S79 in valid iff {
	// The station has at least one entry and one exit
	all t : Track | t not in Entry and t not in Exit and t!=t.succs-Entry and t!=t.succs-Exit
}
    S80 in valid iff {
	// The station has at least one entry and one exit
	all t : Track | (t in Entry or t in Exit) and t!=t.succs-Entry and t!=t.succs-Exit
}
    S81 in valid iff {
	// The station has at least one entry and one exit
	all t : Track | t in Entry implies some t.succs & Exit
}
    S82 in valid iff {
	// The station has at least one entry and one exit
	all t : Track | some t&Entry and some t.succs&Exit
}
    S83 in valid iff {
	// The station has at least one entry and one exit
	all t : Track | some t&Entry and some t.succs&Exit or some t&Exit and some t.succs&Entry
}
    S84 in valid iff {
	// The station has at least one entry and one exit
	all t:Track | one e:Entry | one x:Exit | t in e.^succs or t=e and x in t.^succs or x=t
}
    S85 in valid iff {
	// The station has at least one entry and one exit
	all t:Track | one e:Entry | one x:Exit | (t in e.^succs or t=e) and (x in t.^succs or x=t)
}
    S86 in valid iff {
	// The station has at least one entry and one exit
	all t: Track |all suc:t.succs| some e:Exit | some et:Entry | e in t or e in suc and et in t or et in suc
}
    S87 in valid iff {
	// The station has at least one entry and one exit
	some e:Entry | some x:Exit | one st: e.^succs | x in st
}
    S88 in valid iff {
	// The station has at least one entry and one exit
	all t: Track |all suc:t.succs| some e:Exit | some et:Entry | (e in t or e in suc) and (et in t or et in suc)
}
    S89 in valid iff {
	// The station has at least one entry and one exit
	some e:Entry | some x:Exit | x in e.^succs or e=x
}
    S90 in valid iff {
	// The station has at least one entry and one exit
	all t : Track | some e : Entry | some x : Exit | (t + t.succs + t.^succs) in e and (t + t.succs + t.^succs) in x
}
    S91 in valid iff {
	// The station has at least one entry and one exit
	some t : Track | some e : Entry | some x : Exit | (t + t.succs + t.^succs) in e and (t + t.succs + t.^succs) in x
}
    S92 in valid iff {
	// The station has at least one entry and one exit
  some en : Entry | en in Track
  some ex : Entry | ex in Track 
  no e: Entry, ex: Exit | e = ex
}
    S93 in valid iff {
	// The station has at least one entry and one exit
  all t : Track | some en : Entry | en in t
  all t : Track | some ex : Entry | ex in t 
  no e: Entry, ex: Exit | e = ex
}
    S94 in valid iff {
	// The station has at least one entry and one exit
  all t : Track | t in Entry  

}
    S95 in valid iff {
	// The station has at least one entry and one exit
	all t: Track | some j: Junction | some e: Exit | j in t.succs and e in t.succs
}
    S96 in valid iff {
	// The station has at least one entry and one exit
	lone e: Entry, x: Exit | e != x
}
    S97 in valid iff {
	// The station has at least one entry and one exit
	one e: Entry, ex: Exit | e != ex
}
    S98 in valid iff {
	// The station has at least one entry and one exit

  	some Exit
}
    S99 in valid iff {
	// The station has at least one entry and one exit
	all t : Track | some t => t in Entry and some t => t in Exit
}
    S100 in valid iff {
	// The station has at least one entry and one exit
	all t : Track | some t.^succs => t in Entry & Exit
}
    S101 in valid iff {
	// The station has at least one entry and one exit
  	all s: Signal | one s.~signals
	
}
    S102 in valid iff {
	// The station has at least one entry and one exit
	succs in Track one -> some Entry
}
    S103 in valid iff {
	// The station has at least one entry and one exit
	succs in Track one -> some Entry
  
  	succs in Track one -> some Exit
}
    S104 in valid iff {
	// The station has at least one entry and one exit
	succs in Track one -> some Entry
  
  	succs in Track one -> some Exit
  
  	succs in Track -> set Junction
}
    S105 in valid iff {
	// The station has at least one entry and one exit
	all t : Track | some Entry & Exit
}
    S106 in valid iff {
	// The station has at least one entry and one exit
  all j : Junction | some e : Entry, exit : Exit | e in j.succs and exit in j.succs
}
    S107 in valid iff {
	// The station has at least one entry and one exit
  all t : Track | some e : Entry, exit : Exit, j : Junction | e in t.succs and exit in t.succs and j in t.succs
}
    S108 in valid iff {
	// The station has at least one entry and one exit
	some Entry
  	some Exit
  	no t: Track | t in Entry and t in Exit
}
    S109 in valid iff {
	// The station has at least one entry and one exit
  all t: Track | some e:Entry | e in t.succs
  	
}
    S110 in valid iff {
	// The station has at least one entry and one exit
	Entry in Track.succs
  	Exit in Track.succs
}
    S111 in valid iff {
	// The station has at least one entry and one exit
  Track = Entry + Exit + Junction
  
	
}
    S112 in valid iff {
	// The station has at least one entry and one exit
  	some t: Track | t = Track
  	some t: Track | t = Exit
	
}
    S113 in valid iff {
	// The station has at least one entry and one exit
  all t1, t2: Track | t1 = Exit and t2 = Entry	
  	
	
}
    S114 in valid iff {
	// The station has at least one entry and one exit
  	some t: Track |  t = Entry or t = Exit
	
}
    S115 in valid iff {
	// The station has at least one entry and one exit
  	some t: Track |  t = Entry and t = Exit
	
}
    S116 in valid iff {
	// The station has at least one entry and one exit
  some disj t1,t2: Track | t1 = Exit and t2 = Entry	
  	
	
}
    S117 in valid iff {
	// The station has at least one entry and one exit
  all t: Track | t = Exit or t = Entry	
  	
	
}
    S118 in valid iff {
	// The station has at least one entry and one exit
 	all t:Track | some en:Entry, ex:Exit | en in t or ex in t


}
    S119 in valid iff {
  all disj t,t1 : Track | t in Entry and t1 in Exit
	// The station has at least one entry and one exit	
}
    S120 in valid iff {
  all disj t,t1,t2 : Track |(t1 in t.succs and t2 in t.succs) and t in Entry and t1 in Exit 
	// The station has at least one entry and one exit	
}
    S121 in valid iff {
 some t : Track | 
    some e : Entry | e in t.succs and 
    some x : Exit | x in t.succs
	// The station has at least one entry and one exit	
}
    S122 in valid iff {
	// The station has at least one entry and one exit
	all t: Track | all en: Entry, ex: Exit | en in t and ex in t
}
    S123 in valid iff {
	// The station has at least one entry and one exit
	all t: Track | all en: Entry, ex: Exit | en in t iff ex in t
}
    S124 in valid iff {
	// The station has at least one entry and one exit
  all x: Track | some y: Entry | y in x.succs or x = Entry
  
  all x: Track | some y: Exit | y in x.succs or x = Exit
	
}
    S125 in valid iff {
	// The station has at least one entry and one exit
  all x: Track | some y: Entry | y in x.succs or x in Entry
  
  all x: Track | some y: Exit | y in x.succs or x in Exit
	
}
    S126 in valid iff {
	// The station has at least one entry and one exit
	Entry != Exit
}
    S127 in valid iff {
	// The station has at least one entry and one exit
	some t:Track | Entry in t.^succs
  	some t:Track | Exit in t.^succs
}
    S128 in valid iff {
	// The station has at least one entry and one exit
	some t:Track | Entry in t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))
  	some t:Track | Exit in t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))
}
    S129 in valid iff {
	// The station has at least one entry and one exit
	some t:Track | Entry in t.succs
  	some t:Track | Exit in t.succs
}
    S130 in valid iff {
	// The station has at least one entry and one exit
  all t : Track | one (t.^succs & Exit)
  all t : Track | one (t.^succs & Entry)
  all t : Track | lone (t.^succs & Track)
  
	
}
    S131 in valid iff {
	// The station has at least one entry and one exit
  all i:Track | some disj x,y:Track | x in i.succs and y in i.succs implies x in Entry and y in Exit
}
    S132 in valid iff {
	// The station has at least one entry and one exit
	all tr: Track |
  		some (tr.succs & Exit) and 
  		some (succs.tr & Entry)
}
    S133 in valid iff {
	// The Junction has at least one entry and one exit
	all j : Junction |
		j.succs in Entry and j.succs in Exit
}
    S134 in valid iff {
	// The station has at least one entry and one exit
  	all t : Track | (Entry in ^succs.t) and (Exit in t.^succs)
	
}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, S74, S75, S76, S77, S78, S79, S80, S81, S82, S83, S84, S85, S86, S87, S88, S89, S90, S91, S92, S93, S94, S95, S96, S97, S98, S99, S100, S101, S102, S103, S104, S105, S106, S107, S108, S109, S110, S111, S112, S113, S114, S115, S116, S117, S118, S119, S120, S121, S122, S123, S124, S125, S126, S127, S128, S129, S130, S131, S132, S133, S134 extends Formula {}

run {
    #valid.Oracle = 3
    #(Instance - valid.Oracle) = 3
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 8 Atom, exactly 4 TrackAtom, exactly 4 SignalAtom,
       exactly 6 Instance, 6 Int
