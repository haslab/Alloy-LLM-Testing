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
    Oracle in valid iff {
	// Exit tracks are those without successor
  	all t : Track | t in Exit iff no t.succs

}
    S1 in valid iff {
  // Exit tracks are those without successor
  all e: Exit | no e.succs

}
    S2 in valid iff {
	// Exit tracks are those without successor
  	Exit = {t : Track | no succs} 

}
    S3 in valid iff {
	// Exit tracks are those without successor

}
    S4 in valid iff {
	// Exit tracks are those without successor
	all t : Track | no t.succs implies t in Exit
}
    S5 in valid iff {
	// Exit tracks are those without successor
  	no succs.Exit

}
    S6 in valid iff {
	// Exit tracks are those without successor
	Exit = Track - Track.succs
}
    S7 in valid iff {
	// Exit tracks are those without successor
	all t: Exit | some t.succs
}
    S8 in valid iff {
	// Exit tracks are those without successor
	all t: Exit | lone t.succs
}
    S9 in valid iff {
	// Exit tracks are those without successor
	some t: Exit | no t.succs
}
    S10 in valid iff {
	// Exit tracks are those without successor
	lone t: Exit | no t.succs
}
    S11 in valid iff {
	// Exit tracks are those without successor
	one t: Exit | no t.succs
}
    S12 in valid iff {
	// Exit tracks are those without successor
	all e : Exit | no(e.succs) and some(succs.e)
}
    S13 in valid iff {
	// Exit tracks are those without successor
	all t: Exit | no t.succs
  	all t: Exit | (some succs.t) or (t in Exit and t in Entry)
}
    S14 in valid iff {
	// Exit tracks are those without successor
    all t: Exit | no (t -> Track.succs)


}
    S15 in valid iff {
	// Exit tracks are those without successor
	//all t: Exit | no t.succs
  	//all t: Track - Exit| some t.succs
  
  	some (Track - Exit).succs
}
    S16 in valid iff {
	// Exit tracks are those without successor
	//all t: Exit | no t.succs
  	//all t: Track - Exit| some t.succs
  	no Exit.succs
  	some (Track - Exit).succs
}
    S17 in valid iff {
	// Exit tracks are those without successor
  // all t: Exit | no t.succs
  all t: Track - Exit | some t.succs
  // no Exit.succs
  some (Track - Exit).succs

}
    S18 in valid iff {
	// Exit tracks are those without successor
  all t:Track-Exit | some t.succs - t
  

}
    S19 in valid iff {
	//Exit tracks are those without successor
  	all t:Track | (no t.succs or t.succs =t implies t in Exit)
  	

}
    S20 in valid iff {
	//Exit tracks are those without successor
  	all t:Track | (no t.succs or t in t.succs implies t in Exit)
  	

}
    S21 in valid iff {
	// Exit tracks are those without successor
	all e : Track - Exit | e.succs in e
}
    S22 in valid iff {
	//Exit tracks are those without successor
   all t:Track | no succs.t implies t in Exit
  	

}
    S23 in valid iff {
	//Exit tracks are those without successor
   //all t:Track | no succs.t implies t in Exit
  	all t:Track | all t1:Track | t1 not in t.succs implies t in Exit  
}
    S24 in valid iff {
	//Exit tracks are those without successor
   all t:Track | some t.succs implies t in Exit
  	//all t:Track | (all t1:Track | t1 not in t.succs) implies t in Exit  
}
    S25 in valid iff {
	//Exit tracks are those without successor
   all t:Track | one t.succs implies t in Exit
  	//all t:Track | (all t1:Track | t1 not in t.succs) implies t in Exit  
}
    S26 in valid iff {
	// Exit tracks are those without successor
  all t:(Track-Exit), e:Exit | no (e.succs ) and some(t.succs)

}
    S27 in valid iff {
	// Exit tracks are those without successor
  	all e : Entry | some(e.succs)
	all e : Exit | no(e.succs)
}
    S28 in valid iff {
	// Exit tracks are those without successor
	all e : Exit | (e not in Entry) implies no(e.succs) and some(succs.e)
}
    S29 in valid iff {
	// Exit tracks are those without successor
  no (Exit.succs) and  some(succs.Exit)

}
    S30 in valid iff {
	// Exit tracks are those without successor
  	all t : Track-Junction-Entry | no t.succs

}
    S31 in valid iff {
	// Exit tracks are those without successor
  	all ex : Exit | some t : Track | ex in t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) implies no ex.succs

}
    S32 in valid iff {
	// Exit tracks are those without successor
  	all t : Track | t not in t.^succs
  	all ex : Exit | some t : Track | ex in t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) implies no ex.succs

}
    S33 in valid iff {
	// Exit tracks are those without successor
  	all t :Exit | no t & t.^succs
	all t :Track | no t.succs implies t in Exit and t in Exit implies no t.succs
}
    S34 in valid iff {
  // Exit tracks are those without successor
  all t: Track | no t.signals implies t in Exit
}
    S35 in valid iff {
	// Exit tracks are those without successor
  	all t1, t2 : Track | (t2 in t1.succs and t2 in Exit) implies no t2.succs
}
    S36 in valid iff {
	// Exit tracks are those without successor
  	all t1, t2 : Track | (t1 in Entry and t2 in t1.succs and t2 in Exit) implies no t2.succs
}
    S37 in valid iff {
	// Exit tracks are those without successor
  all t : Track | Exit in t implies no t.succs

}
    S38 in valid iff {
	// Exit tracks are those without successor
  all t : Track | no t.succs implies Exit in t 

}
    S39 in valid iff {
	// Exit tracks are those without successor
  all t : Track | one e : Exit | e not in t implies some t.succs
  //all e : Exit | no e.succs
  
  
}
    S40 in valid iff {
	// Exit tracks are those without successor
  all t : Track, e : Exit | e not in t implies some t.succs - t
  //all e : Exit | no e.succs
  
  
}
    S41 in valid iff {
	// Exit tracks are those without successor
  all t : Track | t not in t.succs
  all t : Track, e : Exit | e not in t implies some t.succs
  //all e : Exit | no e.succs
  
  
}
    S42 in valid iff {
	// Exit tracks are those without successor
  all t : Track | t not in t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden))
  all t : Track, e : Exit | e not in t implies some t.succs
  //all e : Exit | no e.succs
  
  
}
    S43 in valid iff {
	// Exit tracks are those without successor
  //all t : Track | t not in t.*succs
  all t : Track, e : Exit | e in t implies no t.succs
  all t : Track, e : Entry, j : Junction | some e+j & t implies some t.succs
  //all e : Exit | no e.succs
  
  
}
    S44 in valid iff {
	// Exit tracks are those without successor
  all t : Track | t not in t.succs
  all t : Track, e : Exit | e in t implies no t.succs
  all t : Track, e : Entry, j : Junction | some e+j & t implies some t.succs
  //all e : Exit | no e.succs
  
  
}
    S45 in valid iff {
	// Exit tracks are those without successor
  //all t : Track | t not in t.succs
  all t : Track, e : Exit | e in t implies no t.succs
  all t : Track, e : Entry, j : Junction | (e in t or j in t) implies some t.succs
  //all e : Exit | no e.succs
  
  
}
    S46 in valid iff {
	// Exit tracks are those without successor
  all t : Track| one e : Exit | e in t implies no t.succs
  //all t : Track, e : Entry, j : Junction | (e in t or j in t) implies some t.succs
  //all e : Exit | no e.succs
  
  
}
    S47 in valid iff {
	// Exit tracks are those without successor
  all t:Track| no t.succs implies Exit in t
  all e:Exit | no e.succs

}
    S48 in valid iff {
	// Exit tracks are those without successor
	no Track.succs implies Track in Exit
}
    S49 in valid iff {
	// Exit tracks are those without successor
	all t :Track | t in Exit iff t.^succs not in Exit
}
    S50 in valid iff {
	// Exit tracks are those without successor
	all t: Track | t in Exit implies no t.succs and some Entry & ^succs.t
}
    S51 in valid iff {
	// Exit tracks are those without successor
	all t: Track | t in Exit implies no t.^succs and some e: Entry | e in ((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)).t
}
    S52 in valid iff {
	// Exit tracks are those without successor
	Exit.succs = none and
  	no Entry & Exit
}
    S53 in valid iff {
	// Exit tracks are those without successor
  	no succs.Exit and no Exit.succs

}
    S54 in valid iff {
	// Exit tracks are those without successor
  	no (succs.Exit & Exit.succs)

}
    S55 in valid iff {
	// Exit tracks are those without successor
  	no (succs.Exit)
  	some (Exit.succs)
  

}
    S56 in valid iff {
	// Exit tracks are those without successor
	all et : Exit | Track not in et.succs 
}
    S57 in valid iff {
	// Exit tracks are those without successor
	all t : Exit | no t.succs & Entry
}
    S58 in valid iff {
	// Exit tracks are those without successor
  
	all ex:Exit  | ex.succs = none or ex.succs = ex
}
    S59 in valid iff {
	// Exit tracks are those without successor
	all x : Exit | all t : Track | x in t and no t.succs
}
    S60 in valid iff {
	// Exit tracks are those without successor
	all x : Exit | all t : Track | x in t and t not in t.succs implies no t.succs
}
    S61 in valid iff {
	// Exit tracks are those without successor
	all disj t1, t2: Track | t2 not in t1.succs => t1 in Exit
}
    S62 in valid iff {
	// Exit tracks are those without successor
	all t : Track | all tr : Track | not tr in t.succs implies t in Exit
  
  	all t : Track | not t in t.succs
}
    S63 in valid iff {
	// Exit tracks are those without successor
  all t:Track-Exit | some t.succs and t not in t.succs
  

}
    S64 in valid iff {
	// Exit tracks are those without successor
  all t: Track | some t.succs => t in Exit and t not in Junction and t not in Entry

}
    S65 in valid iff {
    // Exit tracks are those without successors
    all t: Track | no t.succs implies t in Exit-Junction-Entry
}
    S66 in valid iff {
	// Exit tracks are those without successor
	some t : Track | t in Exit implies no t.succs
}
    S67 in valid iff {
	// Exit tracks are those without successor

  	all t:Track | t in Entry implies #t.succs =0
}
    S68 in valid iff {
	// Exit tracks are those without successor
  	all t: Track | t not in Entry and no t.succs => t in Exit
}
    S69 in valid iff {
	// Exit tracks are those without successor
	all t : Track | no succs.t implies Exit in t 
}
    S70 in valid iff {
	// Exit tracks are those without successor
	all t : Track | no succs.t iff Exit in t 
}
    S71 in valid iff {
	// Exit tracks are those without successor
  all t1,t2:Track | t1.^succs = t2

}
    S72 in valid iff {
	// Exit tracks are those without successor
	no e : Exit | some e.succs
  	all t : Track | no t.succs implies t in Entry
}
    S73 in valid iff {
	// Exit tracks are those without successor
	all t : Exit-Junction-Entry | no t.succs
}
    S74 in valid iff {
	// Exit tracks are those without successor
	//all t: Track | no t.succs => {
    //  t in Exit
  	//}
  	Exit = Track - Track.signals
}
    S75 in valid iff {
	// Exit tracks are those without successor
	Track.succs != none implies Track in Exit
}
    S76 in valid iff {
	// Exit tracks are those without successor
	no Track.succs implies Track in Exit
  	no Exit.succs
}
    S77 in valid iff {
	// Exit tracks are those without successor
	all e : Exit | no e.succs
  	no e: Exit | e in Entry + Junction
}
    S78 in valid iff {
	// Exit tracks are those without successor
	all e : Exit | no e.succs
  	no t: Track | t in Entry and t in Exit and t in Junction
}
    S79 in valid iff {
	// Exit tracks are those without successor
	Track = Junction+Entry+Exit 
}
    S80 in valid iff {
	// Exit tracks are those without successor
	Track  =Junction+ Entry+ Exit 
  	all t:Track | t in Exit implies t.succs = none
}
    S81 in valid iff {
	// Exit tracks are those without successor
	Track = Junction+Entry+Exit
  	all t:Track | t in Entry implies t.succs = none
}
    S82 in valid iff {
	// Exit tracks are those without successor
	all t : Track | no t.succs iff t = Exit
}
    S83 in valid iff {
	// Exit tracks are those without successor
	all t : Track | all tr : Track | (not tr in t.succs and not t in t.succs) implies t in Exit
}
    S84 in valid iff {
	// Exit tracks are those without successor
	all t : Exit | all tr : Track | not tr in t.succs implies t in Exit
  
  	all t : Track | not t in t.succs
}
    S85 in valid iff {
	// Exit tracks are those without successor
	all t : Track | (t not in t.succs) and (no t.succs implies t in Exit)
}
    S86 in valid iff {
	// Exit tracks are those without successor
  	all t :Track | no t & t.^succs
	all t :Track | no t.succs implies t in Exit
}
    S87 in valid iff {
	// Exit tracks are those without successor
	all t:Track | t in Exit implies no t.succs 
  	all t:Track | t not in t.^succs
}
    S88 in valid iff {
	// Exit tracks are those without successor
	all t:Track | t in Exit implies no t.succs 
  	all t:Track | t not in t.^succs
  	some succs.Exit
}
    S89 in valid iff {
	// Exit tracks are those without successor
	all t:Track | t in Exit implies no t.succs 
  	all t:Track | t not in t.^succs
  	some Track-Exit implies some succs.Exit
}
    S90 in valid iff {
	// Exit tracks are those without successor

  	Track in Exit iff no Track.succs
}
    S91 in valid iff {
	// Exit tracks are those without successor
  	all t : Track | some (Track - Exit).succs or lone Track
	no Exit.succs
}
    S92 in valid iff {
	// Exit tracks are those without successor
  	all t : Track | some (Track - Exit).succs or Exit = Entry
	no Exit.succs
}
    S93 in valid iff {
	// Exit tracks are those without successor
  	all t : Track | some (Track - Exit).succs or lone Track or some Exit & Entry
	no Exit.succs
}
    S94 in valid iff {
	// Exit tracks are those without successor
  	all t : Track | some (Track - Exit).succs or lone Track
	//no Exit.succs
}
    S95 in valid iff {
	// Exit tracks are those without successor
	all t : Track | no t.succs implies t in Exit and no Exit.succs
}
    S96 in valid iff {
	// Exit tracks are those without successor
  all e : Entry | no t : Track | e in t.succs
	all e : Exit | no e.succs
}
    S97 in valid iff {
	// Exit tracks are those without successor
  
  	all ex : Exit | no ex.succs
  
  	all en: Entry | no {t: Track | t.succs = en}

}
    S98 in valid iff {
	// Exit tracks are those without successor
	//all t:Track | no t.succs implies t in Exit
   all t: Track | 
        (no t.succs implies t in Exit)
	all e:Exit | e not in e.succs
}
    S99 in valid iff {
	// Exit tracks are those without successor
	all e : Track - Entry | no e.succs
}
    S100 in valid iff {
    // Exit tracks are those without successor
  	all t: Track | #t.succs > 0
}
    S101 in valid iff {
    // Exit tracks are those without successor
  	all t: Track | #t.succs > 0 and t not in t.succs
}
    S102 in valid iff {
	// Exit tracks are those without successor
  	all t : Track | t not in t.succs and some t.succs implies t in Exit

}
    S103 in valid iff {
	// Exit tracks are those without successor
  	all t : Track | t not in t.succs and (some t.succs implies t not in Exit)

}
    S104 in valid iff {
    // Exit tracks are those without successors
    all t: Track | no t.succs implies t in Track-Junction-Entry
}
    S105 in valid iff {
    // Exit tracks are those without successor, but only Exit tracks should have no successor
    all t: Track - Junction - Entry | no t.succs implies t in Exit
}
    S106 in valid iff {
    // Exit tracks are those without successors
    all t: Track | no t.succs implies t in Exit and t not in Entry
}
    S107 in valid iff {
	// Exit tracks are those without successor
  
  some t : Track | t in Exit implies no t.((^(succs)) + ((this.@Track + this.@Signal + Int + String) <: iden)) 

}
    S108 in valid iff {
	// Exit tracks are those without successor
  	all t :Exit | no t & t.^succs
	all t :Track | no t.succs implies t in Exit
}
    S109 in valid iff {
	// Exit tracks are those without successor
  all e : Exit | e in Track and Track.^succs not in Exit

}
    S110 in valid iff {
	// Exit tracks are those without successor
  all t:Track | t not in t.succs.succs
  all t:Track-Exit | some t.succs 
  

}
    S111 in valid iff {
	// Exit tracks are those without successor
  all t:Track-Exit | some t.succs - t - t.succs.succs
  

}
    S112 in valid iff {
	// Exit tracks are those without successor
	all e : Exit, t : Track - Exit & Entry | t not in e.succs
}
    S113 in valid iff {
	// Exit tracks are those without successor
	all t:Track| t in Exit implies t.succs = none
  	all t:Track| t in Entry implies (some tt:Track| t in tt.succs)
  	
}
    S114 in valid iff {
	// Exit tracks are those without successor
	Exit not in Track.succs
}
    S115 in valid iff {
	// Exit tracks are those without successor
all e : Track - Entry - Junction | no e.^succs and no e

}
    S116 in valid iff {
	// Exit tracks are those without successor
    all e:Exit | no e & e.succs

}
    S117 in valid iff {
	// Exit tracks are those without successor
  some t: Track | t in Exit implies t not in t.succs
}
    S118 in valid iff {
	// Exit tracks are those without successor
	all t : Track | t in Entry <=> no t.~succs
}
    S119 in valid iff {
	// Exit tracks are those without successor
	//all t:Track | no succs.t implies t in Exit
  all t:Track | no t.succs and no succs.t  implies t in Exit
}
    S120 in valid iff {
	// Exit tracks are those without successor
	all t: Track | t not in t.^succs implies t in Exit
}
    S121 in valid iff {
	// Exit tracks are those without successor
	all t: Track | Track not in t.^succs implies t in Exit
}
    S122 in valid iff {
	// Exit tracks are those without successor
    no succs.Entry

}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, S74, S75, S76, S77, S78, S79, S80, S81, S82, S83, S84, S85, S86, S87, S88, S89, S90, S91, S92, S93, S94, S95, S96, S97, S98, S99, S100, S101, S102, S103, S104, S105, S106, S107, S108, S109, S110, S111, S112, S113, S114, S115, S116, S117, S118, S119, S120, S121, S122 extends Formula {}

run {
    #valid.Oracle = 1
    #(Instance - valid.Oracle) = 1
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 8 Atom, exactly 4 TrackAtom, exactly 4 SignalAtom,
       exactly 2 Instance, 6 Int
