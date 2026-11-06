abstract sig Atom {}
sig UserAtom, PhotoAtom, DayAtom extends Atom {}
abstract sig Formula {}
one sig Oracle extends Formula {}
sig detected in Formula {}
sig Instance {
    valid : set Formula,
    User : set UserAtom,
    Influencer : set UserAtom,
    Photo : set PhotoAtom,
    Ad : set PhotoAtom,
    Day : set DayAtom,
    follows : UserAtom -> UserAtom,
    sees : UserAtom -> PhotoAtom,
    posts : UserAtom -> PhotoAtom,
    suggested : UserAtom -> UserAtom,
    date : PhotoAtom -> DayAtom
} {
    follows in User -> User
    sees in User -> Photo
    posts in User -> Photo
    suggested in User -> User
    date in Photo -> Day
    Influencer in User
    Ad in Photo
    date in Photo -> one Day
    // Earlier requirement 0, required in every Instance.
{
	// Every image is posted by one user.
  all p: Photo | one (posts.p)
	
}
    // Earlier requirement 1, required in every Instance.
{
	// Users cannot follow themselves.
    all u: User | u not in u.follows
}
    // Earlier requirement 2, required in every Instance.
{
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all u: User, p: u.sees | p in Ad or posts.p in u.follows
}
    // Earlier requirement 3, required in every Instance.
{
	// If a user posts an ad then all its posts should be labeled as ads. 
  all u: User | some u.posts & Ad implies u.posts in Ad

}
    Oracle in valid iff {
	// Influencers are followed by everyone else.
	all i : Influencer, u : User - i | i in u.follows
}
    S1 in valid iff {
	// Influencers are followed by everyone else.
    all u : User, i: Influencer | i in u.follows
}
    S2 in valid iff {
	// Influencers are followed by everyone else.

  follows.Influencer = User
}
    S3 in valid iff {
	// Influencers are followed by everyone else.
	all i : Influencer, u : User - Influencer | i in u.follows
}
    S4 in valid iff {
	// Influencers are followed by everyone else.

}
    S5 in valid iff {
	// Influencers are followed by everyone else.
  all i: Influencer | all u: User | follows.i in u
}
    S6 in valid iff {
	// Influencers are followed by everyone else.
  	Influencer.~follows = User - Influencer

}
    S7 in valid iff {
	// Influencers are followed by everyone else.
  	 some i:Influencer | i.~follows = User - i

}
    S8 in valid iff {
	// Influencers are followed by everyone else.
	all u : User | u.follows in Influencer
}
    S9 in valid iff {
	// Influencers are followed by everyone else.
	follows in User some -> Influencer
}
    S10 in valid iff {
	// Influencers are followed by everyone else.
	(User - Influencer).follows = Influencer
}
    S11 in valid iff {
	// Influencers are followed by everyone else.
  all i : Influencer | i in (User-Influencer).follows 

}
    S12 in valid iff {
	// Influencers are followed by everyone else.
	 Influencer in (User - Influencer).follows
  	 Influencer.follows = none
}
    S13 in valid iff {
	// Influencers are followed by everyone else.
  all u: User - Influencer | some i: Influencer | i in u.follows

}
    S14 in valid iff {
	// Influencers are followed by everyone else.
  //all u: User - Influencer | some i: Influencer | i in u.follows
  //some i: Influencer | all user: User - Influencer | user in follows.i
  all u: User-Influencer| u in Influencer.follows

}
    S15 in valid iff {
	// Influencers are followed by everyone else.
  //all u: User - Influencer | some i: Influencer | i in u.follows
  all i: Influencer | all user: User - Influencer | user in i.follows

}
    S16 in valid iff {
	// Influencers are followed by everyone else.
  //all u: User - Influencer | some i: Influencer | i in u.follows
  some i: Influencer | all user: User - Influencer | user in follows.i

}
    S17 in valid iff {
	// Influencers are followed by everyone else.
  //all u: User - Influencer | some i: Influencer | i in u.follows
  some i: Influencer | all user: User - Influencer | user in i.follows

}
    S18 in valid iff {
	// Influencers are followed by everyone else.
  //all u: User - Influencer | some i: Influencer | i in u.follows
  //some i: Influencer | all user: User - Influencer | user in follows.i
  some u: User-Influencer| some i: Influencer | i in u.follows

}
    S19 in valid iff {
	// Influencers are followed by everyone else.
  //all u: User - Influencer | some i: Influencer | i in u.follows
  //some i: Influencer | all user: User - Influencer | user in follows.i
  some u: User-Influencer| all i: Influencer | i in u.follows

}
    S20 in valid iff {
	// Influencers are followed by everyone else.
  all u: User | u in Influencer.follows 

}
    S21 in valid iff {
	// Influencers are followed by everyone else.
  //all u: User - Influencer | some i: Influencer | i in u.follows
  //some i: Influencer | all user: User - Influencer | user in follows.i
  all u: User| one i: Influencer | u in i.follows

}
    S22 in valid iff {
	// Influencers are followed by everyone else.
  //all u: User - Influencer | some i: Influencer | i in u.follows
  //some i: Influencer | all user: User - Influencer | user in follows.i
  all u: User| one i: Influencer | u in follows.i

}
    S23 in valid iff {
	// Influencers are followed by everyone else.
	all i: Influencer | i in User.follows
}
    S24 in valid iff {
	// Influencers are followed by everyone else.
  	all u : User-Influencer | follows.u in Influencer

}
    S25 in valid iff {
	// Influencers are followed by everyone else.
	all i: Influencer | i in follows.User
}
    S26 in valid iff {
	// Influencers are followed by everyone else.
  	all i : Influencer, u : Influencer-i | i in u.follows

}
    S27 in valid iff {
	// Influencers are followed by everyone else.
  
    // all x:User | x in Influencer implies 
    //               (all y:User | x!=y implies y->x in follows)
  
    // all x:Influencer, y:User | x!=y implies y->x in follows
  
    // all x:Influencer, y:User | x!=y implies y in follows.x
  
    follows = User->User // - all x : Influencer | x->x
}
    S28 in valid iff {
	// Influencers are followed by everyone else.
  
    // all x:User | x in Influencer implies 
    //               (all y:User | x!=y implies y->x in follows)
  
    // all x:Influencer, y:User | x!=y implies y->x in follows
  
    // all x:Influencer, y:User | x!=y implies y in follows.x
  
     some Influencer.posts & date.Day
}
    S29 in valid iff {
	// Influencers are followed by everyone else.
  
    // all x:User | x in Influencer implies 
    //               (all y:User | x!=y implies y->x in follows)
  
    // all x:Influencer, y:User | x!=y implies y->x in follows
  
    // all x:Influencer, y:User | x!=y implies y in follows.x
  
     all x : Influencer, d : Day | some x.posts & date.d
}
    S30 in valid iff {
	// Influencers are followed by everyone else.
    all x,u : User | x in Influencer implies (all p : Photo | x->p in posts implies x->p in sees)
}
    S31 in valid iff {
	// Influencers are followed by everyone else.
    all x : User | x in Influencer implies (all p : Photo, u : User | x->p in posts implies u->p in sees)
}
    S32 in valid iff {
	all u1:User, u2:User | u1 in u2.follows implies u2 in Influencer  
	// Influencers are followed by everyone else.

}
    S33 in valid iff {
	// Influencers are followed by everyone else.
  	all u:User| one i :User| 
  	(i in Influencer) => i in u.follows

}
    S34 in valid iff {
	all u1:User| one u2:User | u2 in Influencer implies u2 in u2.follows    
	// Influencers are followed by everyone else.

}
    S35 in valid iff {
	// Influencers are followed by everyone else.
	all inf: Influencer, user: User | user != inf => user in inf.follows
}
    S36 in valid iff {
	// Influencers are followed by everyone else.
  some x: User | x in Influencer implies all y: User | x != y implies x -> y in follows

}
    S37 in valid iff {
	// Influencers are followed by everyone else.
  all u1:User | some u2:User | u2 in Influencer implies u1 in u2.follows 

}
    S38 in valid iff {
	// Influencers are followed by everyone else.
    all inf : Influencer | lone follows.inf

}
    S39 in valid iff {
	// Influencers are followed by everyone else.
	one i : Influencer | all u : User | u->i in follows
}
    S40 in valid iff {
	// Influencers are followed by everyone else.
 	some i : Influencer | follows.i in (User - i)

}
    S41 in valid iff {
	// Influencers are followed by everyone else.
	all u : User, v : Influencer | follows.v = u - v
}
    S42 in valid iff {
	// Influencers are followed by everyone else.
	all u: User, d: Day | some i: Influencer | i in u.follows and i in d.posts
}
    S43 in valid iff {
	// Influencers are followed by everyone else.
  //all i : Influencer | i in (User-Influencer).follows 
  
  all u:User | u-Influencer in u.follows

}
    S44 in valid iff {
	// Influencers are followed by everyone else.
  	some i : User | all u : User - i | i in Influencer => i in u.follows

}
    S45 in valid iff {
	// Influencers are followed by everyone else.
  all disj i, u : User |
  i in u.follows 

}
    S46 in valid iff {
	// Influencers are followed by everyone else.
  	some Influencer => follows.Influencer = User - Influencer

}
    S47 in valid iff {
	// Influencers are followed by everyone else.
  all u: User, f: u.follows | some Influencer => some u.follows & Influencer

}
    S48 in valid iff {
	// Influencers are followed by everyone else.
  some Influencer =>  all u: User | u.follows in Influencer

}
    S49 in valid iff {
	// Influencers are followed by everyone else.
  all u: User | some Influencer and u not in Influencer => u.follows in Influencer

}
    S50 in valid iff {
	// Influencers are followed by everyone else.
	all x : User | all z : Influencer | x.follows in z
}
    S51 in valid iff {
	// Influencers are followed by everyone else.
  	all u : User | u != Influencer => Influencer in u.follows

}
    S52 in valid iff {
	// Influencers are followed by everyone else.
	all disj i1,i2 : Influencer | i1 in User.follows and i2 in User.follows implies i1 = i2
}
    S53 in valid iff {
	// Influencers are followed by everyone else.
	all i: Influencer, u:User | 
  		i not in i.follows and u not in i.follows

}
    S54 in valid iff {
	// Influencers are followed by everyone else.
  all i : Influencer, u : User | i in u.follows or u not in i.follows
}
    S55 in valid iff {
	// Influencers are followed by everyone else.
  User not in Influencer.follows
}
    S56 in valid iff {
	// Influencers are followed by everyone else.
	not Influencer = User
  	all u: User, i: Influencer | i in u.follows

}
    S57 in valid iff {
	// Influencers are followed by everyone else.
	Influencer = User or
  	all u: User, i: Influencer | i in u.follows

}
    S58 in valid iff {
	// Influencers are followed by everyone else.
  	some User - Influencer

  	all i : Influencer | i in (User - Influencer).follows
}
    S59 in valid iff {
	// Influencers are followed by everyone else.
  	all i : Influencer | i in (User - Influencer).follows or (User - Influencer) = none
}
    S60 in valid iff {
	// Influencers are followed by everyone else.
  	all u : (User - Influencer) | Influencer != none implies not (u.follows & Influencer) = none
}
    S61 in valid iff {
	// Influencers are followed by everyone else.
  	all u : (User) | Influencer != none implies not (u.follows & Influencer) = none
}
    S62 in valid iff {
	// Influencers are followed by everyone else.
  	all u : (User) | Influencer != none and (User - Influencer != none) implies not (u.follows & Influencer) = none
}
    S63 in valid iff {
	// Influencers are followed by everyone else.
     all i : Influencer | follows.i = User - Influencer
}
    S64 in valid iff {
	// Influencers are followed by everyone else.
  	all i:Influencer, u:User | u != i => Influencer - i in u.follows  

}
    S65 in valid iff {
	// Influencers are followed by everyone else.
  	all i:Influencer | Influencer - i in (User-i).follows  

}
    S66 in valid iff {
	// Influencers are followed by everyone else.
  	all i:Influencer | Influencer - i in User.follows  

}
    S67 in valid iff {
	// Influencers are followed by everyone else.
	all u : User - Influencer | u.follows = Influencer
}
    S68 in valid iff {
	// Influencers are followed by everyone else.
	all u : User | u.follows = Influencer - u
}
    S69 in valid iff {
	// Influencers are followed by everyone else.
	all x : User | x.follows = Influencer
}
    S70 in valid iff {
	// Influencers are followed by everyone else.
	all x: User | some x.follows & Influencer implies x.follows in Influencer
}
    S71 in valid iff {
	// Influencers are followed by everyone else.
	all x: User | lone x.follows & Influencer implies x.follows in Influencer
}
    S72 in valid iff {
	// Influencers are followed by everyone else.
	all x: User | one x.follows & Influencer implies x.follows in Influencer
}
    S73 in valid iff {
	// Influencers are followed by everyone else.
	all x: User | no Influencer.follows & x implies x.follows in Influencer
}
    S74 in valid iff {
	// Influencers are followed by everyone else.
  	some u: User | u in Influencer implies all users: User | u in users.follows
    

}
    S75 in valid iff {
	// Influencers are followed by everyone else.
  all i : Influencer | i.follows not in Influencer
}
    S76 in valid iff {
	// Influencers are followed by everyone else.
  all u: User - Influencer | follows.u = Influencer

}
    S77 in valid iff {
	// Influencers are followed by everyone else.
    all u: User - Influencer, i: Influencer | i.follows in u

}
    S78 in valid iff {
	// Influencers are followed by everyone else.
  all u: User, i: Influencer | some u.follows implies i in u.follows

}
    S79 in valid iff {
	// Influencers are followed by everyone else.
  all u: User, i: Influencer | some Influencer & u.follows implies i in u.follows 

}
    S80 in valid iff {
	// Influencers are followed by everyone else.
  all u: User, ni: User - Influencer,  i: Influencer | some Influencer & ni.follows implies i in u.follows 

}
    S81 in valid iff {
	// Influencers are followed by everyone else.
  all x: User | (some y:User | y in Influencer implies x->y in follows)

}
    S82 in valid iff {
	// Influencers are followed by everyone else.
  	all x : follows.User , y : User.follows | x->y in follows

}
    S83 in valid iff {
	// Influencers are followed by everyone else.
	//all i: Influencer | some u: User| i in u.follows
	//all u: User, i: Influencer | u in Influencer implies u->i in follows
  	some u: User, i: Influencer | one i implies u->i in follows
}
    S84 in valid iff {
	// Influencers are followed by everyone else.
	all i: Influencer | i.~follows.follows = User
}
    S85 in valid iff {
	// Influencers are followed by everyone else.
	all u: User | one Influencer implies Influencer in u.follows
}
    S86 in valid iff {
	// Influencers are followed by everyone else.
	all u: User-Influencer | all i: Influencer | follows.i in u.follows
}
    S87 in valid iff {
	// Influencers are followed by everyone else.
	all u: User-Influencer | all i: Influencer | follows.i in u
}
    S88 in valid iff {
	// Influencers are followed by everyone else.
	all i : Influencer | User.follows <: i = User.follows - i
}
    S89 in valid iff {
	// Influencers are followed by everyone else.
	all i : Influencer | i.follows = User.follows - i
}
    S90 in valid iff {
	// Influencers are followed by everyone else.
	all i : Influencer | follows.i = User.follows - i
}
    S91 in valid iff {
	// Influencers are followed by everyone else.
  all i : Influencer, u : User |
  i in u.follows implies u not in Influencer

}
    S92 in valid iff {
	// Influencers are followed by everyone else.
	all u : User , i : Influencer | u!=i implies u.follows in i 
}
    S93 in valid iff {
	// Influencers are followed by everyone else.
	follows in User -> some Influencer
}
    S94 in valid iff {
	// Influencers are followed by everyone else.
    follows in (User-Influencer) -> some Influencer
}
    S95 in valid iff {
	// Influencers are followed by everyone else.
follows in (User - Influencer) -> Influencer and Influencer in (User - Influencer).follows
}
    S96 in valid iff {
	// Influencers are followed by everyone else.
    follows in (User-Influencer) -> Influencer
}
    S97 in valid iff {
	// Influencers are followed by everyone else.
	//all u : User | (Influencer - u ) in u.follows
  follows in (User - Influencer) -> Influencer and some Influencer

}
    S98 in valid iff {
	// Influencers are followed by everyone else.
	all u: User, i: Influencer | i.follows != none and u not in Influencer implies i in u.follows
}
    S99 in valid iff {
	// Influencers are followed by everyone else.
	all disj u: User, i: Influencer |u not in Influencer implies i in u.^follows
}
    S100 in valid iff {
	// Influencers are followed by everyone else.
	all disj u: User, i: Influencer |i in u.^follows
}
    S101 in valid iff {
	// Influencers are followed by everyone else.
	all i: Influencer | i in (User-Influencer).follows or #Influencer = 1
}
    S102 in valid iff {
	// Influencers are followed by everyone else.
	all i: Influencer | i in (User-Influencer).follows or #User = 1
}
    S103 in valid iff {
	// Influencers are followed by everyone else.
	all i: Influencer | i in User.follows or #User = 1
}
    S104 in valid iff {
	// Influencers are followed by everyone else.
	all u: User | Influencer in u.^follows or #User=1
}
    S105 in valid iff {
	// Influencers are followed by everyone else.
	all u: User | Influencer in u.((^(follows)) + ((this.@User + this.@Photo + this.@Day + Int + String) <: iden)) or #User=1
}
    S106 in valid iff {
	// Influencers are followed by everyone else.
	all u: (User-Influencer) | Influencer in (u.follows + Influencer.follows) or #User=1
}
    S107 in valid iff {
	// Influencers are followed by everyone else.
	all u: (User-Influencer) | (Influencer in u.follows and Influencer in Influencer.follows) or #User=1
}
    S108 in valid iff {
	// Influencers are followed by everyone else.
	all u: User | u = Influencer implies all u2: User-u | u in u2.follows
}
    S109 in valid iff {
	// Influencers are followed by everyone else.
   some i: Influencer | all u: User - i | u in i.follows

}
    S110 in valid iff {
	// Influencers are followed by everyone else.
	one u : User | no i : Influencer | i not in u.follows

}
    S111 in valid iff {
	// Influencers are followed by everyone else.
        all x: Influencer | (x in (User-x).follows) or (no ((User-x).follows))




}
    S112 in valid iff {
	// Influencers are followed by everyone else.
  	all i : Influencer | follows.i  = User-i    
	all u : User | u-Influencer in u.follows
}
    S113 in valid iff {
	// Influencers are followed by everyone else.
  	all i : Influencer | i.follows  = User-i          
    all u : User | Influencer-u in u.follows
}
    S114 in valid iff {
	// Influencers are followed by everyone else.
	//all u : Influencer | follows.u = User - u
 	all i : Influencer | follows.i in (i.follows.follows - i.follows)
}
    S115 in valid iff {
	// Influencers are followed by everyone else.
	all u: User |
  		u in Influencer iff (follows.u & User = none)
}
    S116 in valid iff {
	// Influencers are followed by everyone else.
	all u: User |
  		u in Influencer iff all u2: User - u | u in u2.follows
}
    S117 in valid iff {
	// Influencers are followed by everyone else.
  all disj u1, u2 : User | u1 in Influencer and u1 in u2.follows

}
    S118 in valid iff {
	// Influencers are followed by everyone else.
  //all u1 : Influencer |all u : User  u in follows.u1
  all u:User | u.follows&Ad = Ad
}
    S119 in valid iff {
	// Influencers are followed by everyone else.
	all u: User| one u1:User | u in follows.u1 implies u1 in Influencer 
}
    S120 in valid iff {
	// Influencers are followed by everyone else.
	all i: Influencer | all u: User - i | i.~follows = u
}
    S121 in valid iff {
	// Influencers are followed by everyone else.
	no u: User | u.follows & Influencer = Influencer
}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, S74, S75, S76, S77, S78, S79, S80, S81, S82, S83, S84, S85, S86, S87, S88, S89, S90, S91, S92, S93, S94, S95, S96, S97, S98, S99, S100, S101, S102, S103, S104, S105, S106, S107, S108, S109, S110, S111, S112, S113, S114, S115, S116, S117, S118, S119, S120, S121 extends Formula {}

run {
    #valid.Oracle = 1
    #(Instance - valid.Oracle) = 1
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 12 Atom, exactly 4 UserAtom, exactly 4 PhotoAtom, exactly 4 DayAtom,
       exactly 2 Instance, 6 Int
