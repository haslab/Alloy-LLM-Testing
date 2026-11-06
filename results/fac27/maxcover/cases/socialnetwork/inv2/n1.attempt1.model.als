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
    Oracle in valid iff {
	// Users cannot follow themselves.
    all u: User | u not in u.follows
}
    S1 in valid iff {
	// Users cannot follow themselves.

}
    S2 in valid iff {
	// Users cannot follow themselves.
	all x, y : User | some follows.x
}
    S3 in valid iff {
	// Users cannot follow themselves.
	all u : User | one follows.u 
}
    S4 in valid iff {
	// Users cannot follow themselves.
  	all u : User |  (u in u.follows)

}
    S5 in valid iff {
	// Users cannot follow themselves.
  all u: User | no follows.u

}
    S6 in valid iff {
	// Users cannot follow themselves.
	all u: User | not ( u in u.suggested)
}
    S7 in valid iff {
	// Users cannot follow themselves.
  	all u: User | u.follows != u

}
    S8 in valid iff {
	// Users cannot follow themselves.
	all disj u0,u1 : User | no (u0.follows - u1.follows)
}
    S9 in valid iff {
	// Users cannot follow themselves.
	all disj u0,u1 : User | no (u0.follows & u1.follows)
}
    S10 in valid iff {
	// Users cannot follow themselves.
	all disj u0,u1 : User | no u0.^follows
}
    S11 in valid iff {
	// Users cannot follow themselves.
	all disj u0,u1 : User | no (u0.^follows & u1.^follows)
}
    S12 in valid iff {
	// Users cannot follow themselves.
	all disj u0,u1 : User | one (u0.^follows & u1.^follows)
}
    S13 in valid iff {
	// Users cannot follow themselves.
	all disj u0 : User | one u0.^follows 
}
    S14 in valid iff {
	// Users cannot follow themselves.
	all disj u0 : User | some u0.^follows 
}
    S15 in valid iff {
	// Users cannot follow themselves.
	all disj u0,u1 : User | some (u0.^follows + u1.^follows) 
 	//some (u0.follows & u1.follows)
}
    S16 in valid iff {
	// Users cannot follow themselves.
	all disj u0,u1 : User | some (u0.^follows - u1.^follows) 
 	//some (u0.follows & u1.follows)
}
    S17 in valid iff {
	// Users cannot follow themselves.
  all x : User | x & ((this.@User + this.@Photo + this.@Day + Int + String) <: iden).x in none

}
    S18 in valid iff {
	// Users cannot follow themselves.
	all u : User | User in u.follows 

}
    S19 in valid iff {
	// Users cannot follow themselves.
   all a:User,b:User | no (a.follows & follows.b)
}
    S20 in valid iff {
	// Users cannot follow themselves.
  one u:User | u not in u.follows
  

}
    S21 in valid iff {
	// Users cannot follow themselves.
	all u : User | some follow : User | follow not in u.follows	
}
    S22 in valid iff {
	// Users cannot follow themselves.
  all u : User | some u1 : User | u1 in u.follows implies u!=u1

}
    S23 in valid iff {
	// Users cannot follow themselves.
  	all x : User | follows.x != x
  

}
    S24 in valid iff {
	// Users cannot follow themselves.
	all u: User | u not in u.^follows
}
    S25 in valid iff {
	// Users cannot follow themselves.
  	// all x : User | all y : User | x in follows.y implies x!=y
  	
  	all disj x,y : User | x in follows.y

}
    S26 in valid iff {
	// Users cannot follow themselves.
  	follows in ((this.@User + this.@Photo + this.@Day + Int + String) <: iden)

}
    S27 in valid iff {
	// Users cannot follow themselves.
	User not in User.follows
}
    S28 in valid iff {
	not all u:User | u in u.follows

}
    S29 in valid iff {
	// Users cannot follow themselves.

  	// all p : User | not p -> p in follows

	// ou, usando quantificador 'no' ("nenhum...") 
	// 
  	// no p : User | p -> p in follows

	// Não é possível eliminar a variável p e
	// substituir quantificador 'no' por operador 'no' sobre conjuntos
	//
  	//no p : User | p in p.follows
  
  all x, y: User | not(x->y in follows) and x = y
}
    S30 in valid iff {
	// Users cannot follow themselves.
    all user : User | no user.suggested
}
    S31 in valid iff {
	// Users cannot follow themselves.
  	all x,y : User | x->y in follows implies y->x not in follows
}
    S32 in valid iff {
	// Users cannot follow themselves.
	follows not in ((this.@User + this.@Photo + this.@Day + Int + String) <: iden)
}
    S33 in valid iff {
	// Users cannot follow themselves.
	all x : User | not one follows.x
}
    S34 in valid iff {
	// Users cannot follow themselves.
  	follows not in ~follows and ~follows not in follows
}
    S35 in valid iff {
	// Users cannot follow themselves.
  	follows.~follows not in ((this.@User + this.@Photo + this.@Day + Int + String) <: iden)
}
    S36 in valid iff {
	// Users cannot follow themselves.
  	follows.~follows not in follows
}
    S37 in valid iff {
	// Users cannot follow themselves.
  	not follows in User -> User

}
    S38 in valid iff {
	// Users cannot follow themselves.
  User not in follows.User

}
    S39 in valid iff {
	// Users cannot follow themselves.
  one u: User | u in u.follows

}
    S40 in valid iff {
	// Users cannot follow themselves.
	one u1: User | one u2: User | u1 -> u2 in follows
  
}
    S41 in valid iff {
	// Users cannot follow themselves.
  
  all p1, p2 : User | p1.follows = p2 

}
    S42 in valid iff {
	// Users cannot follow themselves.
	all disj x, y : User | all p : y.posts | (p in x.sees) iff (y in x.follows)
}
    S43 in valid iff {
	// Users cannot follow themselves.
  	all u : User |  u.((^(follows)) + ((this.@User + this.@Photo + this.@Day + Int + String) <: iden)) != u

}
    S44 in valid iff {
	// Users cannot follow themselves.
	all u: User | u.follows = (User - u)
}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44 extends Formula {}

run {
    #valid.Oracle = 1
    #(Instance - valid.Oracle) = 1
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 12 Atom, exactly 4 UserAtom, exactly 4 PhotoAtom, exactly 4 DayAtom,
       exactly 2 Instance, 6 Int
