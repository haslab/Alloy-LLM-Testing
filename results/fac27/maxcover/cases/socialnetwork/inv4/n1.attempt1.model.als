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
    Oracle in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  all u: User | some u.posts & Ad implies u.posts in Ad

}
    S1 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  

}
    S2 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  
	all u: User, p: u.posts | p in Ad
  
}
    S3 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u : User, p : Photo, a : Ad | u in posts.a implies u not in posts.p
}
    S4 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads.
  	all u : User | all a : Ad | u->a in posts and
  	all p  : Photo | u->p in posts implies p in Ad


}
    S5 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  	//all u: User | all p: Photo | p in Ad implies u.posts = Ad
  	all u:User | Ad in u.posts implies u.posts in Ad

}
    S6 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
    all u : User | u.sees in Ad or no (u.sees & Ad)

}
    S7 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u:User | some p:Photo | p in Ad and p in u.posts implies u.posts in Ad
}
    S8 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  all u : User, a : Ad | a in u.posts => lone (u.posts - Ad)

}
    S9 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u : User | no (u.posts & Ad) and some (u.posts & Ad) and u.posts in Ad
}
    S10 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u: User | u.posts in Ad implies (u.posts not in Ad)
}
    S11 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads.
  	all u : User | (one u.posts & Ad) implies u.posts in Ad

}
    S12 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	//all u : User | (some a : Photo | u in posts.a and a in Ad) implies (all p : u.posts |  p in Ad)

	//all u : User | (some a : u.posts | a in Ad) implies (all p : u.posts |  p in Ad)
	//all u : User, a : u.posts | a in Ad implies (all p : u.posts |  p in Ad)
  	//all u : User, a : u.posts | a in Ad implies (all p : u.posts |  p in Ad)
	all u : User | some a : u.posts | a in Ad implies u.posts in Ad

}
    S13 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  	all u: User |Ad in u.posts iff u.posts in Ad
  //all u: User, p: Ad |
        //(p in u.posts) implies (all q: p -> Photo | q in u.posts)

}
    S14 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  	all u: User| some a: Ad |a in u.posts iff u.posts in a
  //all u: User, p: Ad |
        //(p in u.posts) implies (all q: p -> Photo | q in u.posts)

}
    S15 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  	all u: User| all a: Ad |a in u.posts iff u.posts in a
  //all u: User, p: Ad |
        //(p in u.posts) implies (all q: p -> Photo | q in u.posts)

}
    S16 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  	all u: User| all a: Ad |a in u.posts implies all p: u.posts| p in a
  //all u: User, p: Ad |
        //(p in u.posts) implies (all q: p -> Photo | q in u.posts)

}
    S17 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  	all u: User| all a: Ad |a in u.posts implies all p: Photo| u.posts in p
  //all u: User, p: Ad |
        //(p in u.posts) implies (all q: p -> Photo | q in u.posts)

}
    S18 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u : User | some ad : Ad | ad in u.posts implies u.posts in Ad 
}
    S19 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u : User, p : Photo | p in Ad implies u.posts in Ad
}
    S20 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all x: User | (some y: Photo | x->y in posts and y in Ad) implies 
  all z: Photo | x->z in posts and z in Ad  
}
    S21 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  all x : User | all y : Photo | (x in posts.y) and (y in Ad) 
}
    S22 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u: User | some(u.posts & Ad) implies (u.posts = Ad)
}
    S23 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	some u:User | some y:Photo | (y in u.posts and y in Ad) implies u.posts in Ad
}
    S24 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads.
  all i: Influencer | i.posts in Ad implies i.posts = Ad

}
    S25 in valid iff {
	all u:User, p:Photo | some (u.posts & Ad) implies p in Ad else p not in Ad
	// If a user posts an ad then all its posts should be labeled as ads. 

}
    S26 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all user: User | one post: Photo | post in user.posts and post in Ad => user.posts in Ad
}
    S27 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all user: User | one ad: Ad | ad in user.posts => user.posts in Ad
}
    S28 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  all u:User, up:u.posts | one p:Photo | p in u.posts and p in Ad implies up in Ad

}
    S29 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  all u:User, p:Photo | (p in Ad and p in u.posts) implies u.posts in Ad else u.posts not in Ad

}
    S30 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  all u:User | one p:Photo | p in u.posts and p in Ad implies u.posts in Ad else u.posts not in Ad

}
    S31 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u : User, p : u.posts | Ad in p implies u.posts = Ad
}
    S32 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads.
  	some u : User | u->Ad in posts implies u.posts in Ad

}
    S33 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	some u: User | some a: Ad | a in u.posts => u.posts in Ad
}
    S34 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  all u: User | some a: Ad | all p : Photo | p in Ad 
}
    S35 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  
	all u : User, a : u.posts & Ad | a in u.sees

}
    S36 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads.
   all u : User | one p : u.posts| (p in Ad) implies (p in u.posts )

}
    S37 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads.
    all user : User | some Ad and some user.follows.posts
 
}
    S38 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads.
    all user : User | some Ad - user.posts and some user.follows.posts
 
}
    S39 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads.
    all user : User | some Ad or some user.follows.posts
 
}
    S40 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	(all u : User | some p : Photo | p in u.posts and p in Ad) => (all p : Photo, u : User | p in u.posts => p in Ad)
}
    S41 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads.
    all user : User | user.sees in Ad and some user.follows.posts
 
}
    S42 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads.
  all u: User, ad: Ad | (ad in u.sees) => (no u1: User | u1.posts & ad != ad)


}
    S43 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  	all x: User | some y: Ad | y in x.posts implies (all z: Photo | z in x.posts and z in Ad) 
}
    S44 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  all u: User | (some sup: u.posts |Ad in sup) implies (all up:u.posts| Ad in up)

}
    S45 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all x : User | Ad in x.posts   
}
    S46 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads.
  	all u : User | Ad in u.sees implies u.sees in Ad

}
    S47 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads.
  	all u : User | some a : Ad | a in u.sees implies u.sees in Ad

}
    S48 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  no a : Ad | some u : User | a in u.posts and all a2 : u.posts | a2 in Ad
}
    S49 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u: User | no u.posts
}
    S50 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  all u:User | (u.posts in Ad) => u.posts = Ad 

}
    S51 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u : User | #u->Ad=1
}
    S52 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all user : User | #user->Ad = 0 or #user->Ad = #user.posts
  //all post : user.posts | post in Ad or all post : user.posts | post not in Ad
}
    S53 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u:User | one up: u.posts | up in Ad implies u.posts in Ad
}
    S54 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  	all u : User, a : Photo | one add : Ad | u->add in posts implies
  		a in Ad

}
    S55 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u : User | Ad in u.posts implies all p : u.posts | p = Ad
}
    S56 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	some u : User |  ( u.posts in Ad ) implies u.posts in Ad    	

}
    S57 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u : User | one p : Ad | p in u.posts implies all p1 : Photo | p1 in Ad
}
    S58 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  	all u : User | some p : Photo | u in posts.p and p in Ad implies 
  	all p1 : Photo | u in posts.p1 implies p1 in Ad
  
	all u : User | some (u.posts & Ad) implies u.posts in Ad
}
    S59 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u : User | some pa : u.posts & Ad | #pa > 0 implies (all p : u.posts | p in Ad)
}
    S60 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u: User | some Ad & u.posts iff u.posts in Ad
}
    S61 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads.
  	no Ad
	all u: User | (some Ad & u.posts) iff (u.posts in Ad)
}
    S62 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
all u: User | some p: Photo | (u in posts.p) and (p in Ad) implies u.posts in Ad

  all x : User | (some y : Photo | x->y in posts and y in Ad) 
}
    S63 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	lone u:User | some y:Photo | (y in u.posts and y in Ad) implies u.posts in Ad
}
    S64 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  all u: User | (some sup: u.posts |Ad in u.posts) implies (all up:u.posts| Ad in up)

}
    S65 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  all u : User | u.posts in Ad iff u in Influencer

}
    S66 in valid iff {
  // If a user posts an ad then all its posts should be labeled as ads.
  one u: User | all p: u.posts | (p in Ad) implies (p in u.posts)
}
    S67 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  all u: User |
  all disj p1, p2: Photo | {
    p1 in u.posts 
    p2 in u.posts
    p1 in Ad implies p2 in Ad
  }
}
    S68 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u:User | some a:Ad | a in u.posts implies no (u.posts & Photo)
}
    S69 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all a : Ad | not some u : User | a in u.posts implies all a2 : u.posts | a2 in Ad
}
    S70 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  	some a : Ad | all u :User | a in u.posts implies u.posts in Ad
  	
}
    S71 in valid iff {
	all x : User, y,z : Ad | z in Ad and x -> z in posts implies x -> y in posts and y in Ad
 
  
	// If a user posts an ad then all its posts should be labeled as ads. 

}
    S72 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  all a : Ad | some u : User | u->a in posts implies all a2 : u.posts | a2 in Ad
}
    S73 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u: User, p:Photo | some ad: Ad | ad in u.posts implies p in u.posts and p in Ad
}
    S74 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  all x : User, y : x.sees | y in Ad

}
    S75 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u : User | some a : Ad | a in u.posts implies (all x: u.posts| x in a)
}
    S76 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u : User, p : u.posts | Ad in p implies p = Ad
}
    S77 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads.
  all u:User | Ad in u.posts implies (Photo not in u.posts)

}
    S78 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  all u : User | Ad in u.posts and not Photo in u.posts

}
    S79 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads.
  	all u:User | (Ad!=none and Ad in u.posts) implies (u.posts in Ad)
}
    S80 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u: User | one p: Photo | ((p in Ad and p in u.posts) and u.posts in Ad)
}
    S81 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u: User | lone a: u.posts & Ad | u.posts in Ad
}
    S82 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  	all u : User | some a : Ad |
  		a in u.sees implies u.posts in Ad

}
    S83 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  	all u : User, a : Ad |
  		a in u.sees implies u.posts in Ad

}
    S84 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
    all a: Ad, u:User | u in posts.a implies u in Influencer

}
    S85 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
all u:User | lone u.posts&Ad implies u.posts in Ad
}
    S86 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads.
  	 some u : User | u.posts in Ad => all p : Photo | posts.p in Ad

}
    S87 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  	all u :User, p: Photo | one y: Ad | y in u.posts implies p in u.posts
}
    S88 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  	all u :User, p: Photo, y: Ad | y in u.posts implies p in u.posts
}
    S89 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u : User, p : u.posts , a : Ad | a in p implies p = Ad

}
    S90 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u : User, p: u.posts | one o: u.posts | (o in u) implies (p = Ad)
}
    S91 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u : User, p: u.posts | Ad in p implies (p != Photo)
}
    S92 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u : User | (one x : u.posts | x in Ad) implies (all p : u.posts | p = Ad) 
}
    S93 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u : User | (some x : u.posts | x in Ad) implies (all p : u.posts | p = Ad) 
}
    S94 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads.
	
  	some u : User | one a : Ad | u->a in posts implies (all p : Photo | u->p in posts implies p in Ad)

}
    S95 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  	one u : User | some a : u.posts | a in Ad implies (all p : u.posts | p in Ad)
}
    S96 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u: User | some a: Ad | {
      a in u.posts => u.posts in Ad else u.posts not in Ad
    }
}
    S97 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u: User | 
  		some p: u.posts | some a: Ad | {
      		a in p => p in Ad
    }
}
    S98 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  	all x: User | some z: Ad | (x in Influencer and z in x.posts) implies (all z: Photo | z in x.posts and z in Ad)
}
    S99 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  	all x: User | some z: Ad | (z in x.posts) implies (all z: Photo | x in Influencer and z in x.posts and z in Ad)
}
    S100 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u:User | one a:Ad | a in u.posts implies no (u.posts & Photo)
}
    S101 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u : User | lone p : Ad | p in u.posts implies u.posts in Ad
}
    S102 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u : User | no sees.Ad
}
    S103 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	no sees.Ad or (some sees.Ad and no (sees.Photo - sees.Ad))
}
    S104 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	no posts.Ad or (some posts.Ad and no (posts.Photo - posts.Ad))
}
    S105 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u : User, p : u.posts | Ad in p implies (all z : Photo | z = Ad)
}
    S106 in valid iff {
 all u:User | some p : Photo |p in Ad implies all p1:Photo| p1 in u.posts and p1 in Ad
	// If a user posts an ad then all its posts should be labeled as ads. 

}
    S107 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u : User | u in Influencer and u.posts in Ad
}
    S108 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  	all u:User | (no (u.posts & Ad)) implies (u.posts & Ad = u.posts)

}
    S109 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u : User| some p : Photo-Ad | u in posts.p implies p in Ad
  
}
    S110 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u : User | one a : Ad | a in u.posts implies u.posts = Ad 
}
    S111 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  	some a : Ad | a in User.posts implies User.posts in Ad
  	

}
    S112 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  	some a : Ad | all u :User | some u.posts & Ad implies u.posts in Ad
  	
}
    S113 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u:User | u.posts in Ad or lone (Ad & u.posts) 
}
    S114 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  // if user, posts ad, if  post then ad
  all u : User | all p : u.posts | one a : Ad |
  	a in u.posts implies p in Ad

}
    S115 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  // if user, posts ad, if  post then ad
  all u : User | all p : u.posts | one a : Ad |
  	a in p implies p in Ad

}
    S116 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  	all u : User | one ad : Ad | ad in u.posts implies (all p : Photo | p in u.posts and p = Ad)

}
    S117 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u : User | some a : Ad | a in u.posts implies u.posts = u.posts + Ad
}
    S118 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  all u : User |one  p : Photo | u in posts.p and p in Ad implies p in Ad

}
    S119 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  all u: User, p: Photo | lone a: Ad | a in u.posts implies Ad in p

}
    S120 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  all u: User, p: Photo | lone a: Ad | a in u.posts implies a in p

}
    S121 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	all u:User | lone p: u.posts | p in Ad => u.posts in Ad
}
    S122 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	some u : User | (u.posts in Ad)
}
    S123 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	//all u: User | u in (posts.Photo & posts.Ad)
  	not Photo in Ad
}
    S124 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
  	all u:User, p: Photo | one u.posts and p in Ad implies u.posts in Ad

}
    S125 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
//  	all u:User, p: Photo | some u.posts and p in Ad implies u.posts in Ad
	one u: User| all p: Photo | #u.posts>0 and p in Ad implies u.posts in Ad 
}
    S126 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
//  	all u:User, p: Photo | some u.posts and p in Ad implies u.posts in Ad
	one u: User| all a:Ad | u in posts.a  implies u.posts in Ad 
   
}
    S127 in valid iff {
	// If a user posts an ad then all its posts should be labeled as ads. 
	no u: User | 
		some u.posts & Ad implies no u.posts & (Photo - Ad)
}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, S74, S75, S76, S77, S78, S79, S80, S81, S82, S83, S84, S85, S86, S87, S88, S89, S90, S91, S92, S93, S94, S95, S96, S97, S98, S99, S100, S101, S102, S103, S104, S105, S106, S107, S108, S109, S110, S111, S112, S113, S114, S115, S116, S117, S118, S119, S120, S121, S122, S123, S124, S125, S126, S127 extends Formula {}

run {
    #valid.Oracle = 1
    #(Instance - valid.Oracle) = 1
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 12 Atom, exactly 4 UserAtom, exactly 4 PhotoAtom, exactly 4 DayAtom,
       exactly 2 Instance, 6 Int
