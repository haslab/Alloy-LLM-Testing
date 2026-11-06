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
    Oracle in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all u: User, p: u.sees | p in Ad or posts.p in u.follows
}
    S1 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    // all u: User, p: u.sees | p in Ad or posts.p in u.follows
    all p: Photo | (p in Ad) or (sees.p in User.follows)
}
    S2 in valid iff {
    // Users can see ads posted by everyone,
    // but only see non-ads posted by followed users.
    all u: User |
        u.sees in Ad and
        (all p: u.sees - Ad | some f: u.follows | p in f.posts - Ad)
}
    S3 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User, a: Ad | u.posts in (u.follows.posts & a)
}
    S4 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    // all u: User, p: u.sees | p in Ad or posts.p in u.follows
    all p: Photo | (p in Ad) or p in (User.follows.posts)
}
    S5 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User, a: Ad | u.sees in (u.follows.posts & a)
}
    S6 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.

}
    S7 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all a : Ad | some sees.a
}
    S8 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all p : Photo | all u : User | (p in u.posts and p in Ad) implies p in u.sees + Ad
  	all p : Photo | all u : User | (p in u.posts and p !in Ad) implies p in u.follows.sees

}
    S9 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.

  // Photos from followed users
  all a: Ad | lone sees.a
}
    S10 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u,m:User, p:Photo | all a:Ad | a in u.sees and m in u.follows implies p in u.sees 

}
    S11 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u,m:User-Influencer, p:Photo | all a:Ad | a in u.sees and m in u.follows implies p in u.sees 

}
    S12 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	//all u,m:User - Influencer, p:Photo | all a:Ad | a in u.sees and m in u.follows implies p in u.sees

  	all u: User - Influencer, a:Ad | a in u.sees
}
    S13 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	//all u,m:User - Influencer, p:Photo | all a:Ad | a in u.sees and m in u.follows implies p in u.sees

  	//all u: User - Influencer, a:Ad - Photo | a in u.sees
  
  	all u: User, p: Photo |
    (p in Ad implies p in u.sees) and
    (p not in Ad implies
      (p in u.posts and (p in u.follows.sees or p in u.sees))
    )
}
    S14 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	//all u,m:User - Influencer, p:Photo | all a:Ad | a in u.sees and m in u.follows implies p in u.sees

  	//all u: User - Influencer, a:Ad - Photo | a in u.sees
  
  	all u: User - Influencer, p: Photo |
    (p in Ad implies p in u.sees) and
    (p not in Ad implies
      (p in u.posts and (p in u.follows.sees or p in u.sees))
    )
}
    S15 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	//all u,m:User - Influencer, p:Photo | all a:Ad | a in u.sees and m in u.follows implies p in u.sees

  	//all u: User - Influencer, a:Ad - Photo | a in u.sees
  
  	all u: User, p: Photo |
    (p in Ad implies p in u.sees) and
    (p not in Ad implies
      ((u in Influencer implies p in u.posts) and
       (p in u.follows.sees or p in u.sees))
    )
}
    S16 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	//all u,m:User - Influencer, p:Photo | all a:Ad | a in u.sees and m in u.follows implies p in u.sees

  	//all u: User - Influencer, a:Ad - Photo | a in u.sees
  
  	//all u: User, p: Photo |
    //(p in Ad implies p in u.sees) and
    //(p not in Ad implies
      //((u in Influencer implies p in u.posts) and
       //(p in u.follows.sees or p in u.sees))
    //)
  	
  	all u: User + Influencer, a: Ad | a in u.sees
}
    S17 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	//all u,m:User - Influencer, p:Photo | all a:Ad | a in u.sees and m in u.follows implies p in u.sees

  	//all u: User - Influencer, a:Ad - Photo | a in u.sees
  
  	//all u: User, p: Photo |
    //(p in Ad implies p in u.sees) and
    //(p not in Ad implies
      //((u in Influencer implies p in u.posts) and
       //(p in u.follows.sees or p in u.sees))
    //)
  	
  	all u: User + Influencer, a: Ad | a in u.follows.sees
}
    S18 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	//all u,m:User - Influencer, p:Photo | all a:Ad | a in u.sees and m in u.follows implies p in u.sees

  	//all u: User - Influencer, a:Ad - Photo | a in u.sees
  
  	//all u: User, p: Photo |
    //(p in Ad implies p in u.sees) and
    //(p not in Ad implies
      //((u in Influencer implies p in u.posts) and
       //(p in u.follows.sees or p in u.sees))
    //)
  	
  	all u: User + Influencer, a: Ad | a in u.follows.sees and a in u.sees
}
    S19 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	//all u,m:User - Influencer, p:Photo | all a:Ad | a in u.sees and m in u.follows implies p in u.sees

  	//all u: User - Influencer, a:Ad - Photo | a in u.sees
  
  	//all u: User, p: Photo |
    //(p in Ad implies p in u.sees) and
    //(p not in Ad implies
      //((u in Influencer implies p in u.posts) and
       //(p in u.follows.sees or p in u.sees))
    //)
  	
  	//all u: User + Influencer, a: Ad | a in u.follows.sees and a in u.sees
  		all u: User, i:Influencer, p: Photo | (p in Ad implies some u.sees) and (p in Ad implies  some i.sees)
}
    S20 in valid iff {
	// Users can see ads posted by everyone, 
  all p : Ad | all u:User | all i:Influencer | p in u.sees and not u = i
	// but only see non ads posted by followed users.

}
    S21 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	//all u,m:User - Influencer, p:Photo | all a:Ad | a in u.sees and m in u.follows implies p in u.sees

  	//all u: User - Influencer, a:Ad - Photo | a in u.sees
  
  	//all u: User, p: Photo |
    //(p in Ad implies p in u.sees) and
    //(p not in Ad implies
      //((u in Influencer implies p in u.posts) and
       //(p in u.follows.sees or p in u.sees))
    //)
  	
  	//all u: User + Influencer, a: Ad | a in u.follows.sees and a in u.sees
  		all u: User, i:Influencer, p: Photo | (p in Ad implies some u.follows.sees) and (p in Ad implies some i.follows.sees)
}
    S22 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	//all u,m:User - Influencer, p:Photo | all a:Ad | a in u.sees and m in u.follows implies p in u.sees

  	//all u: User - Influencer, a:Ad - Photo | a in u.sees
  
  	//all u: User, p: Photo |
    //(p in Ad implies p in u.sees) and
    //(p not in Ad implies
      //((u in Influencer implies p in u.posts) and
       //(p in u.follows.sees or p in u.sees))
    //)
  	
  	//all u: User + Influencer, a: Ad | a in u.follows.sees and a in u.sees
  		all u: User, p: Photo |
    (p in Ad implies p in u.sees) and
    (p not in Ad implies (
      (p in u.posts and p in u.sees) or
      (p in u.follows.posts and p in u.follows.sees) or
      (u in Influencer and p in u.posts and p in u.sees))) or
    (p in Ad and u in User)
}
    S23 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	//all u,m:User - Influencer, p:Photo | all a:Ad | a in u.sees and m in u.follows implies p in u.sees

  	//all u: User - Influencer, a:Ad - Photo | a in u.sees
  
  	//all u: User, p: Photo |
    //(p in Ad implies p in u.sees) and
    //(p not in Ad implies
      //((u in Influencer implies p in u.posts) and
       //(p in u.follows.sees or p in u.sees))
    //)
  	
  	//all u: User + Influencer, a: Ad | a in u.follows.sees and a in u.sees
  		//all u: User, p: Photo |
    //(p in Ad implies p in u.sees) and
    //(p not in Ad implies (
      //(p in u.posts and p in u.sees) or
      //(p in u.follows.posts and p in u.follows.sees) or
      //(u in Influencer and p in u.posts and p in u.sees))) or
    //(p in Ad and u in User)
  
  	all u1:User,nonAd: Photo-Ad| Ad in u1.sees and (some nonAd & u1.sees) => (posts.nonAd in u1.follows)  
  	// If Jon can see Ads and can also see non ads it implies that the posts were made by people Jon followed
}
    S24 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User | u.sees = {Ad + u.follows.posts} 

}
    S25 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	//all x: User, p : Photo | p in x.sees implies (p in Ad) or posts.p in x.follows
  all x: User, p: Photo | p in Ad or p in x.follows.posts

}
    S26 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all p: Photo | some u: User | p in u.sees implies p in Ad or p in u.follows.posts 

}
    S27 in valid iff {
	  // Users can see ads posted by everyone,
 // Users can see ads posted by everyone.
  // Users can see ads posted by everyone.
  all p: Ad | all u: User | p in u.sees

  // Users only see non-ads posted by followed users.
  all p: Photo - Ad | all u: User | p in u.sees implies (u in u.follows && p not in Ad)
  
}
    S28 in valid iff {
	  // Users can see ads posted by everyone,
 // Users can see ads posted by everyone.
  all p: Ad | all u: User | p in u.sees

  // Users only see non-ads posted by followed users.
  all p: Photo - Ad | all u: User | p in u.sees implies (u in u.follows or p in u.posts)
  
}
    S29 in valid iff {
  // Users can see ads posted by everyone.
  all p: Ad | all u: User | p in u.sees

  // Users only see non-ads posted by followed users.
  all p: (Photo - Ad), u: User | p in u.follows
}
    S30 in valid iff {
  // Users can see ads posted by everyone.
  all p: Ad | all u: User | p in u.sees

  // Users only see non-ads posted by followed users.
  all p: Photo - Ad, u: User | (p in u.sees) implies (p in u.posts implies u in u.follows)
}
    S31 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User | u.sees = u.follows.posts

}
    S32 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User, p:Photo|
  	(p in u.sees) <=> (p in u.follows.posts) || (p in Ad) 

}
    S33 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all a : Ad | (all u : User | a in u.posts) implies (all u : User | a in u.sees)
	all p : Photo | all u1 : User | (not (p in Ad) and p in u1.sees) implies (some u2 : User | u2 in u1.follows and p in u2.posts)
}
    S34 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User | no a: Ad | a in u.sees & u.follows.posts
}
    S35 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User | u.sees in u.follows.posts
}
    S36 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | u.sees = (Ad + u.follows.posts + u.posts)

}
    S37 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | u.sees = (Ad + u.follows.posts + u.posts - (Ad - u.posts))

}
    S38 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User | u.suggested = Ad + u.follows.posts
}
    S39 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User | some u.sees & Ad
  	///all u: User | some u.sees.follows
}
    S40 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User | some u.sees
  	//all u: User | u.
}
    S41 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User | some u.sees & Ad
  	all u: User | some u.sees.follows
}
    S42 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all u: User, p: Photo | p in u.sees implies p in Photo - Ad
}
    S43 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User | some (u.sees & Ad)
  	all u: User | some (u.sees & u.follows.posts)
}
    S44 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User | u.sees in Ad
  	//all u: User | some (u.sees & Ad)
  	all u: User | u.follows.posts in u.sees
}
    S45 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User | u.sees in Ad
  	//all u: User | some (u.sees & Ad)
  	all u: User | (u.follows.posts) not in u.sees
}
    S46 in valid iff { //TODO
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	//all u: User, a: Ad | a in u.sees
  	//all u: User | some (u.sees & Ad)
  	all u: User | (u.follows.posts + Ad) in u.sees 
  	//all u: User | (u.follows.posts - User.posts - u.posts) in u.sees
}
    S47 in valid iff { //TODO
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User, a: Ad | a in u.sees
  	//all u: User | some (u.sees & Ad)
  	all u: User | (User.posts - u.posts) in u.sees 
  	//all u: User | (u.follows.posts - User.posts - u.posts) in u.sees
}
    S48 in valid iff { //TODO
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User, a: Ad | a in u.sees
  	//all u: User | some (u.sees & Ad)
  	all u: User | (User.posts - u.posts) not in u.sees 
  	//all u: User | (u.follows.posts - User.posts - u.posts) in u.sees
}
    S49 in valid iff { //TODO
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User, a: Ad | a in u.sees
  	all u1: User, u2: User | (u2 in u1.follows) implies (u2.posts in u1.sees)
  	all u: User | u.posts not in u.sees
	//all u: User, a: Ad | a in u.sees
  	//all u: User | some (u.sees & Ad)
  	//all u: User | (u.follows.posts) in u.sees 
  	//all u: User | u.posts not in u.sees
  	//all u: User | (u.posts - Ad) not in u.sees
  	//all u: User | (u.follows.posts - User.posts - u.posts) in u.sees
}
    S50 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all x: User | all y: Ad | y in x.sees
  all w: User | all p: Photo |
        (not p in Ad and (p in w.posts or some z: w.follows | p in z.posts)) => p in w.sees

}
    S51 in valid iff { //TODO
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User, a: Ad | a in u.sees
  	all u1: User, u2: User | (u2 in u1.follows) implies (u2.posts in u1.sees)
  	all u: User | (Photo - Ad) not in u.sees
	//all u: User, a: Ad | a in u.sees
  	//all u: User | some (u.sees & Ad)
  	//all u: User | (u.follows.posts) in u.sees 
  	//all u: User | u.posts not in u.sees
  	//all u: User | (u.posts - Ad) not in u.sees
  	//all u: User | (u.follows.posts - User.posts - u.posts) in u.sees
}
    S52 in valid iff { //TODO
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User, a: Ad | a in u.sees
  	all u1: User, u2: User | (u2 in u1.follows) implies (u2.posts in u1.sees)
  	all u: User, a: Ad | (Photo - a) not in u.sees
	//all u: User, a: Ad | a in u.sees
  	//all u: User | some (u.sees & Ad)
  	//all u: User | (u.follows.posts) in u.sees 
  	//all u: User | u.posts not in u.sees
  	//all u: User | (u.posts - Ad) not in u.sees
  	//all u: User | (u.follows.posts - User.posts - u.posts) in u.sees
}
    S53 in valid iff { //TODO
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User, a: Ad | (a in u.sees) and (u.posts not in u.sees)
  	all u1: User, u2: User | (u2 in u1.follows) implies (u2.posts in u1.sees)
  	//all u: User | (u.posts) not in u.sees
	//all u: User, a: Ad | a in u.sees
  	//all u: User | some (u.sees & Ad)
  	//all u: User | (u.follows.posts) in u.sees 
  	//all u: User | u.posts not in u.sees
  	//all u: User | (u.posts - Ad) not in u.sees
  	//all u: User | (u.follows.posts - User.posts - u.posts) in u.sees
}
    S54 in valid iff { //TODO
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User, a: Ad | (a in u.sees) or (u.posts not in u.sees)
  	all u1: User, u2: User | (u2 in u1.follows) implies (u2.posts in u1.sees)
  	//all u: User | (u.posts) not in u.sees
	//all u: User, a: Ad | a in u.sees
  	//all u: User | some (u.sees & Ad)
  	//all u: User | (u.follows.posts) in u.sees 
  	//all u: User | u.posts not in u.sees
  	//all u: User | (u.posts - Ad) not in u.sees
  	//all u: User | (u.follows.posts - User.posts - u.posts) in u.sees
}
    S55 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User, p: Photo |
    p in u.sees =>
      (p in u.posts and p !in Ad) or
      (p in Ad and p in (u.follows.posts + posts.Ad))
}
    S56 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User, a: Ad | a in u.sees
  	all disj u1: User, u2: User | (u2 in u1.follows) implies (u2.posts in u1.sees)
  	all u: User | (u.posts) not in Ad
	//all u: User, a: Ad | a in u.sees
  	//all u: User | some (u.sees & Ad)
  	//all u: User | (u.follows.posts) in u.sees 
  	//all u: User | u.posts not in u.sees
  	//all u: User | (u.posts - Ad) not in u.sees
  	//all u: User | (u.follows.posts - User.posts - u.posts) in u.sees
}
    S57 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User, a: Ad | a in u.sees
  	all disj u1: User, u2: User | (u2 in u1.follows) implies (u2.posts in u1.sees)
  	all u: User | u.sees not in Ad
	//all u: User, a: Ad | a in u.sees
  	//all u: User | some (u.sees & Ad)
  	//all u: User | (u.follows.posts) in u.sees 
  	//all u: User | u.posts not in u.sees
  	//all u: User | (u.posts - Ad) not in u.sees
  	//all u: User | (u.follows.posts - User.posts - u.posts) in u.sees
}
    S58 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User, a: Ad | a in u.sees
  	all disj u1: User, u2: User | (u2 in u1.follows) implies (u2.posts in u1.sees)
  	all u: User | u.sees not in u.posts
	//all u: User, a: Ad | a in u.sees
  	//all u: User | some (u.sees & Ad)
  	//all u: User | (u.follows.posts) in u.sees 
  	//all u: User | u.posts not in u.sees
  	//all u: User | (u.posts - Ad) not in u.sees
  	//all u: User | (u.follows.posts - User.posts - u.posts) in u.sees
}
    S59 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User, a: Ad | a in u.sees
  	all disj u1: User, u2: User | (u2 in u1.follows) implies (u2.posts in u1.sees)
  	all u: User | (u.sees & Ad) not in u.posts
	//all u: User, a: Ad | a in u.sees
  	//all u: User | some (u.sees & Ad)
  	//all u: User | (u.follows.posts) in u.sees 
  	//all u: User | u.posts not in u.sees
  	//all u: User | (u.posts - Ad) not in u.sees
  	//all u: User | (u.follows.posts - User.posts - u.posts) in u.sees
}
    S60 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User, a: Ad | a in u.sees
  	all disj u1: User, u2: User | (u2 in u1.follows) implies (u2.posts in u1.sees)
  	all u: User | all p: u.posts | (p not in Ad) implies (p not in u.sees)
  	all u: User | all p: u.posts | (p in Ad) implies (p in u.sees)
	//all u: User, a: Ad | a in u.sees
  	//all u: User | some (u.sees & Ad)
  	//all u: User | (u.follows.posts) in u.sees 
  	//all u: User | u.posts not in u.sees
  	//all u: User | (u.posts - Ad) not in u.sees
  	//all u: User | (u.follows.posts - User.posts - u.posts) in u.sees
}
    S61 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	//all u: User, a: Ad | a in u.sees
  	//all disj u1: User, u2: User | (u2 in u1.follows) implies (u2.posts in u1.sees)
  	all u: User | all p: u.posts | (p not in Ad) implies (p not in u.sees)
  	all u: User | all p: u.posts | (p in Ad) implies (p in u.sees)
	//all u: User, a: Ad | a in u.sees
  	//all u: User | some (u.sees & Ad)
  	//all u: User | (u.follows.posts) in u.sees 
  	//all u: User | u.posts not in u.sees
  	//all u: User | (u.posts - Ad) not in u.sees
  	//all u: User | (u.follows.posts - User.posts - u.posts) in u.sees
}
    S62 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User | all a: Ad | a in u.sees
  	all u: User | all p: u.posts | p not in u.sees
  	//all u: User, a: Ad | a in u.sees
  	//all disj u1: User, u2: User | (u2 in u1.follows) implies (u2.posts in u1.sees)
  	//all u: User | all p: u.posts | (p not in Ad) implies (p not in u.sees)
  	//all u: User | all p: u.posts | (p in Ad) implies (p in u.sees)
	//all u: User, a: Ad | a in u.sees
  	//all u: User | some (u.sees & Ad)
  	//all u: User | (u.follows.posts) in u.sees 
  	//all u: User | u.posts not in u.sees
  	//all u: User | (u.posts - Ad) not in u.sees
  	//all u: User | (u.follows.posts - User.posts - u.posts) in u.sees
}
    S63 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User | some a: Ad | a in u.sees
  	all u: User | all p: u.posts | (p in Ad) or (p not in u.sees)
  	//all u: User, a: Ad | a in u.sees
  	//all disj u1: User, u2: User | (u2 in u1.follows) implies (u2.posts in u1.sees)
  	//all u: User | all p: u.posts | (p not in Ad) implies (p not in u.sees)
  	//all u: User | all p: u.posts | (p in Ad) implies (p in u.sees)
	//all u: User, a: Ad | a in u.sees
  	//all u: User | some (u.sees & Ad)
  	//all u: User | (u.follows.posts) in u.sees 
  	//all u: User | u.posts not in u.sees
  	//all u: User | (u.posts - Ad) not in u.sees
  	//all u: User | (u.follows.posts - User.posts - u.posts) in u.sees
}
    S64 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | all p : Photo | p not in Ad and p in u.sees implies p not in u.posts
}
    S65 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User | lone a: Ad | a in u.sees
  	all u: User | all p: u.posts | (p not in Ad) implies (p not in u.sees)
  	//all u: User | 
	//all disj u1: User, u2: User | (u2 in u1.follows) implies (u2.posts in u1.sees)
  	//all u: User | all a: Ad | a in u.sees
  	//all u: User | all p: u.posts | (p in Ad) or (p not in u.sees)
  	//all u: User, a: Ad | a in u.sees
  	//all disj u1: User, u2: User | (u2 in u1.follows) implies (u2.posts in u1.sees)
  	//all u: User | all p: u.posts | (p not in Ad) implies (p not in u.sees)
  	//all u: User | all p: u.posts | (p in Ad) implies (p in u.sees)
	//all u: User, a: Ad | a in u.sees
  	//all u: User | some (u.sees & Ad)
  	//all u: User | (u.follows.posts) in u.sees 
  	//all u: User | u.posts not in u.sees
  	//all u: User | (u.posts - Ad) not in u.sees
  	//all u: User | (u.follows.posts - User.posts - u.posts) in u.sees
}
    S66 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User | all p: Photo | (posts.p in u.follows) implies (p in u.sees)
  	//all u: User | all a: Ad | a in u.sees
  	//all u: User | all p: u.posts | (p in Ad) or (p not in u.sees)
  	//all u: User, a: Ad | a in u.sees
  	//all disj u1: User, u2: User | (u2 in u1.follows) implies (u2.posts in u1.sees)
  	//all u: User | all p: u.posts | (p not in Ad) implies (p not in u.sees)
  	//all u: User | all p: u.posts | (p in Ad) implies (p in u.sees)
	//all u: User, a: Ad | a in u.sees
  	//all u: User | some (u.sees & Ad)
  	//all u: User | (u.follows.posts) in u.sees 
  	//all u: User | u.posts not in u.sees
  	//all u: User | (u.posts - Ad) not in u.sees
  	//all u: User | (u.follows.posts - User.posts - u.posts) in u.sees
}
    S67 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all disj u1: User, u2: User | (u1 in u2.follows) implies (u1.posts in u2.sees)
  	all u: User | all p: u.posts | (p not in Ad) implies (p not in u.sees)
  	//all u: User | all a: Ad | a in u.sees
  	//all u: User | all p: u.posts | (p not in Ad) implies (p not in u.sees)
  	//all u: User | 
	//all disj u1: User, u2: User | (u2 in u1.follows) implies (u2.posts in u1.sees)
  	//all u: User | all a: Ad | a in u.sees
  	//all u: User | all p: u.posts | (p in Ad) or (p not in u.sees)
  	//all u: User, a: Ad | a in u.sees
  	//all disj u1: User, u2: User | (u2 in u1.follows) implies (u2.posts in u1.sees)
  	//all u: User | all p: u.posts | (p not in Ad) implies (p not in u.sees)
  	//all u: User | all p: u.posts | (p in Ad) implies (p in u.sees)
	//all u: User, a: Ad | a in u.sees
  	//all u: User | some (u.sees & Ad)
  	//all u: User | (u.follows.posts) in u.sees 
  	//all u: User | u.posts not in u.sees
  	//all u: User | (u.posts - Ad) not in u.sees
  	//all u: User | (u.follows.posts - User.posts - u.posts) in u.sees
}
    S68 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1,u2 : User, p : Photo | p in u1.sees implies u2 in u1.follows and p in u2.posts or p in u1.posts
  	all u1,u2 : User, ad : Ad, p : Photo | ad in u1.sees implies ad in u2.posts or ad in u1.posts
}
    S69 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u0,u1: User | u0.sees in u1.posts
	
}
    S70 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u0,u1: User | u0.sees in u1.posts
	some p: Photo | User.follows in posts.p
}
    S71 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User | u.sees in (Ad + u.follows.posts + u.posts)

}
    S72 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User, ad:Ad| ad in u.sees
  	all p: Photo - Ad, u: User | p in u.posts
}
    S73 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all ad: Ad | all u: User | ad in u.sees
	all p: Photo - Ad | some u:User | p in u.sees

}
    S74 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User, p: Photo | p in u.sees

}
    S75 in valid iff {
	// Users can see ads posted by everyone, 
  	all u : User, add : Ad | add in u.sees 
	// but only see non ads posted by followed users.
  	all u : User, p : Photo |
  		// para cada foto que o user vê e não seja um add, implica:
  		(p in u.sees and not p in Ad) implies
  		// que deve existir algum user que postou a foto e é seu seguidor
  		some user : User | p in user.posts and user in u.follows
  

}
    S76 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  some ad: Ad | all u: User | ad in u.sees
	all p: Photo - Ad | all u:User | p in u.sees implies some v: u.follows | p in v.posts

}
    S77 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  
    // all y:Photo, x:User | x->y in sees implies (y in Ad) or 
    //         (all z:User | z->y in  posts implies x->z in follows)

    // all y:Photo, x:User | x in sees.y implies (y in Ad) or 
    //       (all z:User | z in posts.y implies x in follows.z)

    // all y:Photo, x:User | x in sees.y implies (y in Ad) or (y in x.follows.posts)

      all x:User | x.sees in (x.follows.posts & Ad)
  
  	// all p : User | p.sees - Ad in p.follows.posts


}
    S78 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all ads:Ad | one p : User | ads in p.sees

}
    S79 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  
    // all y:Photo, x:User | x->y in sees implies (y in Ad) or 
    //       (all z:User | z->y in  posts implies x->z in follows)

    // all y:Photo, x:User | x in sees.y implies (y in Ad) or 
    //       (all z:User | z in posts.y implies x in follows.z)

    // all y:Photo, x:User | x in sees.y implies 
    //                      (y in Ad) or (y in x.follows.posts)
     
	all u : User, a : Ad | u->a in sees implies
	    some u1 : User | u1->a in posts and u->u1 in follows
  
    // all x : User | x.sees - Ad in x.follows.posts
}
    S80 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  
    // all y:Photo, x:User | x->y in sees implies (y in Ad) or 
    //       (all z:User | z->y in  posts implies x->z in follows)

    // all y:Photo, x:User | x in sees.y implies (y in Ad) or 
    //       (all z:User | z in posts.y implies x in follows.z)

    // all y:Photo, x:User | x in sees.y implies 
    //                      (y in Ad) or (y in x.follows.posts)
     
	all u : User, a : Ad | u->a in sees implies
	    some u1 : User | u1->a in posts and u1->u in follows
  
    // all x : User | x.sees - Ad in x.follows.posts
}
    S81 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  
    // all y:Photo, x:User | x->y in sees implies (y in Ad) or 
    //       (all z:User | z->y in  posts implies x->z in follows)

    // all y:Photo, x:User | x in sees.y implies (y in Ad) or 
    //       (all z:User | z in posts.y implies x in follows.z)

    // all y:Photo, x:User | x in sees.y implies 
    //                      (y in Ad) or (y in x.follows.posts)
     
	all u : User | u.sees in Ad or some posts.(u.sees) & u.follows
  }
    S82 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all x : User, y : Ad | y in x.sees
  all x : User, y : Photo | y in x.sees implies posts.y in x.follows 
  

}
    S83 in valid iff {
	// Users can see ads posted by everyone,
  	all u : User, a : Ad | a in sees.u
	// but only see non ads posted by followed users.
  	all u1,u2 : User, p : Photo | p not in Ad and p in u1.sees implies u2 in follows.u1
}
    S84 in valid iff {
	// Users can see ads posted by everyone,
  	all u : User, a : Ad | a in u.sees
	// but only see non ads posted by followed users.
  	all u1,u2 : User, p : Photo | p not in Ad and p in u1.sees and p in u2.posts implies u2 in follows.u1
}
    S85 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | some x: u.follows | u.sees in x.posts

}
    S86 in valid iff {
	all u: User, p: Photo |
  p in u.sees <=> (p in Ad) or (p in u.follows.posts)

}
    S87 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u,v: User | all a: Ad | a in u.sees and v in u.follows implies v.posts in u.sees

}
    S88 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u,v: User | all a: Ad | a in v.posts and a in u.sees and v in u.follows implies v.posts in u.sees

}
    S89 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | all x: u.follows | all a: Ad | u.sees in x.posts

}
    S90 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | all x: u.follows | u.sees in x.posts

}
    S91 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	 all u: User, p: Photo | p in u.sees <=> (p in u.posts && p not in Ad) || (p in Ad)
}
    S92 in valid iff {
  // Users can see ads posted by everyone, 
  // but only see non ads posted by followed users.
  all user: User | all fuser : user.follows | user.sees in fuser.posts
  all user: User | all ad: Ad | ad in user.sees
  
}
    S93 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all x:User, y: x.sees | y not in Ad implies some z:User | z in x.follows
  // all x:User, y:x.sees |
  // all x:Photo - Ad |

}
    S94 in valid iff {
  // Users can see ads posted by everyone, 
  // but only see non ads posted by followed users.
  all user: User | all fuser : user.follows | all ad: Ad |user.sees in fuser.posts implies ad not in user.sees else ad in user.sees
}
    S95 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | posts.(u.sees - Ad) in follows.u 
}
    S96 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User | some(u.sees & Photo-Ad)
}
    S97 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | some x: u.follows | all a: Ad | u.sees in x.posts <=> u.sees in a

}
    S98 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | some x: u.follows | all a: Ad | u.sees not in x.posts implies u.sees in a

}
    S99 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all x: User, p : Photo | Ad in x.sees or posts.p in x.follows

}
    S100 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | some x: u.follows | all a: Ad | u.sees in x.posts <=> !(u.sees in a)

}
    S101 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | some x: u.follows | all a: Ad | u.sees in x.posts || !(u.sees in a)

}
    S102 in valid iff {
  // Users can see ads posted by everyone, 
	//all u: User, p:Photo | some u.posts in Ad implies u in u.sees
	//all u: User, p:Photo | u in sees.p implies p in Ad and 
	//all u: User, p: Photo | u in sees.p implies u.posts in Ad   
  	//all u: User, p:Photo| u in sees.Ad implies p in u.posts   	
  	//all u: User, p:Photo| p in Ad implies 

  
	//all u: User, p: Photo | some u.posts implies u not in u.follows   
	//all u: User, p: Photo | p in Ad implies sees.p not in u.follows
  	//all u: User, p:Photo | u in sees.p implies p in Ad
  
  // but only see non ads posted by followed users.
  	//all u: User, p: Photo | p not in Ad implies posts.p in u.follows
  
	//all u: User, p:Photo | p not in Ad and p in u.sees implies u in u.follows	
  //all u: User|some p: Photo - Ad | p in u.sees impli
  
	all u: User, a: Ad | a in posts.u => a in sees.u
	all u: User, p: Photo-Ad| p in u.sees implies u.posts in u.follows
  
}
    S103 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | one x: u.follows | all a: Ad | u.sees in x.posts || !(u.sees in a)

}
    S104 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | one x: u.follows | all a: Ad | u.sees not in x.posts implies u.sees in a

}
    S105 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | one x: u.follows | all a: Ad | u.sees in x.posts <=> u.sees in a

}
    S106 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | one x: u.follows | one a: Ad | u.sees not in x.posts implies u.sees in a

}
    S107 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | one x: u.follows | u.sees not in x.posts implies u.sees in Ad

}
    S108 in valid iff {
	all u:User, p:Photo | p in u.sees and u not in u.follows implies p in Ad
  	all u:User, p:Photo | p in u.sees implies u in u.follows else u not in u.follows 
  
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.

}
    S109 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u:User | u.sees in u.follows.posts or u.sees in Ad
}
    S110 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | one x: u.follows | u.sees not in u.follows.posts implies u.sees in Ad

}
    S111 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
   all u:User, p : Photo |  some(u.sees - Ad) implies  some(u.follows & posts.p)
  

}
    S112 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | one x: u.follows | u.sees not in x.posts implies u.sees = Ad

}
    S113 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u:User | (Ad + u.follows.posts - u.posts) = u.sees 
}
    S114 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | all p : (u.posts-Ad) | u not in User.follows implies p  not in User.sees   
}
    S115 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u:User | u.sees in (u.follows.posts - Ad)  

}
    S116 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u:User, p:Photo | p in u.sees and p in u.follows.posts implies p not in Ad else p in Ad 


}
    S117 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u : User | Ad & u.follows.posts in u.sees

}
    S118 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all o,e : User | all a : Ad | o->a in posts implies e->a in sees
    all p : Photo | some a,b : User | b->p in posts and a->p in sees implies a->b in follows 

}
    S119 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all e : User | all a : Ad |  e->a in sees
    all p : Photo | all a : User | some b : User | a->p in posts and b->p in sees implies b->a in follows 

}
    S120 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all user: User | all fusers: user.follows | all ad: Ad | fusers.sees in user.posts  

}
    S121 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all ad : Ad, photo : Photo | lone sees.ad & follows.sees.photo
}
    S122 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all e : User | all a : Ad |  e->a in sees
    all p : Photo | all a : User | some b : User | all e : Ad | p!=e implies a->p in posts and b->p in sees implies b->a in follows 

}
    S123 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User, p : Photo | u->p in sees implies p= Ad
}
    S124 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all e : User | all a : Ad |  e->a in sees
    some p : Photo | all a : Ad | some e : User | some d : User | p != a and e->p in posts and d->p in sees implies d->e in follows

}
    S125 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | all p : u.sees | all a : Ad | all f : u.follows | p in a or p in f.posts 
}
    S126 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  
  //all u : User, a : u.sees-Ad | some posts.a & u.follows

	all p : Photo | p in User.posts implies p in User.sees

}
    S127 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User , ad : Ad | ad in u.sees
  all u : User | u.follows.posts = u.sees

}
    S128 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User | all ad : Ad  | ad in u.sees
  no u : User | u.sees = u.follows.posts
}
    S129 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User | all u1:User | all p : Photo | all a : Ad | a in u.sees and p in u.sees implies a in u1.posts and u1 in u.follows or u = u1

}
    S130 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all x : User | all a : Ad | x.sees in Ad
}
    S131 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all e : User | all a : Ad |  e->a in sees
    all p : Photo | all a : Ad | some e : User | some d : User | p != a and e->p in posts and d->p in sees implies d->e in follows

}
    S132 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User | all ad : Ad  | ad in u.sees
  all u : User | u.sees = u.follows.posts and u.sees = u.posts  
}
    S133 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | all a : Ad | a in u.sees and u.follows.posts in u.sees
}
    S134 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all user: User | all fusers: follows.user | all ad: Ad | fusers.sees in user.posts and user.sees in user.posts

}
    S135 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User, p : Photo | p in Ad and p not in u.sees implies posts.p in u.follows
}
    S136 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | all a: Ad | a in u.sees implies (some u1: User | a in u1.posts and (u1 in u.follows or u = u1))
  all u: User | all p: Photo | p in u.sees implies (some u1: User | p in u1.posts and (u1 in u.follows or u = u1))
}
    S137 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | all p : u.sees | all a : Ad | all f : u.follows | p in u.sees implies ( p in a and not p in f.posts) or ( p in f.posts and not p in a )
}
    S138 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1,u2:User, p:Photo | (p in Ad => p in u1.sees)
  						&& (u2 in u1.follows => not(p in (u2.posts & Ad) => p in u1.sees))
}
    S139 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all ad : Ad | some sees.ad
    all photo : User.follows | some sees.photo
}
    S140 in valid iff {
    // Users can see ads posted by everyone, 
    // but only see non ads posted by followed users.
  all user: User |
    user.sees = (user.posts - Ad) + (User.follows.posts - Ad)
}
    S141 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User | all u1:User | all p : Photo | all a : Ad | a in u.sees and u1!= u and p in u.sees implies u1 in u.follows and p in u1.posts

}
    S142 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u:User,ad:Ad| ad in u.sees and posts.(u.sees - ad) in u.follows

}
    S143 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | all p : u.sees | all a : Ad | all f : u.follows | (( p in a ) or ( p in f.posts ) ) and not p in u.posts
}
    S144 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all e : User | all a : Ad |  e->a in sees
    all a : Ad | all p : Photo | all e,d : User | (e!=d and e->p in posts and d->p in sees) implies d->e in follows

}
    S145 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User | all u1:User | all p : Photo | all a : Ad | a in u.sees or p in u.sees implies p in u1.posts and u1 in u.follows

}
    S146 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all e : User | all a : Ad |  e->a in sees
    all p : Photo | all e,d : User | (e!=d and e->p in posts and d->p in sees) implies d->e in follows

}
    S147 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all user: User | all fusers: follows.user | all ad: Ad | (user.sees in user.posts) implies user.posts in Ad and fusers.sees in user.posts

}
    S148 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User, a : Ad | a in u.sees
  all u1,u2 : User, p : Photo | p in u1.sees implies u2 in u1.follows or p in u1.posts
}
    S149 in valid iff {
    // Users can see ads posted by everyone, 
    // but only see non ads posted by followed users.
  all user: User |
    user.sees =  (User.follows.posts - Ad)
}
    S150 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all e : User | some a : Ad |  e->a in sees
    all p : Photo | all e,d : User | (e!=d and e->p in posts and d->p in sees) implies d->e in follows

}
    S151 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all user: User | all fusers: follows.user | all ad: Ad | user.sees in ad and (fusers.sees in user.posts)

}
    S152 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | all p : u.sees  | (( p in Ad ) or ( p in u.follows.posts ) ) and (not p in u.posts)
}
    S153 in valid iff {
    // Users can see ads posted by everyone, 
    // but only see non ads posted by followed users.
  all user: User |
    user.sees = (user.posts) + (User.follows.posts - Ad)
}
    S154 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
all x: User | all y: Photo | x-> y in sees and y in Ad or
  all z: User | z->y in posts implies x->z in follows
}
    S155 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User | all u1:User | all p : Photo | all a : Ad | a in u.sees and a not in u.posts and p in u.sees implies u1 in u.follows and p in u1.posts

}
    S156 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all e : User | some a : Ad |  e->a in sees
    all p : Photo | all e,d : User | (e->p in posts and d->p in sees) implies d->e in follows

}
    S157 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1,u2 : User, p : Photo | p in u2.posts and p in u1.sees implies u2 in u1.follows else p in u1.posts
  	all u1,u2 : User, ad : Ad, p : Photo | ad in u2.posts implies ad in u1.sees
}
    S158 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User | u.sees = (u.follows.posts - Ad)
}
    S159 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User | all u1:User | all p : Photo | some a : Ad | a in u.sees and p in u.sees implies u1 in u.follows and p in u1.posts

}
    S160 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | all p : Photo | p in u.sees implies (p in Ad or u in posts.p)

}
    S161 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User | all u1:User | some p : Photo | some a : Ad | a in u.sees and p in u.sees implies u1 in u.follows and p in u1.posts

}
    S162 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
   all u: User, p: Photo |
        (p in Ad) or (some f: u.follows | p in f.posts) implies p in u.sees
	
}
    S163 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  some u : User | some u1:User | some p : Photo | some a : Ad | a in u.sees and p in u.sees implies u1 in u.follows and p in u1.posts

}
    S164 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | (posts.Ad + u.follows.posts) in u.sees and (User.posts - (posts.Ad + u.follows.posts)) not in u.sees
}
    S165 in valid iff {
    // Users can see ads posted by everyone, 
    // but only see non ads posted by followed users.
  all user: User |
    user.sees in (user.posts) + (User.follows.posts) +Ad
}
    S166 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User, i : Photo | u->i in sees implies i = Ad or some v : User | u->v in follows and v->i in posts
}
    S167 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User | all u1:User | some p : Photo | some a : Ad | (a in u.sees) and (p in u.sees implies u1 in u.follows and p in u1.posts)

}
    S168 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all user : User | user.sees in Ad and some user.follows.posts
}
    S169 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	//all u : User | u.sees in u.follows.posts + Ad
    all u: User, a: Photo | u in sees.a implies a in Ad or 
  	some u1: User, a: Photo | u1 in posts.a and u in follows.u1
}
    S170 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User, i : Photo | u->i in sees implies i = Ad or some v : User | u->v in follows and v->i in posts or u->i in posts
}
    S171 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User | all u1:User | some p : Photo | all a : Ad | (a in u.sees) and (p in u.sees implies u1 in u.follows and p in u1.posts and u!=u1)

}
    S172 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all e : User | some v : User | some a : Ad |  v->a in posts implies e->a in sees
    all p : Photo | all e,d : User | (e->p in posts and d->p in sees) implies d->e in follows

}
    S173 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User | some u1:User | some p : Photo | some a : Ad | (a in u.sees) and (p in u.sees implies u1 in u.follows and p in u1.posts and u!=u1)

}
    S174 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | Ad in u.sees
  	all u : User | u.follows.posts in u.sees
  	all u : User | (User.posts - Ad - u.follows.posts - u.posts) not in u.sees
}
    S175 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all a:Ad | some u:User | a->u in sees
  	all p:Photo, u:User | sees.p = follows.u 

}
    S176 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | all p: Photo | all a: Ad | p in u.sees and p in a

}
    S177 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1, u2: User | all p: Photo | p in u2.posts and p in u1.sees
  	all u1, u2: User | all a: Ad | a in u2.posts and u2 in u1.follows implies a in u1.sees

}
    S178 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1, u2: User | all a: Ad | a in u2.posts and a in u1.sees
  	all u1, u2: User | all p: Photo | p in u2.posts and u2 in u1.follows implies p in u1.sees

}
    S179 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1, u2: User | all a: Ad | a in u2.posts and a in u1.sees
  	all u1, u2: User | all p: Photo | p in u2.posts and u2 in u1.follows <=> p in u1.sees

}
    S180 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User, a: Ad | a in u.posts implies a in u.sees
  all u1, u2: User, p: Photo | p in u2.posts and u2 in u1.follows implies p in u1.sees
}
    S181 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1, u2: User | all a: Ad | u1 != u2 and a in u2.posts and a in u1.sees
  	all u1, u2: User | all p: Photo | u1 != u2 and p in u2.posts and u2 in u1.follows implies p in u1.sees

}
    S182 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1, u2: User | all a: Ad | a in u2.posts and a in u1.sees
  	all u1, u2: User | all p: Photo | p in u2.posts and (u2 in u1.follows or u1 = u2) implies p in u1.sees

}
    S183 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1, u2: User | all a: Ad | a in u2.posts and a in u1.sees and u1 not in Influencer
  	all u1, u2: User | all p: Photo | p in u2.posts and u2 in u1.follows implies p in u1.sees

}
    S184 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1, u2: User | all a: Ad | a in u2.posts and a in u1.sees
  	all u1, u2: User | all p: Photo | p in u2.posts and (u2 in u1.follows and u1 not in Influencer and u2 not in Influencer) implies p in u1.sees

}
    S185 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1, u2: User | all a: Ad | a in u2.posts and a in u1.sees
  	all u1, u2: User | all p: Photo | p in u2.posts and (u2 in u1.follows or (u1 not in Influencer and u2 not in Influencer)) implies p in u1.sees

}
    S186 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1, u2: User | all a: Ad | a in u2.posts and a in u1.sees
  	all u1, u2: User | all p: Photo | p in u2.posts and (u2 in u1.follows or (u1 in Influencer and u2 in Influencer)) implies p in u1.sees

}
    S187 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1, u2: Influencer | all a: Ad | a in u2.posts and a in u1.sees
  	all u1, u2: Influencer | all p: Photo | p in u2.posts and u2 in u1.follows implies p in u1.sees

}
    S188 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1, u2: User | all a: Ad | u1 != u2 and a in u2.posts and a in u1.sees
  	all u1, u2: User | all p: Photo | u1 != u2 and (p in u1.posts and u2 in u1.follows) implies p in u1.sees
  

}
    S189 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1, u2: User | all a: Ad | u1 != u2 and a in u2.posts and a in u1.sees
  	all u1, u2: User | all p: Photo | u1 != u2 and (p in u2.posts and p in u1.sees) implies u2 in u1.follows
  

}
    S190 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User, p: Photo |
		p in u.sees <=>
		(p in Ad && p not in u.posts) ||
		(p not in Ad && (p in u.follows.posts or p in u.posts))

}
    S191 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all a : Ad,  u : User | a in u.sees
  	all u : User, p : Photo-Ad | p in u.sees implies p in u.follows.posts+u.posts
}
    S192 in valid iff {
  all u: User, p: Photo | 
    (p in u.posts && p not in Ad) => (p in u.sees) 
}
    S193 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | u.sees = Ad + u.follows.((^(posts)) + ((this.@User + this.@Photo + this.@Day + Int + String) <: iden))

}
    S194 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User |
		u.sees = u.posts - Ad
}
    S195 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	User.sees & Ad = Ad and
  	(all p: Photo|all u: User|
  	(p not in Ad and p in ((u.follows).posts)) implies p in u.sees)
}
    S196 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | 
    all p: Photo | 
      (p in Ad and p not in u.posts implies p in u.sees) and
      (p not in Ad implies (some f: u.follows | p in f.posts) implies p in u.sees)
}
    S197 in valid iff {
  // Ads are visible to all users
  all u: User, a: Ad | a in u.sees
  all u: User | #(u.sees & u.posts) = 0

  // Non-ads are visible only if posted by followed users
  all u: User, p: Photo - Ad | p in u.follows.posts => p in u.sees
}
    S198 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	(all u: User| all p: Photo|
	(p in Ad implies p in u.sees) and 
  	(p in (u.follows).posts) implies p in u.sees and #(u.sees & u.posts) = 0


)
}
    S199 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  
  all u:User, a:Ad |
  	a in u.sees implies  one other:User-u | a in other.posts && other not in u.follows 

}
    S200 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  
  all u:User, p:Photo , other:User-u|
	p in u.sees implies ((p in other.posts) && ( other in u.follows)) or u.sees in Ad
}
    S201 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  
  all u : User, cont : Photo-Ad | (u.follows.posts & cont) + Ad = u.sees
  

}
    S202 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  
  all u : User, cont : Photo-Ad | (u.follows.posts & cont) + Ad in u.sees
  

}
    S203 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  
  all u : User, cont : Photo-Ad, p : Photo | p in u.sees implies (p in Ad or u.follows.posts in cont)
  

}
    S204 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User, p : Photo | u in sees.p implies p in Ad or
  	some u1 : User | u1 in sees.p implies (u1 in posts.p and u1 in follows.u)
}
    S205 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u,u1 : User - Influencer | (u1.posts & Ad in u.sees) and (u1 in u.follows implies u1.posts - Ad in u.sees) 

}
    S206 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all a: Ad | some sees.a
  	all p: Photo - Ad | all u: User | u->p in sees implies posts.p in u.follows

}
    S207 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u1: User | one u2: User | all p: Photo | p in u1.sees implies (p in Ad) or (p in u2.posts and u2 in u1.follows)

}
    S208 in valid iff {
	// Users can see ads posted by everyone, 
  	all disj u,u1 : User | all p : u.sees | p not in Ad implies p in u1.posts and u1 in u.follows
	// but only see non ads posted by followed users.
	
}
    S209 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	
	all u : User, a : u.sees | a = Ad + u.follows.posts
}
    S210 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all u:User, u2:User | u2 in u.follows => {
        all a:Ad | a in u2.posts => a not in u.sees else {
            a in u.sees
        }
    }
}
    S211 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all u:User, u2:User | u2 in u.follows => {
        all a:Ad | a in u2.posts => a not in u.sees else {
            a in u.sees
        }
    }
        else{
            all p:Photo | p in u2.posts => p in u.sees

        }
}
    S212 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all u:User, u2:User | u2 in u.follows => {
        all a:u2.posts | a not in u.sees
    }
    else{
        all p:Photo | p in u2.posts => p in u.sees

    }
}
    S213 in valid iff {
	// Users can see ads posted by everyone,
	// but only see non-ads posted by followed users.

	all u: User, p: Photo | (p in u.sees) implies
		((p in Ad) && (all v: User | p in v.posts)) ||
		((p not in Ad) && (some v: User | (v in u.follows) && (p in v.posts)))
}
    S214 in valid iff {
	// Users can see ads posted by everyone,
	// but only see non-ads posted by followed users.

	all u: User, p: Photo | (p in u.sees) implies
		((p in Ad) && (some v: User | (v not in u.follows) && (p in v.posts))) ||
		((p not in Ad) && (some v: User | (v in u.follows) && (p in v.posts)))
}
    S215 in valid iff {
	// Users can see ads posted by everyone,
	// but only see non-ads posted by followed users.

	all u: User, p: Photo | (p in u.sees) implies
		((p in Ad) && (all v: User | (v not in u.follows) && (p in v.posts))) ||
		((p not in Ad) && (all v: User | (v in u.follows) && (p in v.posts)))
}
    S216 in valid iff {
	// Users can see ads posted by everyone,
	// but only see non-ads posted by followed users.

	all u: User, p: Photo | (p in u.sees) implies
		((p in Ad) && (all v: User | (v not in u.follows) => (p in v.posts))) ||
		((p not in Ad) && (some v: User | (v in u.follows) => (p in v.posts)))
}
    S217 in valid iff {
	// Users can see ads posted by everyone,
	// but only see non-ads posted by followed users.

	all u: User, p: Photo | (p in u.sees) implies
		((p in Ad) && (all v: User  - u| (v not in u.follows) => (p in v.posts))) ||
		((p not in Ad) && (some v: User - u  | (v in u.follows) => (p in v.posts)))
}
    S218 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User, a : Ad | a in u.sees
  	all u : User | all p : Photo | one u2:User | 
  			p in u.sees => (p in Ad or (p in u2.posts and u2 in u.follows))
}
    S219 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u : User | all p : Photo | one u2:User | 
  			p in u.sees => (p in Ad or (p in u2.posts and u2 in u.follows))
}
    S220 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u : User | all p : Photo | one u2:Influencer | 
  			p in u.sees => (p in Ad or (p in u2.posts and u2 in u.follows))
}
    S221 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u : User | all p : Photo | one u2:User | 
  			p in u.sees => (p in Ad or p in u.posts or 
              		(p in u2.posts and u2 in u.follows))
}
    S222 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all u : User | u.sees in Ad
  	all disj u,u1 : User | some p : u1.posts | u1 in u.follows and  p in u.sees and p not in Ad

}
    S223 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | all a: Ad | a in u.sees
  and
  all u: User | all p: Photo - Ad | p in u.sees implies (some u2: User | p in u2.posts and u2 in u.follows)

}
    S224 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all a : Ad | all u : User | u in sees.a or all p : Photo - Ad | u in sees.p implies u in follows.(posts.p)
}
    S225 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User, p : Photo-Ad | u->Ad in sees or (u->p in sees and u->(posts.p) in follows)
}
    S226 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u : User | all a: Ad | a in u.sees
	all u : User | all p : Photo | all a: Ad | p not in a and p not in u.follows.posts and p not in u.posts => p not in u.sees
}
    S227 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | Ad in u.sees
  	all u : User | (u.follows-Ad) in u.sees 
}
    S228 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | all a : Ad | Ad in u.sees implies (a not in u.follows.posts) 
  	
  
}
    S229 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User, a: Ad | a in u.sees && a not in u.follows.posts

}
    S230 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u1:User, u2:User, p:Photo | p in Ad => p in u1.sees && u2.sees in u1.posts => u2 in u1.follows

}
    S231 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u1:User, u2:User, p:Photo | p in Ad => p in u1.sees && u1 in u2.follows => u2.sees in u1.posts
}
    S232 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | all a : Ad | a in u.sees
  	all u : User | one p : Photo | (p not in Ad) implies (p not in u.sees)
}
    S233 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | all a : Ad | a in u.sees
  	all u : User | all p : Photo | (p not in Ad) implies (p not in u.follows.posts)
}
    S234 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
   all u: User | u.sees = u.posts + Ad
}
    S235 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all p : Photo, u1, u2 : User | p not in Ad and p in u1.sees and p in u2.posts iff u2 in u1.follows  
}
    S236 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	
  	all u : User | all p : Photo | u in sees.p implies p in Ad or some u1 : User | u1 in posts.p and u.follows in u1
	
  	all u : User | all p: Photo | u in sees.p implies p in Ad or some posts.p & u.follows

}
    S237 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all p : Photo-Ad | some (sees.p) implies one (sees.p).posts
}
    S238 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all user1: User, user2: User, ad: user1.posts & Ad | ad in user2.sees
    all user1: User, user2: user1.follows, ad: user2.posts | ad not in user1.sees
}
    S239 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all user1: User, user2: User - user1.follows, ad: user1.posts & Ad | ad in user2.sees
    all user1: User, user2: user1.follows, ad: user2.posts | ad not in user1.sees
}
    S240 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all user1: User, user2: User - user1.follows - user1, ad: user1.posts & Ad | ad in user2.sees
    all user1: User, user2: user1.follows, ad: user2.posts | ad not in user1.sees
}
    S241 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	//all user1: User, user2: User - user1.follows - user1, ad: user1.posts & Ad | ad in user2.sees
    //all user1: User, user2: user1.follows, ad: user2.posts | ad not in user1.sees
  
  	all u1: User, u2: u1.follows, p: u2.posts | p in u1.sees && p not in Ad
    all u1: User, u2: User - u1.follows, p: u2.posts & Ad | p in u1.sees 
  	
}
    S242 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  
  	all u1: User, u2: u1.follows, p: u2.posts | p in u1.sees && p not in Ad
    all u1: User, u2: User - u1.follows - u1, p: u2.posts & Ad | p in u1.sees 
  	
}
    S243 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  
  	all u1: User, u2: u1.follows + u1, p: u2.posts | p in u1.sees && p not in Ad
    all u1: User, u2: User - u1.follows - u1, p: u2.posts & Ad | p in u1.sees 
  	
}
    S244 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  
  	all u1: User, u2: User, p: u2.posts | u2 in u1.follows && p in Ad => p not in u1.sees
  	all u1: User, u2: User, p: u2.posts | u2 not in u1.follows && p in Ad => p in u1.sees
  	
}
    S245 in valid iff {
  // Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all u: User | 
        // Users can see all ads
        all a: Ad | a in u.sees and
        // Users can only see non-ads posted by followed users
        all p: Photo - Ad | p in u.sees iff p in (u.follows).posts
}
    S246 in valid iff {
    all u: User | 
        // Users can see all ads
        all a: Ad | a in u.sees and
        // Users can only see non-ads posted by followed users, which implicitly includes their own posts
        all p: Photo - Ad | p in u.sees iff p in (u.follows + u).posts
}
    S247 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
   all u: User, p: Photo |
    (p in Ad implies p in u.sees) and 
    (p !in Ad and p in u.sees implies no f: u.follows | p !in f.posts)
}
    S248 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User, p: Photo |
    (p in Ad implies p in u.sees) and
    (p !in Ad implies (some f: u.follows | p in f.posts) or u.follows = none)
}
    S249 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | all p : Photo | p in u.sees implies
  	(p in Ad or (all u2 : u.follows | p in u2.posts))
}
    S250 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User, p: Photo - Ad | 
  		(Ad in u.sees) and
  		(p in u.sees => posts.p in u.follows)

}
    S251 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User, photo: u.sees - Ad | 
  		(Ad in u.sees) and
  		(posts.photo in (u.follows + u.posts))

}
    S252 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User, a: Ad, photo: u.sees - Ad | 
  		(a in u.sees) and
  		(posts.photo in (u.follows + u.posts))

}
    S253 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	Ad in User.sees
	all u : User | u.follows.posts in u.sees
}
    S254 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	3 < 0
}
    S255 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User, p: Photo |
		p in u.sees =>
			(p in u.posts and p not in Ad) or
			(p in Ad and all f: u.follows | p in f.posts)
}
    S256 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User, p: Photo |
		p in u.sees =>
			(p in Ad and all f: u.follows | p in f.posts)
}
    S257 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User, p: u.sees | p in Ad => all f: u.follows | p in f.posts
}
    S258 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u:User, p:User.sees |
  		one u2:User-u |
  			(p in Ad) implies p in u2.posts

}
    S259 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u:User, p:User.sees |
  		one u2:User-u |
  			(p in Ad) implies p in u2.posts
  
  all u:User, p:User.sees |
  	one u2:User-u |
  		(p not in Ad) implies u2 in u.follows

}
    S260 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User | u.sees = Photo 
  	all u: User, p : Photo | p in u.sees && p in u.posts implies p not in Ad
}
    S261 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | some u.posts & Ad implies u.posts in Ad
}
    S262 in valid iff {
	// Users can see ads posted by everyone, 
	// Users can see non ads posted by followed users.
	all u : User | u.follows.posts in u.sees - Ad 
}
    S263 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u : User | all a : Ad | a in u.sees
  	all u : User | all p : (Photo - Ad) | p in u.^follows.posts implies p in u.sees 

}
    S264 in valid iff {
	all u: User, p: Photo |
        (p in Ad implies p in u.sees) and
        (p in u.posts implies (p in u.sees or some f: u.follows | p in f.posts))

}
    S265 in valid iff {
	all u: User, p: Photo |
        (p in Ad implies p in u.sees) and
        (p not in Ad implies (p in u.sees or some f: u.follows | p in f.posts))
}
    S266 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User, p: Photo | (p in u.posts) or (p in u.posts && p in u.follows.posts && p in u.sees) or (p in Ad && p in u.sees)


}
    S267 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User, p: Photo | (p in u.posts) or ( p in u.follows.posts && p in u.sees) or (p in Ad && p in u.sees)


}
    S268 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | u.sees = u.follows + u.posts + Ad
}
    S269 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	User.follows = none
  	all u : User | u.sees = none
}
    S270 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all u: User | u.sees = (Ad & u.posts) + ((Photo - Ad) & u.follows.posts)

}
    S271 in valid iff {
    // Users can see ads posted by everyone,
    // but only see non-ads posted by followed users.
    all u: User |
        (u.sees & Ad = u.posts & Ad) and
        (all p: u.sees - Ad | some f: u.follows | p in f.posts - Ad)
}
    S272 in valid iff {
  // Users can see ads posted by everyone,
  // but only see non-ads posted by followed users.
  all u: User, p: Photo | p in u.sees implies (p in u.posts or p in Ad) and (p in u.follows.posts implies p not in Ad)
}
    S273 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User, p: Photo |
        (p in u.sees <=> p in Ad) ||
        (p in u.sees <=> some u1: u.follows | p in u1.posts)

}
    S274 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all u : User | u.sees in (u.follows.posts + u.posts) - Ad
}
    S275 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User, p: Photo | (p in u.sees) =>
    (p in u.posts && no Ad & p)
}
    S276 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    no a : Ad, u : User | a in u.follows.posts
}
    S277 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all u : User | u.sees in u.follows.posts implies Ad not in u.follows.posts
}
    S278 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    no a : Ad, u : User | u.sees in (u.follows.posts - a)
}
    S279 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all a : Ad, u : User | u.sees in (u.follows.posts - Ad)
}
    S280 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | #(u.sees & u.posts)=0
  
}
    S281 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all a : Ad, u : User | a in u.posts implies u.sees = u.posts - a
}
    S282 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all u : User | some a : Ad | a in u.sees implies a not in u.follows.posts
}
    S283 in valid iff {
	// Users can see ads posted by everyone, 
 	// but only see non ads posted by followed users.
	User.sees = Ad
}
    S284 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User | sees.u = Ad + u.follows.posts
}
    S285 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all a : Ad | a in User.sees
  all u : User | u.sees in u.follows.posts

}
    S286 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all u : User | u.sees in Ad and u.sees in (u.posts + u.follows.posts)
}
    S287 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all na: Photo - Ad | posts = sees
}
    S288 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.

  User.sees = User.follows.posts + Ad
}
    S289 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.

  all u : User - Influencer | u.sees = u.follows.posts + Ad
}
    S290 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.

  all u : User - Influencer | u.follows.posts in u.sees and Ad in u.sees
}
    S291 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.

  all u : User - Influencer | u.follows.posts in u.sees
  Ad in User.sees
}
    S292 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.

  all u : User - Influencer | u.follows.posts in u.sees
 // Ad in User.sees
}
    S293 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	Ad in User.sees
  	User.follows.posts - Ad in User.sees
}
    S294 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1, u2: User, ads : Ad | u1.sees in ads or  u1.sees in u2.posts and u2 in u1.follows
}
    S295 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : (User - Influencer) | u.sees = Ad + u.follows.posts - u.posts
  
}
    S296 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User | u.sees = Ad - u.posts
  
}
    S297 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User | u.follows.posts in u.sees
  all u : User | no u.posts & u.sees
}
    S298 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
      all u: User | {
        // Users can see ads posted by everyone
        all p: Photo | p in u.sees iff p in Ad or
        // Users can only see non-ads posted by followed users
        (some p1 : Photo - Ad | p1 in u.sees and some f: u.follows | p1 in f.posts)
    }
}
    S299 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
      all u: User, p: Photo | u not in Influencer implies { 
        p in u.sees iff p in u.follows.posts or p in Ad
      }
}
    S300 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
      all u: User, p: Photo | { 
        p in u.sees iff p in (u.follows - Influencer).posts or p in Ad
      }
}
    S301 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | u.posts not in u.sees
}
    S302 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | u.sees = u.posts
}
    S303 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | u.sees != u.posts
}
    S304 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | u.sees not in u.posts
}
    S305 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	User.follows = none
}
    S306 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all u : User | u.sees in Ad or (all p : (Photo - Ad) | posts.p in u.follows)
}
    S307 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  sees in User one -> Ad
}
    S308 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | u.sees = Ad - u.posts
  	all u : User | all p : u.follows.posts - Ad | p in u.sees
}
    S309 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | 
    all p: Photo | 
      (p in Ad and p not in u.posts implies p in u.sees) and
      (p not in Ad implies (some f: u.follows | p in f.posts) implies p in u.sees) and
      (p in Ad and p in u.posts implies p not in u.sees)
}
    S310 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | 
    all p: Photo | 
      (p in u.posts implies p not in u.sees) and
      (p in Ad and p not in u.posts implies p in u.sees) and
      (p not in Ad and p in u.posts implies p not in u.sees) and
      (p not in Ad implies (some f: u.follows | p in f.posts) implies p in u.sees)
}
    S311 in valid iff {
	// Users can see (gets forwarded) ads posted by everyone, 
	// but only gets fortwarded non ads posted by followed users.
    // user does does not get forwards his own posts if they are non-ad
    all u: User | 
    u.sees = { p: Photo | p in Ad and p in (u.follows.posts - { pp : u.posts | pp not in Ad and u not in Influencer })}
}
    S312 in valid iff {
	// Users can see (gets forwarded) ads posted by everyone, 
	// but only gets fortwarded non ads posted by followed users.
    // user does does not get forwarded his own posts if they are non-ad
    all u: User-Influencer | 
    u.sees = { p: Photo | p in Ad and p in (u.follows.posts - u.posts)}
}
    S313 in valid iff {
	// Users can see (gets forwarded) ads posted by everyone, 
	// but only gets fortwarded non ads posted by followed users.
    // user does does not get forwarded his own posts if they are non-ad
    all u: User-Influencer | 
    	u.sees = { p: Photo | p in Ad and p in (u.follows.posts - u.posts)}
    all i: Influencer |
  		i.sees = { p: Photo | p in Ad and p in i.posts}
}
    S314 in valid iff {
	// Users can see (gets forwarded) ads posted by everyone, 
	// but only gets fortwarded non ads posted by followed users.
    // user does does not get forwarded his own posts if they are non-ad
    all u: User-Influencer | 
    	u.sees = { p: Photo | p in Ad and p in (u.follows.posts - u.posts)}
    all i: Influencer |
  		i.sees = { p: Photo | p in Ad and p in (i.follows.posts +i.posts)}
}
    S315 in valid iff {
	// Users can see (gets forwarded) ads posted by everyone, 
	// but only gets fortwarded non ads posted by followed users.
    // user does does not get forwarded his own posts if they are non-ad
    all u: User-Influencer | 
    	u.sees = { p: Photo | p in Ad and p in (u.follows.posts - u.posts)}
    all i: Influencer |
  		i.sees = Ad + i.follows.posts
}
    S316 in valid iff {
	// Users can see (gets forwarded) ads posted by everyone, 
	// but only gets fortwarded non ads posted by followed users.
    // user does does not get forwarded his own posts if they are non-ad
    all u: User-Influencer | 
    	u.sees = { p: Photo | p in Ad and p in (u.follows.posts - u.posts)}
    all i: Influencer |
  		i.sees = Ad + i.follows.posts + i.posts
}
    S317 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	Ad in User.sees
	all u : User | u.follows.posts in u.sees
    User.posts not in User.sees
  
}
    S318 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	Ad in User.sees
	all u : User | u.follows.posts in u.sees
    (User-Influencer).posts not in (User-Influencer).sees
  
}
    S319 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	Ad in User.sees
	all u : User | u.follows.posts in u.sees
    all u: (User-Influencer)| u.posts not in u.sees
  
}
    S320 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	Ad in User.sees
	all u : User | u.follows.posts in u.sees
    all u: (User-Influencer)| (u.posts-Ad) not in u.sees
  
}
    S321 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	Ad in (User-Influencer).sees
	all u : User | u.follows.posts in u.sees
    all u: (User-Influencer)| u.posts not in u.sees

  
}
    S322 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	Ad in (User-Influencer).sees
	all u : User | u.follows.posts in u.sees
    all u:  User | u.posts not in u.sees

  
}
    S323 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	Ad in (User-Influencer).sees
	all u: User | u.follows.posts in u.sees
    all u: (User-Influencer)
           | u.posts not in u.sees
    all i: Influencer | all p: i.posts | p not in Ad and p not in i.sees

  
}
    S324 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	Ad in (User-Influencer).sees
	all u: User | u.follows.posts in u.sees
    all u: (User-Influencer)
           | u.posts not in u.sees
    all i: Influencer | all p: i.posts | p in Ad and p in i.sees

  
}
    S325 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	Ad in (User-Influencer).sees
	all u: User | u.follows.posts in u.sees
    all u: (User-Influencer)
           | u.posts not in u.sees

    all i: Influencer | all p: (Photo-Ad) | p in i.posts and p in i.sees

  
}
    S326 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	Ad in (User-Influencer).sees
	all u: User | u.follows.posts in u.sees
    all u: (User-Influencer)
           | u.posts not in u.sees

    all i: Influencer | all p: Ad | p in i.posts and p in i.sees

  
}
    S327 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	Ad in (User-Influencer).sees
	all u: User | u.follows.posts in u.sees
    all u: (User-Influencer)
           | u.posts not in u.sees

    all i: Influencer | all p: Photo - Ad | p in i.posts and p not in i.sees

  
}
    S328 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	Ad in (User-Influencer).sees
	all u: (User - Influencer)| u.follows.posts in u.sees
    all u: (User-Influencer)
           | u.posts not in u.sees

    all i: Influencer | all p: Photo - Ad | p in i.posts and p not in i.sees

  
}
    S329 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	Ad in (User-Influencer).sees
	all u: (User - Influencer)| u.follows.posts in u.sees
    all u: (User-Influencer)
           | u.posts not in u.sees

    all i: Influencer | i.posts not in i.sees

  
}
    S330 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	Ad in (User-Influencer).sees
	all u: (User - Influencer)| u.follows.posts in u.sees
    all u: (User-Influencer)
           | u.posts not in u.sees

    all i: Influencer | (i.posts-Ad) not in i.sees

  
}
    S331 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	Ad in (User-Influencer).sees
	all u: (User - Influencer)| u.follows.posts in u.sees
    all u: (User-Influencer)
           | u.posts not in u.sees

    all i: Influencer | all a: Ad & Influencer.posts |
             a not in i.sees

  
}
    S332 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	Ad in (User-Influencer).sees
	all u: (User - Influencer)| u.follows.posts in u.sees
    all u: (User-Influencer)
           | u.posts not in u.sees

    all i: Influencer | all a: Ad & Influencer.posts |
             a in i.sees

  
}
    S333 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	Ad in (User-Influencer).sees
	all u: (User - Influencer)| u.follows.posts in u.sees
    all u: (User-Influencer)
           | u.posts not in u.sees

    all i: Influencer | all a: Ad | a in i.posts =>
             a in i.sees
  


  
}
    S334 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  

	Ad in (User-Influencer).sees
	all u: (User - Influencer)| u.follows.posts in u.sees
    all u: (User-Influencer)
           | u.posts not in u.sees

    all i: Influencer | all a: Ad | a in i.posts =>
             a in i.sees
  
    all i: Influencer | all p: Photo - Ad | p in i.posts => p not in i.sees

  
}
    S335 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  

	Ad in (User-Influencer).sees
	all u: (User - Influencer)| u.follows.posts in u.sees
    all u: (User-Influencer)
           | u.posts not in u.sees


 
  
    all i: Influencer | all p: Photo - Ad | p in i.posts => p not in i.sees

  
}
    S336 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  

	Ad in User.sees
	all u: (User - Influencer)| u.follows.posts in u.sees
    all u: (User-Influencer)
           | u.posts not in u.sees


 
  
    all i: Influencer | all p: (Photo - Ad) | p in i.posts and p not in i.sees

  
}
    S337 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  

	User.sees= Ad
	all u: (User - Influencer)| u.follows.posts in u.sees
    all u: (User-Influencer)
           | u.posts not in u.sees


 
  
    all i: Influencer | all p: (Photo - Ad) | p in i.posts and p not in i.sees

  
}
    S338 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  

	User.sees= Ad
	
  User.follows.posts = User.sees
    all u: (User-Influencer)
           | u.posts not in u.sees


 
  
    all i: Influencer | all p: (Photo - Ad) | p in i.posts and p not in i.sees

  
}
    S339 in valid iff {
	// Users can see (gets forwarded) ads posted by everyone, 
	// but only gets fortwarded non ads posted by followed users.
    // user does does not get forwarded his own posts if they are non-ad
    all u: User-Influencer | 
    	u.sees = { p: Photo | p in Ad and p in (u.follows.posts - u.posts)}
    no { p: Photo | some i: Influencer | p in i.sees and p in i.posts and not p in Ad }
}
    S340 in valid iff {
	// Users can see (gets forwarded) ads posted by everyone, 
	// but only gets fortwarded non ads posted by followed users.
    // user does does not get forwarded his own posts if they are non-ad
	Ad in User.sees
	all u : User | u.follows.posts in u.sees
    no { p: Photo | some i: Influencer | p in i.sees and p in i.posts and not p in Ad }
}
    S341 in valid iff {
	// Users can see (gets forwarded) ads posted by everyone, 
	// but only gets fortwarded non ads posted by followed users.
    // user does does not get forwarded his own posts if they are non-ad
	all u : (User-Influencer) |  u.sees = Ad + u.follows.posts
    no { p: Photo | some i: Influencer | p in i.sees and p in i.posts and not p in Ad }
}
    S342 in valid iff {
	// Users can see (gets forwarded) ads posted by everyone, 
	// but only gets fortwarded non ads posted by followed users.
    // user does does not get forwarded his own posts if they are non-ad
    all i : Influencer | i in Ad
	all u : (User-Influencer) |  u.sees = Ad + u.follows.posts
    no { p: Photo | some i: Influencer | p in i.sees and p in i.posts and not p in Ad }
}
    S343 in valid iff {
	// Users can see (gets forwarded) ads posted by everyone, 
	// but only gets fortwarded non ads posted by followed users.
    // user does does not get forwarded his own posts if they are non-ad
    all i : Influencer | i.posts in Ad
	all u : (User-Influencer) |  u.sees = Ad + u.follows.posts
    no { p: Photo | some i: Influencer | p in i.sees and p in i.posts and not p in Ad }
}
    S344 in valid iff {
	// Users can see (gets forwarded) ads posted by everyone, 
	// but only gets fortwarded non ads posted by followed users.
    // user does does not get forwarded his own posts if they are non-ad
    all i : Influencer | i.posts in Ad
	all u : User |  u.sees = Ad + u.follows.posts
}
    S345 in valid iff {
	// Users can see (gets forwarded) ads posted by everyone, 
	// but only gets fortwarded non ads posted by followed users.
    // user does does not get forwarded his own posts if they are non-ad
    all i : Influencer | all p : i.posts | p not in Ad and p not in i.sees
	all u : User |  u.sees = Ad + { p: u.follows.posts| p not in Ad}
}
    S346 in valid iff {
	// Users can see (gets forwarded) ads posted by everyone, 
	// but only gets fortwarded non ads posted by followed users.
    // user does does not get forwarded his own posts if they are non-ad
    all i : Influencer | all p : i.posts | p not in Ad and p not in i.sees
	all u : (User-Influencer) |  u.sees = Ad + { p: u.follows.posts| p not in Ad}
}
    S347 in valid iff {
	// Users can see (gets forwarded) ads posted by everyone, 
	// but only gets fortwarded non ads posted by followed users.
    // user does does not get forwarded his own posts if they are non-ad
    Influencer.sees = Ad
    Influencer.posts in Photo
	all u : (User-Influencer) |  u.sees = Ad + { p: u.follows.posts| p not in Ad}
}
    S348 in valid iff {
	// Users can see (gets forwarded) ads posted by everyone, 
	// but only gets fortwarded non ads posted by followed users.
    // user does does not get forwarded his own posts if they are non-ad
    Influencer.sees = Ad
    Influencer.posts = Ad
	all u : (User-Influencer) |  u.sees = Ad + { p: u.follows.posts| p not in Ad}
}
    S349 in valid iff {
	// Users can see (gets forwarded) ads posted by everyone, 
	// but only gets fortwarded non ads posted by followed users.
    // user does does not get forwarded his own posts if they are non-ad
    all i : Influencer | i.sees = Ad + i.follows
	all u : (User-Influencer) |  u.sees = Ad + { p: u.follows.posts| p not in Ad}
}
    S350 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u:User | no a:Ad | a in u.sees and a in u.follows.posts 
  	all u:User | no (u.posts & u.sees)
  	all i:Influencer | no a:Ad | a in i.sees and a in i.follows.posts 
  	all i:Influencer | no (i.posts & i.sees)
}
    S351 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  
  	all u: User | all f : u.follows | no (u.sees & f.posts & Ad) and no (u.sees & u.posts)

}
    S352 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all ad: Ad, u: User | ad not in u.sees => ad in u.posts
  	all p: Photo - Ad, u: User | p in u.sees => posts.p in u.follows
}
    S353 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all x: Photo, y: User | lone posts.x && one follows.y
}
    S354 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all a : Ad | all u : User | a in u.sees iff not a in u.posts
}
    S355 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all a : Ad | all u : User | a in u.sees implies not a in u.posts
}
    S356 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.

  all x, y : User | x->y in follows and y -> x in follows implies x in y.sees
  
}
    S357 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	some p : Photo | all x : User | all y : User | x != y and p in x.posts and p in 		y.sees implies x in y.follows
}
    S358 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	no p : Ad | all x : User | all y : User | x != y and p in x.posts and p in y.sees implies x in y.follows
}
    S359 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all x : User, a : Photo | some y : User | a in x.posts and y in sees.a implies y in x.follows 
}
    S360 in valid iff {
	// Users can see ads posted by everyone, 
  all u : User | (u.sees in Ad) or (u.sees in u.follows.posts) or (u.sees in u.posts)
	// but only see non ads posted by followed users.

}
    S361 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all a: Ad | all u: User | a in u.sees &&
  	all p: Photo - Ad | all u1: User | p in u.sees iff u1 in u.follows and p in u1.posts 
}
    S362 in valid iff {
	// Users can see ads posted by everyone,
	// but only see non ads posted by followed users.
  all u : User | all p : u.sees | p not in Ad implies p in u.follows.sees
  //all u: User, p: Photo |
  	// in Ad implies p in u.sees)
  	//d (p not in Ad implies one poster : User | poster in u.follows and p in poster.posts and p in u .sees)
	
}
    S363 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User, a : Ad | u -> a in sees
  	no u : User, p : Photo | p in Ad implies all u2 : posts.p | u -> u2 in follows
}
    S364 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all p: Photo-Ad, u:User | p in u.sees

}
    S365 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all p: Photo-Ad, u:User | p in u.follows.sees

}
    S366 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User, p: Photo, a:Ad |
  		(p in u.sees) implies 
  			(p in a or posts.p in u.follows)

}
    S367 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User | Ad not in u.follows.posts

}
    S368 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User.follows.posts | Ad not in u

}
    S369 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User.follows.sees | Ad not in u

}
    S370 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all x: Photo, y,z: User | (not x in Ad) and User->Photo in sees and User->Photo in posts implies User->User in follows

}
    S371 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User, p : Photo - Ad | u.sees in u.follows

}
    S372 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all x:User, y:x.follows, r:y.posts , z:x.sees | z in r

}
    S373 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all x: User | all y: User | some w : Ad | (x->y in follows and y->w in posts) implies x->w in sees 
}
    S374 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all pa : Photo - Ad | some u:User | pa in u.sees and pa in u.follows.posts 
}
    S375 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User, p : Photo - Ad | lone( u.follows & sees.p)

}
    S376 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all x:User, y:x.follows, r:y.posts , z:x.sees | r not in Ad implies z in r

}
    S377 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all x:User, y:User - x.follows | y.posts-Ad not in x.sees
}
    S378 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all x: User | all y: User | some w : Photo | (not x->y in follows and y->w in posts and not w in Ad and not x=y) implies (not x->w in sees)
}
    S379 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all x:User, y:User-x.follows | y.posts not in x.sees
}
    S380 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all x:User, y:User-x.follows | y.posts not in x.sees - Ad
}
    S381 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User| u.sees - Ad not in u.follows.posts

}
    S382 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all x: User | all y: User | some w : Photo | (not x->y in follows and y->w in posts and not w in Ad) implies (not x->w in sees)
}
    S383 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User, ad: Ad, na: Photo - Ad | u in sees.ad and u not in follows.posts.na

}
    S384 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User, ad: Ad, na: Photo - Ad | u in follows.sees.ad and u not in follows.posts.na

}
    S385 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User, ad: Ad, na: Photo - Ad | u in follows.posts.ad and u not in follows.posts.na

}
    S386 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all ads : Ad, nonAds : Photo - Ad, user : User | one sees.ads
}
    S387 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all ads : Ad, nonAds : Photo - Ad, user : User | 
  		ads in user.sees
    // all photo : Photo - Ad, user : User | photo in user.sees implies photo in user.follows.posts
    // all user : User | user.sees - Ad in user.follows.posts
}
    S388 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    User.sees = Photo
    all x: Photo-Ad, u:User | u in sees.x implies x in u.follows.posts
    
}
    S389 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all x: Photo-Ad, u:User | sees.x = u.follows.posts
    
}
    S390 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all a: Ad, u: User | a in u.sees and u.follows.posts in u.sees and u.posts not in u.sees

}
    S391 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | u.follows.posts in u.sees and u.posts not in u.sees
}
    S392 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  Ad in User.sees
  all u: User | u.follows.posts in u.sees - Ad
}
    S393 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | u.follows.posts in u.sees and u.posts - Ad not in u.sees
}
    S394 in valid iff {
    // Users can see ads posted by everyone
    // um ad posted, can be seen by all users
    // all users can see ad
    /*all u : User, a : Ad | a in u.sees
  
    // Users can only see non-ads if they are posted by followed users
    // all users can see photo not ad if follows user who posted
    // u follows v, v posts non-ad called p, u sees   
	all u : User, p : Photo |
  		p not in Ad implies(
  			p in u.sees iff
  				some y : User | y in u.follows and p in y.posts)
  	*/
  
  
	// Users can see ads posted by everyone
	all u: User, p: Ad | p in u.sees
	// Users can only see non-ads posted by followed users
	all u: User, p: Photo |
    	p not in Ad implies (
      		p in u.sees iff (
        		some y: User | y in u.follows and p in y.posts) or
          		p in u.posts
    	)
}
    S395 in valid iff {
    // um ad posted, can be seen by all users
    // all users can see ad
  
    // Users can see ads posted by everyone
	all u : User, a : Ad | a in u.sees
  
    // Users can only see non-ads if they are posted by followed users
	all u : User, p : Photo | 
  		p in u.sees implies (
  			p not in Ad iff (
           		some y : User | p in y.posts and y in u.follows )
        )


        


}
    S396 in valid iff {
    // Users can see ads posted by everyone
    all u : User, a : Ad | a in u.sees
  
    // Users can only see non-ads if they are posted by followed users
    all u : User| some p : Photo |
        p not in Ad implies (
            p in u.sees iff (
                some y : User | p in y.posts and y in u.follows
            )
        )
}
    S397 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
    all a : Photo | all u1,u2 : User | (a in u1.sees ) iff ( ( a in Ad ) or ( u2 in u1.follows and a in u2.posts ) )

}
    S398 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u:User | all a:Ad| u.sees in a.posts

}
    S399 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u : User | all add : Ad | add in u.posts 
  	all u : User, add : Ad| add->u not in follows 
  

}
    S400 in valid iff {
	// Users can see ads posted by everyone,
	// but only see non ads posted by followed users.
  all u : User | all p : Photo| p not in Ad implies some ad : Photo | ad in u.sees

}
    S401 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  
  all u : User | not sees.Ad in follows.u

}
    S402 in valid iff {
	// Users can see ads posted by everyone, 
    all x : Ad | some sees.x
	// but only see non ads posted by followed users. 
  	all x : Photo | not Ad in follows.x
}
    S403 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User, p : Photo | (p in Ad => p in u.sees) and (p not in Ad => (some v : User | p in v.posts and u in v.follows) =>p in u.sees)

}
    S404 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.

  all x: User | all y: Ad | y in x.sees
  all w: User | all p: Photo | some z: w.follows | (not p in Ad) => p in z.posts and p in w.sees
}
    S405 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User | some ad: Ad | ad in u.sees 
	all u: User | some p: Photo | p in u.sees implies (some f: User | u in f.follows)
}
    S406 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	//all u: User | some ad: Ad | ad in u.sees 
	all u: User | some p: Photo | p in u.sees implies (some f: User | u in f.follows)
}
    S407 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.

  all x: User | all y: Ad | y in x.sees
  all w: User | all p: Photo | some z: w.follows | (not p in Ad and p in w.sees) => p in z.posts 
}
    S408 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all p : Photo | posts.p.follows in sees.p
}
    S409 in valid iff {
	// Users can see ads posted by everyone, 
    all x : Ad | some sees.x
	// but only see non ads posted by followed users. 
  	all x : Photo, u : User | u.follows not in Ad
}
    S410 in valid iff {
	// Users can see ads posted by everyone, 
    all x : Ad | some sees.x
	// but only see non ads posted by followed users. 
  	all x : Photo | User.follows not in Ad
}
    S411 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	//all u: User | some ad: Ad | ad in u.sees 
	all u: User | some p: Photo | p in u.sees implies (some f: User | u in f.follows and p in f.posts)
}
    S412 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all a : Ad, u : User | u in sees.a
  	all p : Photo | posts.p.follows in sees.p and p not in Ad
}
    S413 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.

  all w: User | all p: Photo | some z: w.follows | (not p in Ad) => p in z.posts and p in w.sees

}
    S414 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users
   all u: User | some a : Ad |
        u.sees = Ad + (u.follows.posts)
}
    S415 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users
   all u: User | some a : Ad |
        u.sees = a + (u.follows.posts)
}
    S416 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  

  
  all u1, u2:User, p: Photo - Ad | 
  		u1 in u2.follows and p in u2.posts 
  			implies 
  		p in u1.sees

}
    S417 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.

  all w: User | all p: Photo | all z: w.follows | (not p in Ad) => p in z.posts and p in w.sees

}
    S418 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users. foto é ad or 
  	all x : Photo, u : User | x = Ad or posts.x in u.follows
}
    S419 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.

  all w: User | all p: Photo | all z: w.follows | (not p in Ad) => p in z.posts and p in w.sees and p in w.posts

}
    S420 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users
   all u: User | all a : Ad |
        u.sees = a + (u.follows.posts)
}
    S421 in valid iff {
    User -> User in sees.(~posts)
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.

}
    S422 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	//all u: User | some ad: Ad | ad in u.sees 
	all u: User | some p: Photo | p in u.sees implies ((some f: User | u in f.follows and p in f.posts) or p in Ad)
}
    S423 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	//all u: User | some ad: Ad | ad in u.sees 
	all u: User | some p: Photo | p in u.sees implies ((some f: User | f in u.follows and p in f.posts) or p in Ad)
}
    S424 in valid iff {
    User -> User in sees.(((this.@User + this.@Photo + this.@Day + Int + String) <: iden) & (Ad -> Ad)).(~posts).follows
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.

}
    S425 in valid iff {
	// Users can see ads posted by everyone,
	// but only see non ads posted by followed users.
  all u : User | all p : Photo| 
  (p in Ad implies all poster : User | p in u.sees and p in poster.posts) and 
  (p not in Ad implies 
    (all poster : User | poster in u.follows and p in poster.posts and p in u.sees))
}
    S426 in valid iff {
    User -> User in sees.(((this.@User + this.@Photo + this.@Day + Int + String) <: iden) & (Ad -> Ad)).(~posts).((((this.@User + this.@Photo + this.@Day + Int + String) <: iden)) -  follows)
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.

}
    S427 in valid iff {
    User -> User in sees.(((this.@User + this.@Photo + this.@Day + Int + String) <: iden) & (Ad -> Ad)).(~posts).(((this.@User + this.@Photo + this.@Day + Int + String) -> (this.@User + this.@Photo + this.@Day + Int + String)) -  follows)
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.

}
    S428 in valid iff {
    User -> User in sees.(((this.@User + this.@Photo + this.@Day + Int + String) <: iden) - (Ad -> Ad)).(~posts).((User -> User) -  follows)
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.

}
    S429 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all disj u1,u2:User | some p:Photo| p in sees.u1 implies (u2 in follows.u1 or p in Ad)
}
    S430 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all disj u1,u2:User | some p:Photo| p in u1.sees implies (u2 in follows.u1 or p in Ad)
}
    S431 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all disj u1,u2:User | some p:Photo| p in u1.sees implies ((u2 in follows.u1 and p in u2.posts) or p in Ad)
}
    S432 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all disj u1,u2:User | some p:Photo| p in u1.sees implies ((u2 in follows.u1 and p in posts.u2) or p in Ad)
}
    S433 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1:User | one u2:User | some p:Photo| p in u1.sees implies ((u2 in follows.u1 and p in u2.posts) or p in Ad)
}
    S434 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1:User | one u2:User | one p:Photo| p in u1.sees implies ((u2 in follows.u1 and p in u2.posts) or p in Ad)
}
    S435 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1:User | one u2:User | all p:Photo| p in u1.sees implies ((u2 in follows.u1 and p in u2.posts) or p in Ad)
}
    S436 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1:User | some u2:User | all p:Photo| p in u1.sees implies ((u1 in u2.follows and p in u2.posts) or p in Ad)
}
    S437 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1:User | some u2:User | all p:Photo| p in u1.sees implies ((u1 in follows.u2 and p in u2.posts) or p in Ad)
}
    S438 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all p : Photo | one sees.p
}
    S439 in valid iff {
	// Users can see ads posted by everyone,
  	all u1 ,u2 : User |all ad : Ad |  u2.posts in u1.sees 
	// but only see non ads posted by followed users.
  	
  	

}
    S440 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all x: User | (some Ad & x.sees) and ((some x.follows) implies (x.follows.posts in x.sees))
}
    S441 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all x: User | x.sees = (Ad + x.follows.posts) or ((no x.follows) implies x.sees = Ad)
}
    S442 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User, ad: Ad | {
      u.sees = ad + u.follows.posts - u.posts
    }
}
    S443 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User, ad: Ad | {
      u.sees = ad + u.follows.posts + u.posts
    }
}
    S444 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User, a: Ad, f: u.follows.posts | {
      u.sees = a + f
      
  	}
}
    S445 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	Ad in User.sees
  	Photo - User.follows.posts - Ad not in User.sees
}
    S446 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	//all ad : Ad | all u: User | ad in u.sees
  all u : User |
  
  	some p: u.sees | some f: u.follows | p in Ad or p in f.posts
  		
 
}
    S447 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all ad : Ad | all u: User | ad in u.sees
  all u : User |
  	some p: u.sees | 
  	some f: u.follows | p in Ad or p in f.posts
  		
 
}
    S448 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all ad : Ad | all u: User | ad in u.sees
  all u : User | some p : u.sees | p in Ad or p in u.follows.posts
  
  		
 
}
    S449 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all ad : Ad | all u: User | ad in u.sees
  all u : User | some p : u.sees | p in Ad or p in u.follows.posts or p in u.posts
  
  		
 
}
    S450 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all ad : Ad | all u: User | ad in u.sees
  all u : User | some p : u.sees | some f : u.follows |p in Ad or p in f.posts or p in u.posts
  
  		
 
}
    S451 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all ad : Ad | 
  	all u: User | 
  		ad in u.sees
  
  all u : User | 
  	some p : u.sees |
  		all f : u.follows |
  		p in Ad or p in f.posts or p in u.posts
  
  		
 
}
    S452 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all ad : Ad | 
  	all u: User | 
  		ad in u.sees
  
  all u : User | 
  	all p : u.sees |
  		all f : u.follows |
  		p in Ad or p in f.posts or p in u.posts
  
  		
 
}
    S453 in valid iff {
	// Users can see ads posted by everyone, 
    all u: User, a: Ad | a in u.sees

	// but only see non ads posted by followed users.
	all u: User, a: Ad | a not in u.sees one date
  
  	
}
    S454 in valid iff {
	// Users can see ads posted by everyone, 
    all u: User, a: Ad | a in u.sees

	// but only see non ads posted by followed users.
	all u: User, a: Ad | a not in u.sees some date
  
  	
}
    S455 in valid iff {
  // Users can see ads posted by everyone, 
  // but only see non ads posted by followed users.
  all u : User | u.sees in Ad
  all u: User, p: Photo | p in u.sees iff ((p not in Ad) and p in u.follows.posts)
}
    S456 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User, f : u.follows | Ad in u.sees and f.posts in u.sees
}
    S457 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User | (posts.(u.sees) - u.follows).posts in Ad

}
    S458 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User | (posts.(u.sees) - u.follows - u).posts in Ad

}
    S459 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  
  all u1, u2 : User, p : Photo, a : Ad |
  (u1 -> p in sees && u1 -> u2 in follows) implies p not in Ad 
  
  //(u1 -> p in sees && u1 -> u2 not in follows) implies p in Ad

//  u -> a in sees and u->p in sees && u ->  in follows   

}
    S460 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1, u2 : User, p : Photo | u2 in u1.follows and p in u1.sees and p in u2.posts implies p in Ad 
}
    S461 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User, a : Photo | a in u.sees implies a in Ad or 
	    some u1 : User | a in u.posts-Ad and u1 in u.follows
  	
}
    S462 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all disj u1, u2: User | all s: u2.sees| u2 not in u1.follows and s in Ad and s not in u1.sees
}
    S463 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all disj u1, u2: User | all s: u2.sees| u2 not in u1.follows and s not in Ad and s not in u1.sees
}
    S464 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all disj u1, u2: User | all s: u2.posts| u2 not in u1.follows and s not in Ad and s not in u1.sees
}
    S465 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all disj x, y : User | all p : y.posts | (p in x.sees) iff (y in x.follows)
}
    S466 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all disj x, y : User | some ((x.sees - Ad) & x.posts) implies (y in x.follows)
}
    S467 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User | all ad: Ad | ad in u.sees
  	all p: Photo - Ad | all u1, u2: User | p in u1.sees iff u2 in u1.follows
}
    S468 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User | all ad: Ad | ad in u.sees
  	all p: Photo - Ad | all u: User | all img: u.sees | posts.img in u.follows
}
    S469 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u1, u2:User, p:Photo, a:Ad | u1 in u2.follows and p in u1.posts 
  			implies p in u2.sees

}
    S470 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u1, u2:User, p:Photo, a:Ad | 
  			u1 in u2.follows and p in u1.posts and a !=p
  				implies 
  			p in u2.sees

}
    S471 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u1, u2, u3:User, p:Photo, a:Ad | 
  			u1 in u2.follows and p in u1.posts and u3 not in u2.follows and a in u3.posts and a != p 
  				implies 
  			p in u2.sees and a in u2.sees

}
    S472 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User, ad: Ad | all uu: u.follows| ad in u.sees implies not ad in uu.posts
  		and not ad in u.posts

}
    S473 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.

  all u: User, p: Photo |
        (p in Ad => p in u.sees) and           // Users can see all ads
        (p not in Ad => some u2: u.follows | p in u2.posts => p in u.sees) // Users see non-ads only from followed users
  
}
    S474 in valid iff {
	// Users can see ads posted by everyone,
  	all ad: Ad | all u: User | (ad-u.posts) in u.sees
	// but only see non ads posted by followed users.
  	and (u.follows.posts- ad) in u.sees

}
    S475 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | all ad: Ad | ad in u.sees and (ad not in u.follows.sees )

}
    S476 in valid iff {
	// Users can see ads posted by everyone, 
  	all u: User, ad: Ad | ad in u.sees
	// but only see non ads posted by followed users.
  	// if not followed not see not add
  	all u1, u2: User|some p: Photo | (p not in Ad && u1 -> p in sees && u2-> p in posts) implies (u2 in u1.follows) && u1 != u2
  	//all u1, u2: User, p: Photo | u1 not in u2.follows 

}
    S477 in valid iff {
	// Users can see ads posted by everyone, 
  	all u: User, ad: Ad | ad in u.sees
	// but only see non ads posted by followed users.
  	// if not followed not see not add
  	all u1, u2: User, p: Photo | u1 != u2 and p not in Ad and u1 not in u2.follows implies p not in u2.sees 

}
    S478 in valid iff {
	// Users can see ads posted by everyone, 
  	all u: User| some p: Photo | p in Ad implies p in u.sees
	// but only see non ads posted by followed users.
  	// if not followed not see not add
  	all u1, u2: User, p: Photo | (p not in Ad and u1 not in u2.follows) implies (p not in u2.sees)

}
    S479 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all p : Photo, u : (User - Influencer) | p in Ad implies p in u.sees
  	all u : (User - Influencer) | no (u.sees & Ad)
}
    S480 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | one u2 : User| all i : Photo | (i in Ad) implies i in u.sees
  and ((i in u2.posts) and ( u2 in u.follows)) implies i in u.sees
}
    S481 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | one u2 : User| all i : Photo | (i in Ad) implies i in u.sees
  or ((i in u2.posts) and ( u2 in u.follows)) implies i in u.sees
}
    S482 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  
  all u, u1 : User, p : Photo | u != u1 and u in follows.u1 implies u in sees.p

}
    S483 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u, u1 : User, p : Photo | u in follows.u1 implies p not in Ad
  

}
    S484 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all p : Photo | all u : User | (p in u.posts and p in Ad) implies p in u.sees
  	all p : Photo | all u : User | (p in u.posts and p !in Ad) implies p in u.follows.sees

}
    S485 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all p : Photo - Ad, u : User | Ad in u.sees && u.sees in u.follows.posts 

}
    S486 in valid iff {
	// Users can see ads posted by everyone,
  	// but only see non ads posted by followed users.
  	all disj u : User , a : Ad | all p : u.sees |one u1 : User | (p in u1.posts and u1 in 	u.follows and u1 != u) or a in u.sees
	
	
}
    S487 in valid iff {
	// Users can see ads posted by everyone,
  	// but only see non ads posted by followed users.
  	all a : Ad , u : User | a in u.sees or
  	all disj u1,u2 : User | all p : u1.sees | u2 not in u1.follows implies (p not 	  in u2.posts)  
	
	
}
    S488 in valid iff {
	// Users can see ads posted by everyone,
  	// but only see non ads posted by followed users.
  	all disj u1,u2 : User |one p : Photo | (u1 not in u2.follows and p in u2.sees) 	implies p in Ad  
  	
	
	
}
    S489 in valid iff {
	// Users can see ads posted by everyone,
  	// but only see non ads posted by followed users.
  	all disj u1,u2 : User |one p : Photo | ((p != Ad and u1 not in u2.follows) 		implies p not in u2.sees ) or p = Ad
  	
	
	
}
    S490 in valid iff {
	// Users can see ads posted by everyone,
  	// but only see non ads posted by followed users.
  	all u1,u2 : User |one p : Photo | ((p != Ad and u1 not in u2.follows) 		implies p not in u2.sees ) or p = Ad
  	
	
	
}
    S491 in valid iff {
	// Users can see ads posted by everyone,
  	// but only see non ads posted by followed users.
  	all u1,u2 : Influencer |one p : Photo | ((p != Ad and u1 not in u2.follows) 		implies p not in u2.sees ) or p = Ad
  	
	
	
}
    S492 in valid iff {
	// Users can see ads posted by everyone,
  	// but only see non ads posted by followed users.
  	all u1,u2 : User |lone p : Photo | ((p != Ad and u1 not in u2.follows) 		implies p not in u2.sees ) or p = Ad
  	
	
	
}
    S493 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u: User | all a: Ad, p: Photo - Ad | a in u.sees and (p in u.follows.posts => p in u.sees)  
  	
}
    S494 in valid iff {
  // Ads are visible to all users
  all u: User, a: Ad | a in u.sees
  all u: User | #(u.sees & (u.posts - Ad)) = 0

  // Non-ads are visible only if posted by followed users
  all u: User | some p: Photo - Ad | p in u.follows.posts => p in u.sees
}
    S495 in valid iff {
  // Ads are visible to all users
  all u: User, a: Ad | a in u.sees
  //all u: User | #(u.sees & (u.posts - Ad)) = 0

  // Non-ads are visible only if posted by followed users
  all u: User | some p: Photo - Ad | p in u.follows.posts => p in u.sees
}
    S496 in valid iff {
	// Users can see ads posted by everyone,
  	// but only see non ads posted by followed users. 
	//all u,u1 : User | all p : Photo | (p in u.sees and p in u1.posts) implies 		(u1 not in u.follows implies p = Ad) or p = Ad 
  	all u: User | 
        u.sees = (Ad + (Photo - Ad) & {p: Photo | some u.follows & p.(~posts)}) 
  		or u.sees = none 
}
    S497 in valid iff {
	// Users can see ads posted by everyone,
  	// but only see non ads posted by followed users. 
	//all u,u1 : User | all p : Photo | (p in u.sees and p in u1.posts) implies 		(u1 not in u.follows implies p = Ad) or p = Ad 
  	//all u: User | 
        //u.sees = (Ad + (Photo - Ad) & {p: Photo | some u.follows & p.(~posts)}) 
  		//or u.sees = none 
  all u: User | {
        // Users can always see all ads
        Ad in u.sees or #u.sees = 0  
        
        // Users can only see non-ads posted by followed users
        all p: Photo - Ad | 
            p in u.sees iff some u.follows & p.(~posts)
    }
}
    S498 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User | u.sees in (User - u).posts
  	all u: User | all p: Photo - Ad | p in u.sees <=> p in u.follows.posts 

}
    S499 in valid iff {
  all u1, u2: User, p: Photo |
    (u2 in u1.follows => (p !in Ad and p in u2.posts and p in u1.sees)) and
    (u2 !in u1.follows => (p in Ad => p in u1.sees))
}
    S500 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User, a:Ad | a in u.sees
  all u: User, f: Photo | f in u.sees implies some u.follows.posts

}
    S501 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User, a:Ad | a in u.sees
  all u: User | some f: Photo | f in u.sees implies f in u.follows.posts

}
    S502 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | Ad in u.sees 
  all u: User | Photo in u.sees implies Photo not in u.posts

}
    S503 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | u.sees = u.follows.posts + posts.Ad + u.posts
}
    S504 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | all p : u.follows.posts-Ad | u.sees = Ad + p
}
    S505 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | all p : u.follows.posts - Ad | u.sees = Ad 
}
    S506 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | u.follows.posts not in Ad and u.sees = u.follows.posts + Ad
}
    S507 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | (u.follows.posts not in Ad) and u.sees in (u.follows.posts + Ad)
}
    S508 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1, u2: User | all a: Ad | u1 != u2 and a in u2.posts implies a in u1.sees
}
    S509 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1, u2: User | all a: Ad | (u1 != u2 and a in u2.posts) implies a in u1.sees
  	all u1, u2: User | all p: Photo - Ad | u1 != u2 and p in u1.sees implies (u2 in u1.follows and p in u2.posts)
}
    S510 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1, u2: User | all a: Ad | (a in u2.posts) implies a in u1.sees
  	all u1, u2: User | all p: Photo - Ad |( u1 != u2 and p in u1.sees )implies (u2 in u1.follows and p in u2.posts)
}
    S511 in valid iff {
	// Users can see 	 ads posted by everyone, 
	// Users can see non ads posted by followed users.
	all u : User | some p : Photo - Ad |
  		p in u.follows.posts
  		
}
    S512 in valid iff {
	// Users can see 	 ads posted by everyone, 
	// Users can see non ads posted by followed users.
	all u : User | some p : Photo - Ad |
  		p in u.sees and p in u.follows.posts
  		
}
    S513 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
 all u: User, p: Photo |
        (p in Ad => p in u.sees) and
        (p not in Ad => (some u2: User | (u2 in u.follows && p in u2.posts && p in u.sees)) or (p in u.posts and p in u.sees))

}
    S514 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all disj u, followed : User | all p : u.sees | followed in u.follows and p in u.sees and p in u.follows.posts

}
    S515 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u : User, p : Photo | #(u.follows) > 0 and  p not in Ad and (p in u.sees iff p in u.follows.posts)

}
    S516 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u : User, ad : Ad | ad in u.sees and ( all p : Photo | p != ad and p not in Ad and p in u.sees iff p in u.follows.posts)
}
    S517 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u : User, ad : Ad | ad in u.sees or ( all p : Photo | p not in Ad and p in u.sees iff p in u.follows.posts)
}
    S518 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u : User, ad : Ad | u not in Influencer and ad in u.sees or ( all p : Photo | p != ad and p not in Ad and p in u.sees iff p in u.follows.posts)
}
    S519 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u : User, ad : Ad, followed : u.follows | ad in u.sees or ( all p : Photo | p not in Ad and p in u.sees iff p in followed.posts)
}
    S520 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u : User, ad : Ad, followed : u.follows | ad in u.sees or #(u.follows)>0 and ( all p : Photo | p not in Ad and (p in u.sees iff p in followed.posts))
}
    S521 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all disj u1, u2 : User |
  	(u1 not in u2.follows) implies u2.posts not in u1.sees

}
    S522 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u1, u2 : User |
  	(u1 not in u2.follows) implies u2.posts not in u1.sees

}
    S523 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all disj u1, u2 : User |
  	((u1 not in u2.follows) implies (all p : Photo | (p in u1.posts and p in Ad) 		 		implies (p not in u2.sees)))

}
    S524 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u1, u2: User| some a: Ad| a in u1.sees implies (a in  u2.posts and u2 in u1.follows)
}
    S525 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u1, u2: User| some a: Ad| a in u1.sees iff (a in  u2.posts and u2 in u1.follows)
}
    S526 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u1, u2: User| some p: Photo| (p not in Ad and p in u1.sees) iff (p in  u2.posts and u2 in u1.follows)
}
    S527 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u1, u2: User| some p: Photo| (p not in Ad and p in u1.sees) implies (p in  u2.posts and u2 in u1.follows)
}
    S528 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | #(u.sees & u.posts)=0
  all u1, u2: User| some p: Photo| (p not in Ad and p in u1.sees) implies (p in  u2.posts and u2 in u1.follows)
}
    S529 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | #(u.sees & u.posts & (Photo - Ad))=0
  all u1, u2: User| some p: Photo| (p not in Ad and p in u1.sees) implies (p in  u2.posts and u2 in u1.follows)
}
    S530 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all a: Ad, u: User | a in u.sees
  	all p: Photo - Ad, u: User | p in u.sees iff 
  		some u1: User | u1 in u.follows and u1 != u
}
    S531 in valid iff {
  	all disj u1,u2 : User|
  not (u2 in u1.follows) implies (all p : u1.posts| p in u2.sees implies p in Ad)
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
 
	//all u :User| let p : sees | p.~posts in u.follows
}
    S532 in valid iff {
  	all disj u1,u2 : User|
  (not (u2 in u1.follows)) implies (all p : u1.posts| p in u2.sees implies p in Ad)
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
 	all disj u1,u2 : User| some p : u1.posts| 
(not p in Ad and p in u2.sees) implies (u2 in u1.follows)
	//all u :User| let p : sees | p.~posts in u.follows
}
    S533 in valid iff {
  	all disj u1,u2 : User|
  (not (u1 in u2.follows)) implies (all p : u1.posts| p in u2.sees implies p in Ad)
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
 	all disj u1,u2 : User| some p : u1.posts| 
(not p in Ad and p in u2.sees) implies (u1 in u2.follows)
	//all u :User| let p : sees | p.~posts in u.follows
}
    S534 in valid iff {
  	all u1,u2 : User|
  (not (u2 in u1.follows)) implies (all p : u1.posts| p in u2.sees implies p in Ad)
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
 	all  u1,u2 : User| some p : u1.posts| 
(not p in Ad and p in u2.sees) implies (u2 in u1.follows)
	//all u :User| let p : sees | p.~posts in u.follows
}
    S535 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
all disj u1,u2:User, p:Photo|u1 in u2.follows and p in u1.posts implies p not in Ad
all u:User,p:Photo| p in u.sees implies (p.~posts in u.follows and p not in Ad)
}
    S536 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User | u.sees not in u.follows.posts

}
    S537 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User | u.sees & Ad not in u.follows.posts

}
    S538 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u, u1 : User, p : Photo | u in posts.p  and u1 in follows.u implies u in sees.p and p not in Ad
  

}
    S539 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u, u1 : User, p : Photo | u in posts.p  and u in follows.u1 implies u in sees.p and p not in Ad
  

}
    S540 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all s : User.sees | s not in User.follows.posts & Ad
}
    S541 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | u.sees not in u.follows.posts & Ad
}
    S542 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | u.follows.posts & Ad not in u.sees
}
    S543 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | Ad in u.sees implies Ad in u.follows.posts
}
    S544 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | Ad not in u.follows.posts && u.posts not in u.sees
}
    S545 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | Ad not in u.follows.posts && u.posts & Ad not in u.sees
}
    S546 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | u.follows.posts & Ad not in u.sees
    all u : User | u.posts not in u.sees
}
    S547 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | u.follows.posts not in u.sees

}
    S548 in valid iff {
	// Users can see ads posted by everyone, 
  	all u: User, a: Ad | a in u.sees 
  	// but only see non ads posted by followed users.
  	all u : User, a: Ad | u.sees in u.follows.posts implies no a

}
    S549 in valid iff {
	// Users can see ads posted by everyone, 
  all u: User, p: Photo | u in u.sees implies p in Ad
	// but only see non ads posted by followed users.
  	all u: User, p: Photo | u.follows in u.sees implies p not in Ad

}
    S550 in valid iff {
	// Users can see ads posted by everyone, 
  all u: User, p: Photo | p in u.sees implies p in Ad
	// but only see non ads posted by followed users.
  	all u: User, p: Photo | u.follows in u.sees implies p not in Ad

}
    S551 in valid iff {
	// Users can see ads posted by everyone, 
  all u: User, p: Photo | p in u.sees implies p in Ad
	// but only see non ads posted by followed users.
  	all u: User, u1: User, p: Photo | u1 in u.follows implies p not in Ad

}
    S552 in valid iff {
	// Users can see ads posted by everyone, 
  all u: User, p: Photo | p in u.sees implies p in Ad
	// but only see non ads posted by followed users.
  	all u: User, u1: User, p: Photo | u1 in u.follows implies u.sees not in Ad

}
    S553 in valid iff {
	// Users can see ads posted by everyone, 
  all u: User, p: Photo | p in u.sees implies p in Ad
	// but only see non ads posted by followed users.
  	all u: User, u1: User | u1 in u.follows implies u.sees not in Ad

}
    S554 in valid iff {
	// Users can see ads posted by everyone, 
  all u: User, p: Photo | p in u.sees implies p in Ad
	// but only see non ads posted by followed users.
  	all u, u1: User | u1 in u.follows implies no (u.sees & Ad)

}
    S555 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User, p: Photo |
    (p in Ad) => (p in u.sees)
    else (some u.follows & User) => (p in u.sees)
}
    S556 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User, p : Photo |
        (p in u.sees) <=> (p in Ad or (all f : u.follows | p in f.posts))
}
    S557 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all disj u, q : User | u.sees in (Ad)

}
    S558 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all disj u1,u2: User | all p: Photo | ((u2 not in u1.follows and p not in Ad) => u2.posts not in u1.sees) 
  
}
    S559 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u, y : User | y in u.follows implies y.posts in u.sees
  all u, y : User | y not in u.follows implies y.posts not in u.sees
  all u : User | all a :Ad | a in u.sees

}
    S560 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all disj u1,u2: User | all p: Photo | ((u2 not in u1.follows) and (u2.posts not in Ad)) => (u2.posts not in u1.sees) 
  
}
    S561 in valid iff {
    all u: User, p: Photo |
        (p in Ad => p in u.sees) &&
        (p not in Ad =>
            (some f: u.follows | p in f.posts implies p in u.sees)
            or (some i: Influencer | p in i.posts implies p in u.sees)
        )
}
    S562 in valid iff {
    all u: User, p: Photo |
        (p in Ad => some f: u.follows | p in f.posts or p in Influencer.posts) &&
        (p not in Ad =>
            (some f: u.follows | p in f.posts implies p in u.sees)
            or (some i: Influencer | p in i.posts implies p in u.sees)
        )
}
    S563 in valid iff {
    all u: User, p: Photo |
        -- Les publicités sont visibles par tout le monde
        (p in Ad => p in u.sees) &&
        
        -- Les photos non-publicitaires sont visibles seulement si :
        (p not in Ad =>
            (some f: u.follows | p in f.posts implies p in u.sees)  -- postée par un suivi
            or (some i: Influencer | i in u.follows and p in i.posts implies p in u.sees)  -- postée par un influenceur suivi
        )
}
    S564 in valid iff {
    all u: User, p: Photo |
        -- Un utilisateur ne voit une publicité que si elle a été postée par quelqu'un qu'il suit
        (p in Ad => (some f: u.follows | p in f.posts)) &&
        
        -- Les photos normales ne sont visibles que si :
        (p not in Ad =>
            (some f: u.follows | p in f.posts implies p in u.sees)  -- postée par un suivi
            or (some i: Influencer | i in u.follows and p in i.posts implies p in u.sees)  -- postée par un influenceur suivi
        )
}
    S565 in valid iff {
    all u: User, p: Photo |
        (p in Ad and posts.p != u) => (p in u.sees)  // Une pub est visible par tout le monde sauf son propre posteur
        else (p not in Ad and some f: u.follows | p in f.posts) => (p in u.sees)  // Une non-pub est visible seulement si postée par un suivi
        // Ajouter la contrainte pour que l'utilisateur ne voie pas ses propres posts
        and (posts.p != u => p not in u.sees)  // L'utilisateur ne voit pas ses propres posts
}
    S566 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User, p : Photo |
    p in u.sees <=>
      (p in Ad and all u2 : User | p in u2.posts) or
      (p !in Ad and some u2 : u.follows | p in u2.posts)
}
    S567 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1,u2 : User | u1 in u2.follows => u2.sees not in (u1.posts & Ad)
}
    S568 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1,u2 : User | u2 in u1.follows => u2.sees not in (u1.posts & Ad)
}
    S569 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u1,u2 : User | u1 in u2.follows => u2.sees in (u1.posts & Ad)
}
    S570 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u: User, a: Ad | a in u.sees
  
 	all u: User, p: Photo - Ad |
        (some owner: User | p in owner.posts and owner in u.follows) implies p in u.sees or u.sees in u.posts
}
    S571 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	Ad in User.sees
	all u: User | (u.sees & Ad) in u.follows.posts
}
    S572 in valid iff {
	// Users can see ads posted by everyone, 
	all u: User, a: Ad | some u.sees implies a in u.sees  
  // but only see non ads posted by followed users.
	all u: User, p: Photo | p in u.sees implies posts.p in u.follows
}
    S573 in valid iff {
	// Users can see ads posted by everyone, 
	all u: User, p:Photo | some u.sees implies p in Ad
  // but only see non ads posted by followed users.
	all u: User, p: Photo | p in u.sees implies posts.p in u.follows
}
    S574 in valid iff {
	// Users can see ads posted by everyone, 
	//all u: User, p:Photo | some u.posts in Ad implies u in u.sees
	all u: User, p:Photo | u in sees.p implies p in Ad
  
  // but only see non ads posted by followed users.
	all u: User, p: Photo | p in u.sees implies u.posts in u.follows
}
    S575 in valid iff {
  // Users can see ads posted by everyone, 
	//all u: User, p:Photo | some u.posts in Ad implies u in u.sees
	//all u: User, p:Photo | u in sees.p implies p in Ad and 
	all u: User, p:Photo | u in sees.p implies p in Ad
  // but only see non ads posted by followed users.
	//all u: User, p: Photo | p in u.sees implies u.posts in u.follows
	all u: User|some p: Photo - Ad | p in u.sees implies u in u.follows
 
}
    S576 in valid iff {
  // Users can see ads posted by everyone, 
	//all u: User, p:Photo | some u.posts in Ad implies u in u.sees
	//all u: User, p:Photo | u in sees.p implies p in Ad and 
	all u: User, p: Photo | u in sees.p implies u.posts in Ad     
  //all u: User, p:Photo | u in sees.p implies p in Ad
  // but only see non ads posted by followed users.
	//all u: User, p: Photo | p in u.sees implies u.posts in u.follows
	all u: User|some p: Photo - Ad | p in u.sees implies u in u.follows
}
    S577 in valid iff {
  // Users can see ads posted by everyone, 
	//all u: User, p:Photo | some u.posts in Ad implies u in u.sees
	//all u: User, p:Photo | u in sees.p implies p in Ad and 
	all u: User, p: Photo | u in sees.p implies u.posts in Ad     
  //all u: User, p:Photo | u in sees.p implies p in Ad
  // but only see non ads posted by followed users.
	//all u: User, p: Photo | p in u.sees implies u.posts in u.follows
	all u: User, p:Photo | p not in Ad and p in u.sees implies u in u.follows	
  //all u: User|some p: Photo - Ad | p in u.sees implies u in u.follows
	//all u: User, p:Photo |  
  
}
    S578 in valid iff {
  // Users can see ads posted by everyone, 
	//all u: User, p:Photo | some u.posts in Ad implies u in u.sees
	//all u: User, p:Photo | u in sees.p implies p in Ad and 
	//all u: User, p: Photo | u in sees.p implies u.posts in Ad   
  	all u: User, p: Photo | p in Ad implies u.sees not in u.follows
  //all u: User, p:Photo | u in sees.p implies p in Ad
  // but only see non ads posted by followed users.
	//all u: User, p: Photo | p in u.sees implies u.posts in u.follows
	all u: User, p:Photo | p not in Ad and p in u.sees implies u in u.follows	
  //all u: User|some p: Photo - Ad | p in u.sees implies u in u.follows
	//all u: User, p:Photo |  
  
}
    S579 in valid iff {
  // Users can see ads posted by everyone, 
	//all u: User, p:Photo | some u.posts in Ad implies u in u.sees
	//all u: User, p:Photo | u in sees.p implies p in Ad and 
	//all u: User, p: Photo | u in sees.p implies u.posts in Ad   
  	all u: User, p:Photo| u in sees.Ad implies p in u.posts   	
  
	//all u: User, p: Photo | some u.posts implies u not in u.follows   
	//all u: User, p: Photo | p in Ad implies sees.p not in u.follows
  	//all u: User, p:Photo | u in sees.p implies p in Ad
  
  // but only see non ads posted by followed users.
  	all u: User, p: Photo | p not in Ad implies posts.p in u.follows
  
	//all u: User, p: Photo | p in u.sees implies u.posts in u.follows
	//all u: User, p:Photo | p not in Ad and p in u.sees implies u in u.follows	
  //all u: User|some p: Photo - Ad | p in u.sees implies u in u.follows
	//all u: User, p:Photo |  
  
}
    S580 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User, p : Photo | u.sees = (Ad + follows.posts.p)
}
    S581 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User, p : Photo | (Ad + follows.posts.p) in u.sees
}
    S582 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	all u : User | Ad in u.sees and ((User - u.follows).posts - Ad) not in u.sees
}
    S583 in valid iff {
	// Users can see ads posted by everyone, 
  	all u:User, p: Photo | u in sees.p implies p in Ad
  	all u:User| one p: Photo | u in sees.p implies p in Ad
	// but only see non ads posted by followed users.
  	all u:User, p: Photo - Ad | p in u.sees implies u in posts.p and u in follows.u

}
    S584 in valid iff {
	// Users can see ads posted by everyone, 
  	all u:User, p: Photo | u in sees.p implies p in Ad
  	//all u:User| one p: Photo | u in sees.p implies p in Ad
	
  // but only see non ads posted by followed users.
  	//all u:User, p: Photo| p in u.sees and p not in Ad implies u.follows in posts.p
  	//all disj u1,u2:User, p: Photo| p in u1.sees and p not in Ad implies u1.follows in posts.p
	//all u:User, p: Photo| u in u.follows and p in u.sees and u in posts.p implies p not in Ad
	all u: User, p: Photo| u.follows in posts.p implies p not in Ad
}
    S585 in valid iff {
	// Users can see ads posted by everyone, 
  	all u:User, p: Photo | u in sees.p implies p in Ad
  	//all u:User| one p: Photo | u in sees.p implies p in Ad
	
  // but only see non ads posted by followed users.
  	//all u:User, p: Photo| p in u.sees and p not in Ad implies u.follows in posts.p
  	//all disj u1,u2:User, p: Photo| p in u1.sees and p not in Ad implies u1.follows in posts.p
	//all u:User, p: Photo| u in u.follows and p in u.sees and u in posts.p implies p not in Ad
	all u: User, p: Photo| u.follows in posts.p 
}
    S586 in valid iff {
	// Users can see ads posted by everyone, .
  	all u:User, p: Photo | u in sees.p and posts.p not in u.follows implies p in Ad
  	//all u:User| one p: Photo | u in sees.p implies p in Ad
	
  // but only see non ads posted by followed users.
  	//all u:User, p: Photo| p in u.sees and p not in Ad implies u.follows in posts.p
  	//all disj u1,u2:User, p: Photo| p in u1.sees and p not in Ad implies u1.follows in posts.p
	//all u:User, p: Photo| u in u.follows and p in u.sees and u in posts.p implies p not in Ad
	all u: User, p: Photo| u.follows in posts.p 
}
    S587 in valid iff {
	// Users can see ads posted by everyone, .
  	all u:User, p: Photo | u in sees.p and posts.p not in u.follows implies p in Ad
  	//all u:User| one p: Photo | u in sees.p implies p in Ad
	
  // but only see non ads posted by followed users.
  	//all u:User, p: Photo| p in u.sees and p not in Ad implies u.follows in posts.p
  	//all disj u1,u2:User, p: Photo| p in u1.sees and p not in Ad implies u1.follows in posts.p
	//all u:User, p: Photo| u in u.follows and p in u.sees and u in posts.p implies p not in Ad
//	all u: User, p: Photo| u.follows in posts.p
	all u: User, p: Photo| posts.p in u.follows implies u.sees not in Ad
}
    S588 in valid iff {
	// Users can see ads posted by everyone, .
  	all u:User, p: Photo | u in sees.p and posts.p not in u.follows implies p in Ad
  	//all u:User| one p: Photo | u in sees.p implies p in Ad
	
  // but only see non ads posted by followed users.
  	//all u:User, p: Photo| p in u.sees and p not in Ad implies u.follows in posts.p
  	//all disj u1,u2:User, p: Photo| p in u1.sees and p not in Ad implies u1.follows in posts.p
	//all u:User, p: Photo| u in u.follows and p in u.sees and u in posts.p implies p not in Ad
//	all u: User, p: Photo| u.follows in posts.p
//	all u: User, p: Photo| posts.p in u.follows implies u.sees
	all u: User, p: Photo| p not in Ad implies u.follows in posts.p
}
    S589 in valid iff {
	// Users can see ads posted by everyone, .
  	all u:User, p: Photo | u.sees in posts.p implies p in Ad
//  	all u:User, p: Photo | (u in sees.p) and (posts.p not in u.follows) implies p in Ad
  	//all u:User| one p: Photo | u in sees.p implies p in Ad
	
  // but only see non ads posted by followed users.
  	//all u:User, p: Photo| p in u.sees and p not in Ad implies u.follows in posts.p
  	//all disj u1,u2:User, p: Photo| p in u1.sees and p not in Ad implies u1.follows in posts.p
	//all u:User, p: Photo| u in u.follows and p in u.sees and u in posts.p implies p not in Ad
//	all u: User, p: Photo| u.follows in posts.p
//	all u: User, p: Photo| posts.p in u.follows implies u.sees
	all u: User, p: Photo| p not in Ad implies u.follows in posts.p
}
    S590 in valid iff {
	// Users can see ads posted by everyone, .
  	all u:User, p: Photo | u in sees.p implies p in Ad 
  	//all u:User, p: Photo | u.sees in posts.p implies p in Ad
//  	all u:User, p: Photo | (u in sees.p) and (posts.p not in u.follows) implies p in Ad
  	//all u:User| one p: Photo | u in sees.p implies p in Ad
	
  // but only see non ads posted by followed users.
  	//all u:User, p: Photo| p in u.sees and p not in Ad implies u.follows in posts.p
  	//all disj u1,u2:User, p: Photo| p in u1.sees and p not in Ad implies u1.follows in posts.p
	//all u:User, p: Photo| u in u.follows and p in u.sees and u in posts.p implies p not in Ad
//	all u: User, p: Photo| u.follows in posts.p
//	all u: User, p: Photo| posts.p in u.follows implies u.sees
	all u: User, p: Photo| p not in Ad implies u.follows in posts.p
}
    S591 in valid iff {
	// Users can see ads posted by everyone, 
	all u: User, p: Photo | u in sees.p implies p in Ad 
  // but only see non ads posted by followed users.
	all u1: User, p: Photo | some u2: User| (u2 in sees.p) and u1 in posts.p implies u2 in u1.follows  
}
    S592 in valid iff {
	// Users can see ads posted by everyone, 
	all u: User, p: Photo | u in sees.p implies p in Ad or
  // but only see non ads posted by followed users.
	all u1: User, p: Photo | some u2: User| (u2 in sees.p) and u1 in posts.p implies u2 in u1.follows  
}
    S593 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u: User | all a: Ad | all p: Photo - Ad | a in u.sees and (p in u.sees implies (some u2: User | p in u2.posts and u2 in u.follows))

}
    S594 in valid iff {

  all u: User | all a: Ad | a in u.sees
  
  and
  
  all u: User | all p: Photo - Ad | p in u.sees implies (p in u.posts or p in u.(follows.posts))
}
    S595 in valid iff {

  all u: User | all a: Ad | a in u.sees
  
  and
  
  all u: User | all p: Photo - Ad | one u2: User | p in u.sees implies (p in u2.posts and u2 in u.follows)
}
    S596 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  	all u : User, a : Ad | u -> a in sees
  	all u : User | some u1 : User, p : Photo | u1 -> p in posts and u -> u1 in follows implies u -> p in sees
	
}
    S597 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  some u :User | some a :Ad | a in u.sees
  some u1,u2 :User | some p :Photo | p in u1.sees implies u2 in u1.follows

}
    S598 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  some u :User | some a :Ad | a in u.sees
  some u1,u2 :User | some p :Photo - Ad | p in u1.sees implies u2 in u1.follows

}
    S599 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u :User | some a :Ad | a in u.sees
  some u1,u2 :User | some p :Photo| p in u1.sees implies u2 in u1.follows

}
    S600 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all a:Ad | a in User.sees
  all p:Photo - Ad | all u:User | p in u.follows.posts
}
    S601 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all a:Ad | a in User.sees
  all u:User, p:Photo - Ad, f:u.follows  | p in f.posts
}
    S602 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all a:Ad | a in User.sees
  all u:User - Influencer, p:Photo - Ad, f:u.follows  | p in f.posts
}
    S603 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all a:Ad | a in User.sees
  all u:User, p:Photo - Ad, f:u.follows  | p in u.sees and p in f.posts 
}
    S604 in valid iff {
	all u: User | some p:Photo | p in u.sees => posts.p in u.follows
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.

}
    S605 in valid iff {
	// Users can see ads posted by everyone, 
  all p : Ad | all i:Influencer | not p in i.sees 
	// but only see non ads posted by followed users.

}
    S606 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User | all a:Ad | a in u.sees iff a in User.posts and (u.sees - a) in (u.follows.posts)

}
    S607 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User | some a : Ad | (a in u.sees iff a in User.posts) and (u.sees - Ad) in 	u.follows.posts

}
    S608 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User | some a : Ad | (a in u.sees implies a in User.posts) and (u.sees - Ad) in 	u.follows.posts

}
    S609 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u : User | all a : Ad | (a in u.sees implies a in User.posts) and (u.sees - Ad) in 	u.follows.posts

}
    S610 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
	
	(all u : User | (Ad - u.posts) in u.sees) and
	all u : User | no (u.sees & (Photo - (u.follows.posts + Ad - u.posts)))
  	
  	
}
    S611 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u:User | all a:Ad | a not in u.sees implies (u.sees in u.follows.posts)

}
    S612 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
  all u:User - Influencer | all a:Ad | a not in u.sees implies (u.sees in u.follows.posts)

}
    S613 in valid iff {
	// Users can see ads posted by everyone, 
	// but only see non ads posted by followed users.
all u :User |
  u.sees= ((u.follows+u.suggested).posts & Ad) +(u.follows.posts -Ad)
}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, S74, S75, S76, S77, S78, S79, S80, S81, S82, S83, S84, S85, S86, S87, S88, S89, S90, S91, S92, S93, S94, S95, S96, S97, S98, S99, S100, S101, S102, S103, S104, S105, S106, S107, S108, S109, S110, S111, S112, S113, S114, S115, S116, S117, S118, S119, S120, S121, S122, S123, S124, S125, S126, S127, S128, S129, S130, S131, S132, S133, S134, S135, S136, S137, S138, S139, S140, S141, S142, S143, S144, S145, S146, S147, S148, S149, S150, S151, S152, S153, S154, S155, S156, S157, S158, S159, S160, S161, S162, S163, S164, S165, S166, S167, S168, S169, S170, S171, S172, S173, S174, S175, S176, S177, S178, S179, S180, S181, S182, S183, S184, S185, S186, S187, S188, S189, S190, S191, S192, S193, S194, S195, S196, S197, S198, S199, S200, S201, S202, S203, S204, S205, S206, S207, S208, S209, S210, S211, S212, S213, S214, S215, S216, S217, S218, S219, S220, S221, S222, S223, S224, S225, S226, S227, S228, S229, S230, S231, S232, S233, S234, S235, S236, S237, S238, S239, S240, S241, S242, S243, S244, S245, S246, S247, S248, S249, S250, S251, S252, S253, S254, S255, S256, S257, S258, S259, S260, S261, S262, S263, S264, S265, S266, S267, S268, S269, S270, S271, S272, S273, S274, S275, S276, S277, S278, S279, S280, S281, S282, S283, S284, S285, S286, S287, S288, S289, S290, S291, S292, S293, S294, S295, S296, S297, S298, S299, S300, S301, S302, S303, S304, S305, S306, S307, S308, S309, S310, S311, S312, S313, S314, S315, S316, S317, S318, S319, S320, S321, S322, S323, S324, S325, S326, S327, S328, S329, S330, S331, S332, S333, S334, S335, S336, S337, S338, S339, S340, S341, S342, S343, S344, S345, S346, S347, S348, S349, S350, S351, S352, S353, S354, S355, S356, S357, S358, S359, S360, S361, S362, S363, S364, S365, S366, S367, S368, S369, S370, S371, S372, S373, S374, S375, S376, S377, S378, S379, S380, S381, S382, S383, S384, S385, S386, S387, S388, S389, S390, S391, S392, S393, S394, S395, S396, S397, S398, S399, S400, S401, S402, S403, S404, S405, S406, S407, S408, S409, S410, S411, S412, S413, S414, S415, S416, S417, S418, S419, S420, S421, S422, S423, S424, S425, S426, S427, S428, S429, S430, S431, S432, S433, S434, S435, S436, S437, S438, S439, S440, S441, S442, S443, S444, S445, S446, S447, S448, S449, S450, S451, S452, S453, S454, S455, S456, S457, S458, S459, S460, S461, S462, S463, S464, S465, S466, S467, S468, S469, S470, S471, S472, S473, S474, S475, S476, S477, S478, S479, S480, S481, S482, S483, S484, S485, S486, S487, S488, S489, S490, S491, S492, S493, S494, S495, S496, S497, S498, S499, S500, S501, S502, S503, S504, S505, S506, S507, S508, S509, S510, S511, S512, S513, S514, S515, S516, S517, S518, S519, S520, S521, S522, S523, S524, S525, S526, S527, S528, S529, S530, S531, S532, S533, S534, S535, S536, S537, S538, S539, S540, S541, S542, S543, S544, S545, S546, S547, S548, S549, S550, S551, S552, S553, S554, S555, S556, S557, S558, S559, S560, S561, S562, S563, S564, S565, S566, S567, S568, S569, S570, S571, S572, S573, S574, S575, S576, S577, S578, S579, S580, S581, S582, S583, S584, S585, S586, S587, S588, S589, S590, S591, S592, S593, S594, S595, S596, S597, S598, S599, S600, S601, S602, S603, S604, S605, S606, S607, S608, S609, S610, S611, S612, S613 extends Formula {}

run {
    #valid.Oracle = 1
    #(Instance - valid.Oracle) = 1
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 12 Atom, exactly 4 UserAtom, exactly 4 PhotoAtom, exactly 4 DayAtom,
       exactly 2 Instance, 6 Int
