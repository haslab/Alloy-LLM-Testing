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
    // Earlier requirement 4, required in every Instance.
{
	// Influencers are followed by everyone else.
	all i : Influencer, u : User - i | i in u.follows
}
    // Earlier requirement 5, required in every Instance.
{
	// Influencers post every day.
	all d : Day, i : Influencer | d in i.posts.date
}
    // Earlier requirement 6, required in every Instance.
{
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User | u.suggested = (u.follows.follows - u.follows - u)
	
}
    Oracle in valid iff {
	// A user only sees ads from followed or suggested users.
  all u : User | posts.(u.sees & Ad) in (u.follows + u.suggested)
}
    S1 in valid iff {
	// A user only sees ads from followed or suggested users.
  
}
    S2 in valid iff {
	// A user only sees ads from followed or suggested users.
	User.sees in Ad
}
    S3 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u : User | sees.(u.sees & Ad) in (u.follows + u.suggested)
}
    S4 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u : User | u.sees = u.follows.posts + u.suggested.posts
}
    S5 in valid iff {
	// A user only sees ads from followed or suggested users.
  
  all u: User, f : u.follows, s: u.suggested | u.sees in f or u.sees in s

}
    S6 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u : User | u.sees = u.follows.posts & u.suggested.posts
}
    S7 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u : User | some u.sees + Ad
}
    S8 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all u: User | ((u.suggested + u.follows).posts) in u.sees

}
    S9 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u : User | (u.follows.posts & u.suggested.posts + u.posts) in Ad
}
    S10 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u : User | (u.follows.posts + u.suggested.posts - u.posts) in Ad
}
    S11 in valid iff {
	// A user only sees ads from followed or suggested users.
  // all u : User | (u.follows.posts + u.suggested.posts) in Ad
  all u : User | (u.follows.posts + u.suggested.posts) in Ad implies u.sees = (u.follows.posts + u.suggested.posts)

}
    S12 in valid iff {
	// A user only sees ads from followed or suggested users.
  // all u : User | (u.follows.posts + u.suggested.posts) in Ad
  all u : User | (u.follows.posts + u.suggested.posts + u.follows.follows.posts) = u.sees// in Ad

}
    S13 in valid iff {
	// A user only sees ads from followed or suggested users.
  // all u : User | (u.follows.posts + u.suggested.posts) in Ad
  all u : User | (u.follows.posts + u.suggested.posts) in u.sees & Ad

}
    S14 in valid iff {
	// A user only sees ads from followed or suggested users.
  // all u : User | (u.follows.posts + u.suggested.posts) in Ad
  all u : User | (u.follows.posts  - u.posts/*u.suggested.posts*/) in u.sees & Ad

}
    S15 in valid iff {
	// A user only sees ads from followed or suggested users.
  // all u : User | (u.follows.posts + u.suggested.posts) in Ad
  all u : User | (u.follows.posts + u.suggested.posts) in (u.posts & Ad)

}
    S16 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u : User, p : Ad - u.posts| (u.follows.posts + u.suggested.posts) in p

}
    S17 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all u : User | u.sees  & Ad = (u.follows.posts + u.suggested.posts) 

}
    S18 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u: User | u.sees = ((u.follows.posts + u.suggested.posts) & Ad)
}
    S19 in valid iff {
	// A user only sees ads from followed or suggested users.
    all u:User | (Ad & (u.follows.posts + u.suggested.posts)) = (Ad & u.sees)
}
    S20 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all u: User | ((u.suggested + u.follows).posts & Ad) in u.sees

}
    S21 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u : User | ((u.follows.posts + u.suggested.posts) <: Ad in u.sees) and no u.posts

}
    S22 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u : User | ((u.follows.posts + u.suggested.posts) <: Ad in u.sees) and u.sees not in u.posts

}
    S23 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u : User | u.posts not in u.sees and ((u.follows.posts + u.suggested.posts) <: Ad ) in u.sees

}
    S24 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all u: User | all p: u.posts | p not in u.sees
  	all u: User | ((u.suggested + u.follows).posts & Ad) in u.sees

}
    S25 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u : User | (u.posts & u.sees = none) and ((u.follows.posts + u.suggested.posts)) in u.sees

}
    S26 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u : User | (u.posts & u.sees = none) and ((u.follows.posts <: Ad = u.sees) or (u.suggested.posts <: Ad = u.sees))

}
    S27 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u : User | (u.posts & u.sees = none) and ((u.follows.posts <: Ad = u.sees <: Ad) or (u.suggested.posts <: Ad = u.sees))

}
    S28 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u : User | (u.posts & u.sees = none) and ((u.follows.posts <: Ad = u.sees <: Ad) or (u.suggested.posts <: Ad = u.sees <: Ad))

}
    S29 in valid iff {
	// A user only sees ads from followed or suggested users.
  all a: Ad | some u1: User| a in u1.sees implies some u2 : User | a in u2.posts and u2 in {u1.suggested + u1.follows}

}
    S30 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u: User, a: Ad | (
    a in u.sees implies posts.a in u.follows
  )
}
    S31 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all u: User | all p: u.posts | p not in u.sees
  	all u: User | Ad - ((u.suggested + u.follows).posts & Ad) not in u.sees
  	all u: User | ((u.suggested + u.follows).posts & Ad) in u.sees

}
    S32 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u: User, a: Ad | some f: u.follows| some s: u.suggested| a in u.sees implies (f.posts in Ad or s.posts in Ad)

}
    S33 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u: User, a: Ad | some f: u.follows| some s: u.suggested| a in u.sees implies (a in f.posts or a in s.posts)

}
    S34 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u: User, a: Ad | all f: u.follows| all s: u.suggested| a in u.sees implies (a in f.posts or a in s.posts)

}
    S35 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u: User, a: Ad | some f: u.follows| some s: u.suggested| a in u.sees iff (a in f.posts or a in s.posts)

}
    S36 in valid iff {
	// A user only sees ads from followed or suggested users.
  //all u: User, a: Ad | some f: u.follows| some s: u.suggested| a in u.sees implies (a in f.posts or a in s.posts)
all u: User, a: Ad | some f: u.follows| some s: u.suggested| a in f.posts or a in s.posts implies a in u.sees
}
    S37 in valid iff {
	// A user only sees ads from followed or suggested users.
  //all u: User, a: Ad | some f: u.follows| some s: u.suggested| a in u.sees implies (a in f.posts or a in s.posts)
all u: User, a: Ad | all f: u.follows| all s: u.suggested| a in f.posts or a in s.posts implies a in u.sees
}
    S38 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u: User, a: Ad | all f: u.follows| some s: u.suggested| a in u.sees implies (a in f.posts or a in s.posts)
//all u: User, a: Ad | all f: u.follows| all s: u.suggested| a in f.posts or a in s.posts implies a in u.sees
}
    S39 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u: User, a: Ad | some f: u.follows| all s: u.suggested| a in u.sees implies (a in f.posts or a in s.posts)
//all u: User, a: Ad | all f: u.follows| all s: u.suggested| a in f.posts or a in s.posts implies a in u.sees
}
    S40 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u: User, s: u.sees | all u1: u.follows, u2: u.suggested | (s in u1.posts) or (s in u2.posts)
}
    S41 in valid iff {
	// A user only sees ads from followed or suggested users.
	all ad: Ad, u: User| ad in u.sees implies all v: u.follows + u.suggested - u | ad in v.posts
}
    S42 in valid iff {
	// A user only sees ads from followed or suggested users.
	//all ad: Ad, u: User| ad in u.sees implies all v: u.follows + u.suggested - u | ad in v.posts
  	all ad: Ad, u: User| ad in u.follows + u.suggested

}
    S43 in valid iff {
	// A user only sees ads from followed or suggested users.
	//all ad: Ad, u: User| ad in u.sees implies all v: u.follows + u.suggested - u | ad in v.posts
  	all ad: Ad, u: User| ad in (u.follows + u.suggested).sees

}
    S44 in valid iff {
	// A user only sees ads from followed or suggested users.
  
// all x:User, y:Photo | x->y in sees and y in Ad implies 
// (all z:User | z->y in posts => x->z in follows or x->z in suggested)

// all x:User, y:Photo | y in x.sees & Ad implies 
//  (all z:User | z in posts.y => z in x.follows + x.suggested)

// all x:User, y: x.sees & Ad | posts.y in (x.follows + x.suggested)

// all x:User, y: x.sees & Ad | posts.y in x.(follows+suggested)

     all a : Ad | posts.a in sees.a.(follows+suggested)
}
    S45 in valid iff {
	// A user only sees ads from followed or suggested users.
  
// all x:User, y:Photo | x->y in sees and y in Ad implies 
// (all z:User | z->y in posts => x->z in follows or x->z in suggested)

// all x:User, y:Photo | y in x.sees & Ad implies 
//  (all z:User | z in posts.y => z in x.follows + x.suggested)

// all x:User, y: x.sees & Ad | posts.y in (x.follows + x.suggested)

// all x:User, y: x.sees & Ad | posts.y in x.(follows+suggested)

     all a : Ad | posts.a in sees.a[follows+suggested]
}
    S46 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u1,u2 : User, a : Ad | a in u1.sees implies u2 in u1.follows or u2 in u1.follows.follows
}
    S47 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u1,u2 : User, a : Ad | a in u1.sees and a in u2.posts implies u2 in u1.follows or u2 in u1.follows.follows
}
    S48 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u : User | u.sees in Ad & ( u.follows.posts + u.suggested.posts)
}
    S49 in valid iff {
	// A user only sees ads from followed or suggested users.
	all x: User, y: Photo | y in x.sees and y in Ad implies y.posts = x.follows + x. suggested
}
    S50 in valid iff {
	// A user only sees ads from followed or suggested users.
	all x: User, y: Photo | y in x.sees and y in Ad implies posts.y = x.follows + x. suggested
}
    S51 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u : User | all a : Ad | a in u.sees => (some u : User | a in u.posts => a in u.suggested or a in u.follows) 

}
    S52 in valid iff {
	// A user only sees ads from followed or suggested users.
	all x: User, y: Photo | y in x.sees and y in Ad implies y = (x.follows + x. suggested).posts
}
    S53 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u : User | all us : u.sees | us in Ad implies (us in u.follows or us in u.suggested.posts)
}
    S54 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all u : User | u.sees.posts & Ad = u.follows.posts & Ad+ u.suggested.posts & Ad

}
    S55 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all u: User | u.sees = follows.u.posts + u.suggested.posts
}
    S56 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u:User | u.sees in Ad implies u.sees in u.suggested.posts or u.sees in u.follows.posts

}
    S57 in valid iff {
	// A user only sees ads from followed or suggested users.
  
  all u : User | u.sees = (Photo-Ad) + (Ad & u.follows.posts)

}
    S58 in valid iff {
	// A user only sees ads from followed or suggested users.
  
  all u:User | u.sees = (Photo-Ad) + (Ad & (u.follows.posts + u.suggested.posts))

}
    S59 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u : User | Ad in u.sees implies Ad in u.follows.posts + u.suggested
}
    S60 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all u : User, a : Ad | a in u.sees iff posts.a in u.follows or posts.a in a.suggested 

}
    S61 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all u : User, a : Ad | a in u.sees iff posts.a in u.follows or posts.a in u.suggested 

}
    S62 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u : User, a : u.sees & Ad | posts.a in u.follows + u
}
    S63 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all u : User, ad : Ad | (ad in u.sees) implies (ad in follows.u.posts) or (ad in suggested.u.posts)
  

}
    S64 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u: User | some a : Ad | (a in u.sees) and (a in u.suggested.posts or a in u.follows.posts)

}
    S65 in valid iff {
	// A user only sees ads from followed or suggested users.
  all p : User.sees & Ad | p in User.follows.posts or p in User.suggested.posts 

}
    S66 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u : User | u.sees in (Ad & (u.follows.posts + u.follows.follows.posts))
}
    S67 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u: User | (posts.(u.sees & Ad) - u) in (u.follows + u.suggested)
}
    S68 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u: User | Ad in u.sees iff Ad in u.follows.posts or Ad in u.suggested.posts
}
    S69 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u : User | some a: Ad| a in u.follows.posts 


}
    S70 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u : User | all a : Ad | a in u.sees

}
    S71 in valid iff {
	// A user only sees ads from followed or suggested users.
	one u:User | u.sees in u.follows.posts + Ad or u.sees in u.suggested.posts + Ad
}
    S72 in valid iff {
	// A user only sees ads from followed or suggested users.
	some u:User | u.sees in u.follows.posts + Ad or u.sees in u.suggested.posts + Ad
}
    S73 in valid iff {
	// A user only sees ads from followed or suggested users.
	some u:User | u.sees in follows.u.posts + Ad or u.sees in suggested.u.posts + Ad
}
    S74 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all u: User, s: u.sees, f: u.follows, ss: u.suggested|
  	s in Ad implies s in f or s in ss

}
    S75 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u : User, p : Ad | 
	p in u.sees implies (p in u.follows.sees or p in u.suggested.sees)
}
    S76 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u: User | no (Ad - u.follows.posts - u.suggested.posts) - u.sees
}
    S77 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u : User | u.sees = u.follows.posts + u.suggested.posts & Ad

}
    S78 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u: User| all x: u.follows| all  g : u.suggested| u.sees = (x.posts + u.posts)

}
    S79 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u: User| all x: u.follows| all g : u.suggested| u.sees = (x.posts + g.posts)

}
    S80 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u: User| all x: u.follows.posts| all  g: u.suggested.posts| Ad in u.sees => Ad in x or Ad in g
}
    S81 in valid iff {
    all u: User, p: Photo |
        (p in Ad or (p in u.follows.posts or p in u.suggested.posts)) implies p in u.sees
}
    S82 in valid iff {
  // A user only sees ads from followed or suggested users.
  all u: User, p: Photo | p in u.sees implies (p in u.follows.posts or p in u.follows.suggested.posts)
}
    S83 in valid iff {
	// A user only sees ads from followed or suggested users.
    all u: User | all p: Photo | p in u.sees => (p in u.follows.posts + u.suggested.posts => Ad in p)

}
    S84 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u : User - Influencer, p : Photo | p in u.sees & Ad implies p in u.follows.posts & u.suggested.posts

}
    S85 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u : User | (Ad - (u.follows + u.suggested).posts) not in u.sees
}
    S86 in valid iff {
	// A user only sees ads from followed or suggested users.
  //all u : User | (u.sees & Ad) = (u.follows.posts & Ad) + (u.suggested.posts & Ad)
  all a : Ad | sees.a = follows.posts.a + suggested.posts.a + posts.a

}
    S87 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u : User | some a : Ad | u -> a in sees implies a in u.follows.posts or a in u.suggested.posts
}
    S88 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all u : User, us : User.sees | some f : u.follows, s : u.suggested | us in Ad implies us in f.posts or us in s.posts

}
    S89 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u : User | u.sees = u.follows.posts or u.sees = u.suggested.posts
}
    S90 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u : User | u.sees & Ad = u.follows + u.suggested
}
    S91 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u : User | u.sees & Ad = (follows.u + u.suggested).sees & Ad
}
    S92 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u : User | u.sees & Ad in (follows.u + u.suggested).sees & Ad
}
    S93 in valid iff {
  	all x,y,z: User, p: Photo | (x -> p in sees implies p in Ad and y -> p in posts) or (x -> z in follows and z -> y in follows and x -> y in suggested and y -> p in posts)
	// A user only sees ads from followed or suggested users.

}
    S94 in valid iff {
  	all x,y,z: User, p: Photo | x -> p in sees implies (p in Ad and y -> p in posts) or (x -> z in follows and z -> y in follows implies x -> y in suggested and y -> p in posts)
	// A user only sees ads from followed or suggested users.

}
    S95 in valid iff {
	all x: User, p: Photo | x -> p in sees implies p in Ad and some y: User | y -> p in posts implies (x -> y in follows or x -> y in suggested)
	// A user only sees ads from followed or suggested users.

}
    S96 in valid iff {
	all x: User, a: Ad | x -> a in sees and some y: User | y -> a in posts implies (x -> y in follows or x -> y in suggested)
	// A user only sees ads from followed or suggested users.

}
    S97 in valid iff {
	all x: User, p: Photo | x -> p in sees implies p in Ad and one y: User | y -> p in posts implies ( x -> y in follows or x -> y in suggested)
	// A user only sees ads from followed or suggested users.

}
    S98 in valid iff {
	all x: User, p: Photo | x -> p in sees implies p in Ad and some y: User | y -> p in posts and ( x -> y in follows or y -> x in suggested)
	// A user only sees ads from followed or suggested users.

}
    S99 in valid iff {
	// A user only sees ads from followed or suggested users.
   all u : User | ( u.sees & Ad ) in u.follows.posts or ( u.sees & Ad )  in u.suggested.posts

}
    S100 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u : User |some a : Ad |a in u.sees implies a in u.follows or a in u.suggested
}
    S101 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all u1, u2 : User, y : Ad | y in u2.posts and y in u1.sees implies u2 in follows.u1 or u2 in suggested.u1 or u2 in Influencer

}
    S102 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u,u1 : User, a : Ad | u1 in posts.a and u in sees.a implies u in follows.u1 or u1 in suggested.u

}
    S103 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all a : Ad, u : sees.Ad | a in (u.follows.posts + u.suggested.posts)
  
  		

}
    S104 in valid iff {
	// A user only sees ads from followed or suggested users.
    all u:User, a:Ad | Ad in u.sees implies Ad in (u.follows.posts + u.suggested.posts)
}
    S105 in valid iff {
	// A user only sees ads from followed or suggested users.
    all u:User, a:Ad |  (u.sees & Ad) = (u.follows.posts + u.suggested.posts)
}
    S106 in valid iff {
	// A user only sees ads from followed or suggested users.
   all u: User | some Ad & u.sees implies u.follows.posts in Ad and u.suggested.posts in Ad
}
    S107 in valid iff {
	// A user only sees ads from followed or suggested users.
   all u: User | some Ad & (u.sees - u.posts) implies u.follows.posts in Ad and u.suggested.posts in Ad
}
    S108 in valid iff {
	// A user only sees ads from followed or suggested users.
	// user sees a in ads iff 
  	all u : User |
  		all a : Ad |
  			a in u.sees iff
  				(some y : User | y in u.follows or y in u.suggested and a in y.posts)

}
    S109 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u: User | (u.sees in u.follows.posts) or (u.sees in u.suggested.posts)
 }
    S110 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u: User | u.sees in (Ad - u.follows.posts & Ad - u.suggested.posts)
 }
    S111 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u: User | u.sees not in (Ad - (u.follows.posts + u.suggested.posts))
 }
    S112 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u: User | u.sees not in (Ad - u.follows.posts + Ad - u.suggested.posts)
 }
    S113 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u: User | u.sees not in ((Ad + u.posts) - (u.follows.posts + u.suggested.posts)) or u.sees in none
 }
    S114 in valid iff {
	// A user only sees ads from followed or suggested users.
  all x : User, y : Photo | x->y in sees and y in Ad implies some z: User | x->z in follows or x->z in suggested
  }
    S115 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u : User | u.sees & Ad = u.follows || u.sees & Ad = u.suggested
}
    S116 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u: User | some ad: Ad | ad in u.sees implies (some f: User | u in f.follows or u in f.suggested and ad in f.posts)
}
    S117 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u: User {
		u.follows.posts & Ad in u.sees
		u.suggested.posts & Ad in u.sees
		(Ad - u.follows.posts & Ad - u.suggested.posts & Ad) not in u.sees
	} 
}
    S118 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u : User | (u.follows+ u.suggested) in posts.(u.sees & Ad)

}
    S119 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u: User | (posts.(u.posts & Ad) - u) = (u.follows + u.suggested)
}
    S120 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u: User | all s: u.sees | u.sees in Ad implies s in (u.follows + u.suggested).posts
}
    S121 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u:User, a:Ad | a in u.sees implies posts.Ad in u.follows or posts.Ad in u.suggested
}
    S122 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u1,u2:User, a:Ad | u2 in posts.Ad and a in u1.sees and u1!=u2 
  		implies u2 in u1.follows or u2 in u1.suggested 
  
}
    S123 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u: User, seg: u.follows | u != seg implies Ad in seg.sees or Ad in u.suggested
}
    S124 in valid iff {
    all u : User, seg : u.follows |
        u != seg implies 
            all ad : Ad | 
                ad in u.sees implies 
                    (ad in seg.sees or ad in seg.suggested)
}
    S125 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u: User, seg: u.follows | u != seg implies Ad in seg.posts or Ad in u.suggested
}
    S126 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all u : User, a : Ad, u2 : User.follows + User.suggested| a in u.sees implies (a in u2.posts)

}
    S127 in valid iff {
  all u : User, a : Photo| a in Ad and a in u.sees implies (some u1: User | u1 in u.follows and a in u.posts) or (some u2: User | u2 in u.suggested and a in u2.posts)
  
	// A user only sees ads from followed or suggested users.

}
    S128 in valid iff {
	// A user only sees ads from followed or suggested users.

  all u, u1 : User, p : Photo |  u != u1 and u in follows.u1 or u1 in suggested.u implies p in Ad
  
}
    S129 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u : User | u.sees & Ad in follows.u.posts + u.suggested.posts
}
    S130 in valid iff {
	// A user only sees ads from followed or suggested users.
  	
  	all u: User | u.sees & Ad = ( u.follows.posts + u.suggested.posts + Influencer.posts ) & Ad

}
    S131 in valid iff {
	// A user only sees ads from followed or suggested users.
	all a: Ad | lone u: sees.a.follows + sees.a.suggested | Ad in u.sees
}
    S132 in valid iff {
	// A user only sees ads from followed or suggested users.
	all a: Ad | lone u: sees.a.follows + sees.a.suggested - posts.a | Ad in u.sees
}
    S133 in valid iff {
	// A user only sees ads from followed or suggested users.
          all x: User | (sees.Ad in (x.follows + x.suggested + x))



}
    S134 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u: User | all f,s: User | all ad: Ad | f in u.follows and s in u.suggested and (ad in u.sees) implies (ad in u.follows.posts or ad in s.follows.posts)

}
    S135 in valid iff {
	// A user only sees ads from followed or suggested users.
 	// all user some user.follows
  	// if user see add implies poster is followed or suggested
  all u,z : User, a : Ad |
  	a in u.sees iff
  		(z in u.follows or z in u.suggested) and a in z.posts and z != u
  
  
  
  

}
    S136 in valid iff {
	// A user only sees ads from followed or suggested users.
 	// all user some user.follows
  	// if user see add implies poster is followed or suggested
  all u : User, a : Ad, z : u.follows + u.suggested |
  	a in u.sees iff
  		a in z.posts and z != u
  
  
 

}
    S137 in valid iff {
	// A user only sees ads from followed or suggested users.
 	// all user some user.follows
  	// if user see add implies poster is followed or suggested
  all u : User, a : Ad | some z : u.follows + u.suggested |
  	a in u.sees iff
  		a in z.posts and z != u
  
  
 

}
    S138 in valid iff {
	// A user only sees ads from followed or suggested users.
 	// all user some user.follows
  	// if user see add implies poster is followed or suggested
  all u : User, a : Ad | some z : u.follows + u.suggested |
  	a in u.sees iff
  		a in z.posts and z != u
  
  all u : User | some y : User | some a : y.posts |
  	a in Ad and a in u.sees implies 
  		(y in u.follows or y in u.suggested)
  	
  
 

}
    S139 in valid iff {
	// A user only sees ads from followed or suggested users.
 	// all user some user.follows
  	// if user see add implies poster is followed or suggested
  //all u : User, a : Ad | some z : u.follows + u.suggested |
  //	a in u.sees iff
  //		a in z.posts and z != u
  
  all u : User | some y : User | some a : y.posts |
  	a in Ad and a in u.sees implies 
  		(y in u.follows or y in u.suggested)
  

}
    S140 in valid iff {
	// A user only sees ads from followed or suggested users.
 	// all user some user.follows
  	// if user see add implies poster is followed or suggested
  //all u : User, a : Ad | some z : u.follows + u.suggested |
  //	a in u.sees iff
  //		a in z.posts and z != u
  
  all u : User | some y : User | some a : y.posts |
  	a in Ad and u != y and a in u.sees implies 
  		(y in u.follows or y in u.suggested)
  

}
    S141 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u : User | u.sees not in (u.follows.posts & u.suggested.posts & Photo - Ad)
}
    S142 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u, u2: User | all a: Ad |( u != u2 and a in u.sees) implies a in u2.posts and u2 in u.follows or u2 in u.suggested
}
    S143 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u:User, a:Ad| u.sees in a implies ((posts.a in u.follows) or (posts.a in u.suggested))
}
    S144 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u : User, p : Ad | 
  	u.sees = u.follows & u.suggested 
}
    S145 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u : User, p : Photo | 
	p in u.sees implies (p in u.follows.sees or p in u.suggested.sees)
}
    S146 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u : User, p : Photo | 
	 p in u.sees implies (p in u.follows.sees or p in u.suggested.sees or p in Ad)
}
    S147 in valid iff {
	// A user only sees ads from followed or suggested users.
   all u: User, su: User |
        su in u.suggested =>
            su not in u.follows and
            some f: User | f in u.follows.follows and su in f.follows


}
    S148 in valid iff {
	// A user only sees ads from followed or suggested users.
     all u: User, su: User |
        su in u.suggested =>
            su not in u.follows and
            some f: User | f in (u.follows.follows - u.follows) && su in f.follows


}
    S149 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all disj u1, u2: User, p: Ad | p in u1.sees implies (
      p in u2.posts and (u2 in u1.follows or u2 in u1.suggested))

}
    S150 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all p: Ad | p in User.posts
  	all p: Photo, u: User | p in u.posts implies p not in u.sees
  	all disj u1, u2: User, p: Ad | p in u1.sees implies (
      p in u2.posts and (u2 in u1.follows or u2 in u1.suggested))

}
    S151 in valid iff {
	// A user only sees ads from followed or suggested users.
	all x, z : User| some p : Photo | x != z and (x in follows.z or x in suggested.z) implies p not in Ad
  
}
    S152 in valid iff {
	// A user only sees ads from followed or suggested users.
	all x, z : User| some p : Photo | x != z and z in posts.p and x in sees.p
  //and (x in follows.z or x in suggested.z) implies p not in Ad
  
}
    S153 in valid iff {
	// A user only sees ads from followed or suggested users.
	all x, z : User| some p : Photo | x != z and z in posts.p and x in sees.p and (x in follows.z or x in suggested.z) implies p not in Ad
  
}
    S154 in valid iff {
	// A user only sees ads from followed or suggested users.
	all x, z : User| all p : Photo | x != z and z in posts.p and x in sees.p and (x in follows.z or x in suggested.z) implies p not in Ad
  
}
    S155 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u,u1 : User, a : Ad | u != u1 and u in sees.a iff u in follows.u1 or u1 in suggested.u

}
    S156 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u,u1 : User, a : Ad | (u != u1 and u in sees.a) iff (u in follows.u1 or u1 in suggested.u)

}
    S157 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u,u1 : User, a : Ad | u in sees.a iff u != u1 and u in follows.u1 or u1 in suggested.u

}
    S158 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u,u1 : User, a : Ad | u1 in posts.a and u in sees.a iff u != u1 and u in follows.u1 or u1 in suggested.u

}
    S159 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u : User | Ad & u.sees = u.follows & Ad + u.suggested + Ad

}
    S160 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u : User | Ad & u.follows.posts not in u.sees

}
    S161 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u : User | Ad & u.follows.posts + u.posts not in u.sees

}
    S162 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u, u1: User | Ad in u.sees iff u!=u1 and u->u1 in follows or u->u1 in suggested
}
    S163 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all u : User, p : Photo | u in sees.p and p in Ad implies all z : User | z!=u and z in posts.p implies u in follows.z or z in suggested.u

}
    S164 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u : User | u.sees in (u.follows.posts & Ad)
}
    S165 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u : User | u.sees in  ( u.suggested.posts & Ad)
}
    S166 in valid iff {
	// A user only sees ads from followed or suggested users.
	all u1:User, p:Photo | u1.sees in Ad implies posts.p in u1.follows or posts.p in u1.suggested
}
    S167 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u,v:User | Ad in u.sees iff Ad in u.follows.posts or Ad in u.suggested.posts and u!=v

}
    S168 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u,v:User | Ad in u.sees iff (Ad in u.follows.posts or Ad in u.suggested.posts and u!=v)

}
    S169 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u:User | Ad in u.sees iff (Ad in (u.follows - u).posts or Ad in (u.suggested-u).posts)

}
    S170 in valid iff {
	// A user only sees ads from followed or suggested users.
  all u:User | Ad in u.sees implies Ad in u.follows.posts or Ad in u.suggested.posts

}
    S171 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all ad: Ad | some u: User - Influencer | u in (sees.ad.follows + sees.ad.suggested)

}
    S172 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all ad: Ad | some u: User | u in (sees.ad.follows + sees.ad.suggested)

}
    S173 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all ad: Ad | some u: User | u = (sees.ad.follows + sees.ad.suggested)

}
    S174 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all ad: Ad,  u: User | u in (sees.ad.follows + sees.ad.suggested)

}
    S175 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all disj u1, u2: User | u2 in (u1.follows + u1.suggested) => u2.sees in u1.posts

}
    S176 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all disj u1, u2: User | u2 in (u1.follows + u1.suggested) <=> u2.sees in u1.posts

}
    S177 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all disj u1, u2: User | u2 in (u1.follows + u1.suggested) => u2.sees in u1.posts and u2.sees not in u2.posts

}
    S178 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all disj u1, u2: User | u2 in (u1.follows + u1.suggested) => u2.sees in u1.posts
  	all u: User | u.posts not in u.sees

}
    S179 in valid iff {
	// A user only sees ads from followed or suggested users.
  	all disj u1, u2: User | u2 in (u1.follows + u1.suggested) => u2.sees in u1.posts
  	all u: User | no (u.posts & u.sees)

}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, S74, S75, S76, S77, S78, S79, S80, S81, S82, S83, S84, S85, S86, S87, S88, S89, S90, S91, S92, S93, S94, S95, S96, S97, S98, S99, S100, S101, S102, S103, S104, S105, S106, S107, S108, S109, S110, S111, S112, S113, S114, S115, S116, S117, S118, S119, S120, S121, S122, S123, S124, S125, S126, S127, S128, S129, S130, S131, S132, S133, S134, S135, S136, S137, S138, S139, S140, S141, S142, S143, S144, S145, S146, S147, S148, S149, S150, S151, S152, S153, S154, S155, S156, S157, S158, S159, S160, S161, S162, S163, S164, S165, S166, S167, S168, S169, S170, S171, S172, S173, S174, S175, S176, S177, S178, S179 extends Formula {}

run {
    #valid.Oracle = 1
    #(Instance - valid.Oracle) = 1
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 12 Atom, exactly 4 UserAtom, exactly 4 PhotoAtom, exactly 4 DayAtom,
       exactly 2 Instance, 6 Int
