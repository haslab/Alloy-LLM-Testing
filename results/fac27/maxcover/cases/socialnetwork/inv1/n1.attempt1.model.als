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
    Oracle in valid iff {
	// Every image is posted by one user.
  all p: Photo | one (posts.p)
	
}
    S1 in valid iff {
	// Every image is posted by one user.
	
}
    S2 in valid iff {
	// Every image is posted by one user.
  all p : Photo | lone User
	
}
    S3 in valid iff {
	// Every image is posted by one user.
	all x : Photo | lone posts.x
}
    S4 in valid iff {
	// Every image is posted by one user.
  one Photo.posts
  
	
}
    S5 in valid iff {
	// Every image is posted by one user.
  all p : Photo | one User
	
}
    S6 in valid iff {
	// Every image is posted by one user.
  all x: Photo | one x.posts
	
}
    S7 in valid iff {
	// Every image is posted by one user.
  all u : User | lone Photo
	
}
    S8 in valid iff {
	// Every image is posted by one user.
  all u : User | one Photo
	
}
    S9 in valid iff {
	// Every image is posted by one user.
  all u : User | lone u.posts
	
}
    S10 in valid iff {
	// Every image is posted by one user.
  all u : User | one u.posts
	
}
    S11 in valid iff {
	// Every image is posted by one user.
  all p : Photo | some u : User | p in u.posts
	
}
    S12 in valid iff {
	// Every image is posted by one user.
  all p : Photo | some u : User, u2 : User - u | p in u.posts and no u2.posts
	
}
    S13 in valid iff {
	// Every image is posted by one user.
	all u : User | one posts.u
}
    S14 in valid iff {
	// Every image is posted by one user.
	all u1, u2: User | u1 != u2 implies u1.posts != u2.posts
}
    S15 in valid iff {
	// Every image is posted by one user.
  	all disj u, v: User | u.posts not in v.posts
	
}
    S16 in valid iff {
	// Every image is posted by one user.
  all u1 : User | some u2 : User - u1 | u1.posts not in u2.posts
	
}
    S17 in valid iff {
	// Every image is posted by one user.
  some u1 : User | all u2 : User - u1 | u1.posts not in u2.posts
	
}
    S18 in valid iff {
	// Every image is posted by one user.
  some p: Photo | one User.posts
	
}
    S19 in valid iff {
	// Every image is posted by one user.
    some (Photo & User.posts)
}
    S20 in valid iff {
  // Every image is posted by one user.
  all user: User | some photo: Photo | photo in user.posts
}
    S21 in valid iff {
  // Every image is posted by one user.
  all disj u1 : User, u2 : User | no (u1.posts & u2.posts)
}
    S22 in valid iff {
	// Every image is posted by one user.
	all ph: Photo | one u: User | ph in u.sees
}
    S23 in valid iff {
	// Every image is posted by one user.
	all p: Photo | one u: User | u.posts = p
}
    S24 in valid iff {
	// Every image is posted by one user.
	all p: Photo | some u: User | u.posts = p
}
    S25 in valid iff {
	// Every image is posted by one user.
  	all p: Photo, u: User | p in u.posts
	
}
    S26 in valid iff {
	// Every image is posted by one user.
  one (posts.Photo)
	
}
    S27 in valid iff {
	// Every image is posted by one user.
	all u1, u2: User | u1 != u2 implies lone (u1.posts & u2.posts)
}
    S28 in valid iff {
	// Every image is posted by one user.
	all u1, u2: User | u1 != u2 implies one (u1.posts & u2.posts)
}
    S29 in valid iff {
	// Every image is posted by one user.
	all disj u0,u1: User | no (u0.posts &  u1.posts)
  	all p: Photo | one u:User | no posts.p
}
    S30 in valid iff {
	// Every image is posted by one user.
  	all x: Photo, u: User | one posts.x
	
}
    S31 in valid iff {
	// Every image is posted by one user.
  	all p : Photo | some User.posts
	
}
    S32 in valid iff {
	// Every image is posted by one user.
	all p:Photo , u:User| u.posts in p
}
    S33 in valid iff {
	// Every image is posted by one user.
  	all p : Photo | lone User.posts
	
}
    S34 in valid iff {
	// Every image is posted by one user.
  all p:Photo, u:User, i:Influencer | p in u.posts and p in i.posts
	
}
    S35 in valid iff {
	// Every image is posted by one user.
  all p: Photo, disj u: User, i: Influencer |  p in u.posts or p in i.posts
	
}
    S36 in valid iff {
	// Every image is posted by one user.
  all x : Photo | some y : User | all z: User | y->x in posts	and y=z
}
    S37 in valid iff {
	// Every image is posted by one user.
  all p:Photo | one u1:User | one u2:User | (p in u1.posts) implies (p not in u2.posts)
	
}
    S38 in valid iff {
	// Every image is posted by one user.
  all p:Photo | one u1:User | all u2:User | (p in u1.posts) implies (p not in u2.posts)
	
}
    S39 in valid iff {
	// Every image is posted by one user.
	all img : Photo, ad : Ad | img in User.posts and ad in User.posts
}
    S40 in valid iff {
	// Every image is posted by one user.
	all img : Photo, ad : Ad | img in User.posts or ad in User.posts
}
    S41 in valid iff {
	// Every image is posted by one user.
	all p : Photo | one User.posts
}
    S42 in valid iff {
	// Every image is posted by one user.
	all p : Photo | all u : User | p in u
}
    S43 in valid iff {
	// Every image is posted by one user.
	all u1, u2 : User | u1 != u2 implies no (u1.posts.date & u2.posts.date)
	
}
    S44 in valid iff {
	// Every image is posted by one user.
	all p : Photo, u : User, i : Influencer | lone u.posts & i.posts
	
}
    S45 in valid iff {
	// Every image is posted by one user.
	all u : User, i: Influencer | one (u.posts & i.posts)
	
}
    S46 in valid iff {
	// Every image is posted by one user.
	all ph : Photo, u1,u2 : User | u1 = posts.ph implies u2 != posts.ph  	
}
    S47 in valid iff {
	// Every image is posted by one user.
	all ph : Photo, u : User | ph in User.posts
}
    S48 in valid iff {
	// Every image is posted by one user.
	all photo : Photo,user : User | one user.posts
	
}
    S49 in valid iff {
	// Every image is posted by one user.
	all p : Photo | one posts.Photo
}
    S50 in valid iff {
	// Every image is posted by one user.
  all p : Photo | p in User.posts and p in Influencer.posts
	
}
    S51 in valid iff {
	// Every image is posted by one user.
	all u : User, i: Influencer | lone u.posts
	
}
    S52 in valid iff {
	// Every image is posted by one user.
	all u : User, i: Influencer | lone (u.posts + i.posts)
	
}
    S53 in valid iff {
	// Every image is posted by one user.
    lone (Photo & User.posts) or lone (Photo & Influencer.posts) 
}
    S54 in valid iff {
	// Every image is posted by one user.
	all p : Photo | p in User.posts implies one User
}
    S55 in valid iff {
	// Every image is posted by one user.
	all u : User, disj p1,p2 : u.posts | p1.date != p2.date
}
    S56 in valid iff {
	// Every image is posted by one user.
	all u : User, disj p1,p2 : Photo | p1.date != p2.date
}
    S57 in valid iff {
	// Every image is posted by one user.
	all u1, u2: User, p: Photo | (p in u1.posts and p in u2.posts) <=> u1 = u2
}
    S58 in valid iff {
	// Every image is posted by one user.
  all u:User, p:Photo , others:User-u |
 		(p in u.posts && p not in others.posts) or p in others.posts
}
    S59 in valid iff {
	// Every image is posted by one user.
	all p : Photo | some u : User - Influencer | p in u.posts
}
    S60 in valid iff {
	// Every image is posted by one user.
  all i:Photo | some u: User | one i->u
	
}
    S61 in valid iff {
	// Every image is posted by one user.
	all p : Photo | one u : User | p in u.follows.posts
}
    S62 in valid iff {
	// Every image is posted by one user.
  	one u : User | all p : Photo | u.posts in p 
	
}
    S63 in valid iff {
	// Every image is posted by one user.
  	one u : User | all p : Photo | p in u.posts
	
}
    S64 in valid iff {
	// Every image is posted by one user.
  	one u : User | all p : Photo | p in posts.u
	
}
    S65 in valid iff {
	// Every image is posted by one user. 
	one u : User | u.posts - Photo in u.follows.posts
}
    S66 in valid iff {
	// Every image is posted by one user.
    all u:User | one p:Photo | u.posts in p
	
}
    S67 in valid iff {
	// Every image is posted by one user.
  	// pelo menos um 
	Photo in User.posts
  	all u : User | lone u.posts
}
    S68 in valid iff {
  // Every image is posted by one user.
  some u: User | lone u.posts
}
    S69 in valid iff {
	// Every image is posted by one user.
	one u: User | all p: Photo | lone u.posts
}
    S70 in valid iff {
	// Every image is posted by one user.
	posts in User lone -> one Photo	
}
    S71 in valid iff {
	// Every image is posted by one user.
	posts in User lone -> some Photo	
}
    S72 in valid iff {
	// Every image is posted by one user.
	one p: Photo, u: User | p in u.posts
}
    S73 in valid iff {
	// Every image is posted by one user.
  	all p: Photo | lone sees.p
	
}
    S74 in valid iff {
	// Every image is posted by one user.
	posts in User one -> some Photo
}
    S75 in valid iff {
	// Every image is posted by one user.
  all p: Ad, u:User | p in u.posts

	
}
    S76 in valid iff {
	// Every image is posted by one user.
  all p: Photo | (p in User.posts) and (p not in Influencer.posts)

	
}
    S77 in valid iff {
	// Every image is posted by one user.
  Photo - Ad in User.posts


	
}
    S78 in valid iff {
	// Every image is posted by one user.
  Photo - Ad in (User-Influencer).posts


	
}
    S79 in valid iff {
	// Every image is posted by one user.
  Photo - Ad in (User-Influencer).posts
  Ad not in User.posts



	
}
    S80 in valid iff {
	// Every image is posted by one user.
  Photo - Ad in (User-Influencer).posts
  (User-Influencer).posts in Photo -Ad
  




	
}
    S81 in valid iff {
	// Every image is posted by one user.
  all i : Photo - Ad | i in User.posts and i not in Influencer.posts

  




	
}
    S82 in valid iff {
	// Every image is posted by one user.
  all i : User.posts| i not in Influencer.posts

  




	
}
    S83 in valid iff {
	// Every image is posted by one user.
  User.posts = Photo-Ad
  all i : User.posts| i not in Influencer.posts

  




	
}
    S84 in valid iff {
	// Every image is posted by one user.
	lone posts.Photo
}
    S85 in valid iff {
	// Every image is posted by one user.
 	//all x : Photo, y,z : User | y->x in posts and z->x in posts implies y = z
  	//all x : Photo | one y: User | y->x in posts
  	all x : Photo | one posts.x
  	one posts.Photo
}
    S86 in valid iff {
	// Every image is posted by one user. 
	all u : User | u.posts not in u.sees
}
    S87 in valid iff {
	// Every image is posted by one user. 
	all u : User | u.posts not in u.follows.posts
}
    S88 in valid iff {
	// Every image is posted by one user. 
	all u : User | u.posts - Ad in u.follows.posts
}
    S89 in valid iff {
	// Every image is posted by one user. 
	one u : User |  u.posts not in u.sees
}
    S90 in valid iff {
	// Every image is posted by one user. 
	one u : User |  u.sees not in u.posts
}
    S91 in valid iff {
	// Every image is posted by one user.
	all u: User | one posts.Photo
}
    S92 in valid iff {
	// Every image is posted by one user.
	all u: User | some posts.Photo
}
    S93 in valid iff {
	// Every image is posted by one user.
	lone ~posts
}
    S94 in valid iff {
	// Every image is posted by one user.
    some (Photo & User.posts) and (all x: Photo | one posts.x)
}
    S95 in valid iff {
	// Every image is posted by one user.
  lone u: User, p: Photo, a: Ad | p in u.posts or a in u.posts
	
}
    S96 in valid iff {
	// Every image is posted by one user.
  one u: User, p: Photo, a: Ad | p in u.posts or a in u.posts
	
}
    S97 in valid iff {
	// Every image is posted by one user.
  all p: Photo |one disj u: User, i: Influencer |  p in u.posts or p in i.posts 
	
}
    S98 in valid iff {
	// Every image is posted by one user.
  all p: Photo | one posts
	
}
    S99 in valid iff {
	// Every image is posted by one user.
	one posts.Photo || one posts.Ad
}
    S100 in valid iff {
	// Every image is posted by one user.
	all u : User, p : Photo | some u.posts
}
    S101 in valid iff {
	// Every image is posted by one user.
	all i : Influencer, u : User | 
  		i != u implies i in u.follows
}
    S102 in valid iff {
	// Every image is posted by one user.
  	//all p: Photo | one posts.p 
  	posts in Photo one -> one User
}
    S103 in valid iff {
	// Every image is posted by one user.
	all p:Photo , u: User  | u.posts = p
}
    S104 in valid iff {
	// Every image is posted by one user.
  all p: Photo | all ad:Ad |  p in User.posts and ad in User.posts
  no disj u1,u2: User | (u1.posts & u2.posts) != none 
	
}
    S105 in valid iff {
  all x,y : User-Influencer | no (x.posts & y.posts)
	// Every image is posted by one user.
}
    S106 in valid iff {
  all disj x,y : User-Influencer | no (x.posts & y.posts)
	// Every image is posted by one user.
}
    S107 in valid iff {
	// Every image is posted by one user.
  all p: Photo |all u: User | u.posts != none implies p in u.posts
	
}
    S108 in valid iff {
	// Every image is posted by one user.
	some disj a, b: User | no (a.posts & b.posts)
}
    S109 in valid iff {
	// Every image is posted by one user.
  
	all u:User,p:Photo, a:Ad | u -> p in posts && u -> a in posts  
}
    S110 in valid iff {
	// Every image is posted by one user.
  
	some p:Photo| all u:User | p in u.posts  
}
    S111 in valid iff {
	// Every image is posted by one user.
	lone u: User | all i: Photo | i in u.posts
}
    S112 in valid iff {
	// Every image is posted by one user.
	one p: Photo | one posts.p
}
    S113 in valid iff {
	// Every image is posted by one user.
  lone img : Photo | one u : User | img in u.posts
	
}
    S114 in valid iff {
	// Every image is posted by one user.
	some p : Photo | one posts.p
}
    S115 in valid iff {
	// Every image is posted by one user.
	all p : Photo | one u : User | u.posts in p
}
    S116 in valid iff {
	// Every image is posted by one user.
  	all p : Photo | let u = {u : User | p in u.posts } | no u2 : User, inf : 					Influencer | p in u2.posts or p in inf.posts and ( u = u2 or inf = u)
	
}
    S117 in valid iff {
	// Every image is posted by one user.
  one Photo one User
	
}
    S118 in valid iff {
	// Every image is posted by one user.
	posts in User lone -> lone Photo
}
    S119 in valid iff {
	// Every image is posted by one user.
	one u: User | all p: Photo | some u.posts
}
    S120 in valid iff {
	// Every image is posted by one user.
		posts in User one -> one Photo

}
    S121 in valid iff {
  // Every image is posted by one user.
  all p: Photo | no disj u1, u2 : User | u1.posts = p and u2.posts = p
  
	
}
    S122 in valid iff {
  // Every image is posted by one user.
  all p: Photo | no disj u1, u2 : Influencer | u1.posts = p and u2.posts = p
  
	
}
    S123 in valid iff {
  // Every image is posted by one user.
  all p: Photo | no disj u1, u2 : User | u1.posts = p and u2.posts = p
  and 
  all ad: Ad | no disj u1, u2 : User | u1.posts = ad and u2.posts = ad
  
	
}
    S124 in valid iff {
  // Every image is posted by one user.
  all p: Photo | no disj u1, u2 : User | u1.posts = p and u2.posts = p
  and 
  all ad: Ad | no disj u1, u2 : User | u1.posts = ad and u2.posts = ad
  and
  all ad: Ad | no disj i1, i2 : Influencer | i1.posts = ad and i2.posts = ad
  
	
}
    S125 in valid iff {
  // Every image is posted by one user.
  all p: Photo | no disj u1, u2 : User | p in u1.posts and p in u2.posts
  and
  all p: Photo | some u : User | p in u.posts

}
    S126 in valid iff {
  // Every image is posted by one user.
  all p: Photo | no disj u1, u2 : User | p in u1.posts and p in u2.posts
  and
  all p: Photo | all u : User | p in u.posts

}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, S74, S75, S76, S77, S78, S79, S80, S81, S82, S83, S84, S85, S86, S87, S88, S89, S90, S91, S92, S93, S94, S95, S96, S97, S98, S99, S100, S101, S102, S103, S104, S105, S106, S107, S108, S109, S110, S111, S112, S113, S114, S115, S116, S117, S118, S119, S120, S121, S122, S123, S124, S125, S126 extends Formula {}

run {
    #valid.Oracle = 1
    #(Instance - valid.Oracle) = 1
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 12 Atom, exactly 4 UserAtom, exactly 4 PhotoAtom, exactly 4 DayAtom,
       exactly 2 Instance, 6 Int
