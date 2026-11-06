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
    Oracle in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User | u.suggested = (u.follows.follows - u.follows - u)
	
}
    S1 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User | u.suggested = u.follows.follows - u.follows
	
}
    S2 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User | u.suggested = User.follows - u.follows
	
}
    S3 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | u.suggested in u.follows.follows - u.follows
}
    S4 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | u.suggested in u.follows.follows - u.follows - u
}
    S5 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u : User | u.suggested not in u.follows
	
}
    S6 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u : User | u.suggested not in u.follows and u.suggested = u.follows.follows
	
}
    S7 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u : User | u.suggested not in u.follows and u.suggested in u.follows.follows
	
}
    S8 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u : User | u.suggested not in (u.follows + u) and u.suggested in u.follows.follows
	
}
    S9 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u : User | u.suggested not in u.follows and u.suggested in (u.follows.follows - u)
	
}
    S10 in valid iff {
  // Suggested are other users followed by followed users, but not yet followed.
  all u: User | u.suggested -u  in u.follows.follows and u.suggested - u not in u.follows
}
    S11 in valid iff {
  // Suggested are other users followed by followed users, but not yet followed.
  // all u: User | u.suggested -u  in u.follows.follows and u.suggested - u not in u.follows
  all u: User | u.suggested = u.follows.follows - u
}
    S12 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u: User | u.suggested in (u.follows.follows - u)
}
    S13 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	
  //all u: User, s: u.suggested | 
}
    S14 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	
  all u: User, s: u.suggested, others: User - u | s in others.follows 
}
    S15 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	
  all u: User, s: u.suggested, others: User - u | s in others.follows and no u
}
    S16 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	
  all u: User, s: u.suggested, f: u.follows | f.follows in s
}
    S17 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	
  all u: User, s: u.suggested, f: u.follows | s in f.follows and u.follows not in f.follows
}
    S18 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	
  all u: User, s: u.suggested, f: u.follows | s in f.follows and u.follows not in f
}
    S19 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.

  all u : User | u.suggested in u.follows.follows 
}
    S20 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	//If i follow Tai, I will get suggestion of other users but I dont follow them as yet
  	all u: User + Influencer | (u in u.follows.suggested 
  	implies u not in u.follows) and ( u !in u.suggested)
	
}
    S21 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	//If i follow Tai, I will get suggestion of other users but I dont follow them as yet
  	//all u: User + Influencer | (u in u.follows.suggested 
  	//implies u not in u.follows) and (u in u.suggested implies u not in u.follows)
	all u: User |
    u.suggested = {v: User |
      some w: u.follows |
        (v not in u.follows) and
        (v != u) and
        (v not in w.follows)
    }
}
    S22 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | no (u.suggested & u.follows)
}
    S23 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u: User | u.suggested = (u.^follows) - u.follows
	
}
    S24 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u: User | u.suggested in ( (u.^follows) - u.follows )
	
}
    S25 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u: User | u.suggested in ( (u.^follows) - u.follows - u)
	
}
    S26 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u1, u2: User | u2 in u1.follows implies u2 in {u1.follows.follows - u1.follows}
	
}
    S27 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u1: User, u2: User, u3:User |u1 in u3.suggested implies u1 in u2.follows and  u2 in u3.follows and u1 not in u3.follows
	
}
    S28 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u: User | u.suggested = u.^follows
	
}
    S29 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u: User | u.suggested = u.^follows - u.follows - u
	
}
    S30 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all disj u, v: User | u in v.follows implies v.follows in u.suggested
	
}
    S31 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all disj u, v: User | u in v.follows implies u.follows in v.suggested
	
}
    S32 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all disj u, v: User | u.suggested = u.^follows - u.follows - u
	
}
    S33 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all disj u, v: User | u in v.follows && v not in u.follows implies u.follows in v.suggested
	
}
    S34 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all disj u, v: User | u in v.follows implies u.follows in v.suggested && v not in v.suggested
	
}
    S35 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all disj u, v: User | u in v.follows implies u.follows - v in v.suggested
	
}
    S36 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u: User | u not in u.suggested
  	all disj u, v: User | u in v.follows implies u.follows in v.suggested
	
}
    S37 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u: User | u not in u.suggested
  	all disj u, v: User | u in v.follows implies u.follows - v in v.suggested
	
}
    S38 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all disj u1: User, u2: User | all u3: u2.follows | ((u2 in u1.follows) and (u3 not in u1.follows)) implies u3 in u1.suggested
  	all u: User | u not in u.suggested
}
    S39 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u: User | u not in u.suggested
  	all disj u, v: User | v in u.follows implies (u.follows - v.follows) in v.suggested
	
}
    S40 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u: User | u not in u.suggested
  	all disj u, v: User | u in v.follows implies (u.follows - v.follows) in v.suggested
  	all disj u, v: User | u not in v.follows implies (u.follows - v.follows) not in v.suggested
	
}
    S41 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u: User | u not in u.suggested
  	all disj u, v: User | u in v.follows implies (u.follows - v.follows) in v.suggested
  	all disj u, v: User | u not in v.follows implies u.follows not in v.suggested
	
}
    S42 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all disj u, v: User | u.follows.follows in v.suggested
	
}
    S43 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
    all u:User |  (u.follows.follows - u.follows) in u.suggested
}
    S44 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	some u1: User, u2: User, u3:User | u1 in u2.suggested implies u2 in u3.follows and no u1.follows
	
}
    S45 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	some u1: User, u2: User, u3:User | u1 in u3.suggested implies u1 in u2.follows and  u2 in u3.follows and u1 not in u3.follows
	
}
    S46 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  --all u: User | u not in u.suggested
  --all disj u1, u2: User | u2 in u1.follows => u2 not in u1.suggested 
  all disj u1, u2, u3: User | u3 in u1.suggested => u2 in u1.follows and u3 in u2.follows and u3 not in u1.follows
  --follows.~follows in suggested 
  --all disj u1, u2: User | u2 in u1.follows =>
  --((u2.follows) - (u1.follows)) in u1.suggested 
	
}
    S47 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u:User | u.suggested = u.follows.follows
	
}
    S48 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u: User | u.suggested = (User - u.follows - u)
}
    S49 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u:User | no(u.suggested & (u.follows+u)) //and (u.suggested in u.follows.follows)
	
}
    S50 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u: User | all u2: (User - u.follows - u)| u2 in u.suggested iff u2 in u.follows.follows and u2 not in u.follows and u2 != u
}
    S51 in valid iff {
// Suggested are other users followed by followed users, but not yet followed.
	
// all x,y : User | x->y in suggested iff x!=y and
//  (some z:User | x->z in follows and z->y in follows and x->y not in follows)

// all x,y : User | y in x.suggested iff x!=y and 
//   (some z:User | z in x.follows and y in z.follows and y not in x.follows)

   // all x,y : User | y in x.suggested iff x!=y and 
   //            y in x.follows.follows and y not in x.follows

   //  all x,y : User | y in x.suggested iff x!=y and 
   //                         y in x.follows.follows - x.follows

   //  all x,y : User | y in x.suggested iff 
   //                       y in x.follows.follows - x.follows - x

   all x, y : User | y in x.suggested iff
   y in User-x-x.follows & x.follows.follows
}
    S52 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | all uf : u.follows | uf.follows = u.suggested
}
    S53 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1,u2 : User | u1 != u2 and (u1 in u2.follows and u2 not in u1.follows => u2 in u1.suggested)
}
    S54 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u,v: User |  (v in u.follows) implies (u not in v.follows) 
	
}
    S55 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u:User | 
  		some u1:u.suggested |
  				some u2:u.follows |
					u1 in u2.follows and u1 not in u.follows	
}
    S56 in valid iff {
    // Suggested are other users followed by followed users, but not yet followed.
	all u: User | (u.follows.follows in u.suggested) and (u.suggested not in u.follows)
}
    S57 in valid iff {
    // Suggested are other users followed by followed users, but not yet followed.
	all u: User | (u.follows.follows in u.suggested) and (u.suggested != u.follows)
}
    S58 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User, f:u.follows, f2:f.follows-u-f | f2 in u.follows
}
    S59 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all i:Influencer, u:User+i, f:u.follows, f2:f.follows-u-f | f2 in u.follows
}
    S60 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u,v: User |  (v in u.suggested) implies (u in v.follows) 
	
}
    S61 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User | u.follows.follows in u.suggested and not (u.follows in u.suggested)
}
    S62 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User | u.suggested in u.follows.follows and no u.suggested - u.follows  
}
    S63 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all i:Influencer, u:User, f:u+i.follows, f2:f.follows-u-f | f2 in u.follows
}
    S64 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all i:Influencer, u:User-i, f:u.follows, f2:f.follows-u-f | f2 in u.follows
}
    S65 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
    all u:User | (u.follows.follows - u.follows - u) in u.suggested
}
    S66 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User, f:u.follows, f2:f.follows-u | f2 in u.suggested and f2 not in u.follows
}
    S67 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User.suggested | some u2 : User | (u not in u2.follows) and u in u2.follows.follows
}
    S68 in valid iff {
    // Suggested are other users followed by followed users, but not yet followed.
	all u: User | (u.follows.follows in u.suggested) and (u.suggested not in u.follows) and (u not in u.suggested)
}
    S69 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | some(u.suggested) implies (no(u.follows&u.suggested) and some(u.follows.follows&u.suggested))
}
    S70 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1,u2,u3 : User | u1 in u2.follows and u3 in u2.follows and u1 not in u3.follows implies u3 in u1.suggested
}
    S71 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User | #(u.suggested & u.follows) = 0 and u.suggested = u.follows.follows 
	
}
    S72 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all x,y,z : User | y in x.suggested iff y in z.follows and z in x.follows
	
}
    S73 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | some(u.suggested) implies (no(u.follows&u.suggested) and some(u.follows.follows-u&u.suggested))
}
    S74 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | some(u.suggested) implies (no(u.follows&u.suggested) and some((u.follows.follows-u)&u.suggested))
}
    S75 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1,u2,u3 : User | u1 in u2.follows and u3 in u2.follows and u1 not in u3.follows and u3 not in u1.follows implies u3 in u1.suggested
}
    S76 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1,u2,u3 : User | u1 in u2.follows and u3 in u2.follows and u1 not in u3.follows and u1 != u3 implies u3 in u1.suggested
}
    S77 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all x,y,z : User | y in x.suggested iff y in z.follows and z in x.follows and y not in x.follows
	
}
    S78 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1,u2,u3 : User-Influencer | u1 in u2.follows and u3 in u2.follows and u1 not in u3.follows implies u3 in u1.suggested
}
    S79 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all x,y,z : User | y in x.suggested iff y not in x.follows
}
    S80 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1,u2,u3 : User-Influencer | u1 in u2.follows and u3 in u2.follows and u1 not in u3.follows implies u1 in u3.suggested
}
    S81 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all x,y,z : User | y in x.suggested iff y not in x.follows and y in z.follows
}
    S82 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1,u2,u3 : User | u1 in u2.follows and u3 in u2.follows and u1 not in u3.follows and u1 != u3 implies u1 in u3.suggested
}
    S83 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1,u2,u3 : User | u1 in u2.follows and u3 in u2.follows and u1 not in u3.follows implies u1 in u3.suggested
}
    S84 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all x,y,z : User | y in x.suggested iff y not in x.follows and y in z.follows and z in x.follows and x not in y.follows
}
    S85 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all x,z : User, y: User-x | y in x.suggested iff y not in x.follows and y in z.follows and z in x.follows 
}
    S86 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	// if u follows y and y follows z z in u.suggested implies u not in z.follows 
  // u -> y -> z . z not in z.follows and u != z
  all disj u,y,z : User |
  	z in u.suggested iff y in u.follows and z in y.follows and z not in u.follows and z != u
}
    S87 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all i : Influencer, u1,u2,u3 : User-i | u1 in u2.follows and u3 in u2.follows and u1 not in u3.follows implies u1 in u3.suggested
}
    S88 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1,u2,u3 : User-Influencer | u1 in u2.follows and u3 in u2.follows and u1 not in u3.follows and u1 != u3 implies u1 in u3.suggested
}
    S89 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1,u2,u3 : User-Influencer | u1 in u2.follows and u3 in u2.follows and u1 not in u3.follows and u1 != u3 iff u1 in u3.suggested
}
    S90 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  (all disj u, s: User|
  s in u.suggested iff s not in u.follows and s in (u.follows).follows)
	
}
    S91 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all x,y: User | x in x.follows.follows and x not in y.follows and x!=y iff x in y.suggested
}
    S92 in valid iff {

  	// Suggested are other users followed by followed users, but not yet followed.
 // all  u:User, f:u.follows-u |
  //		all use : f.follows |
  //		use not in u.follows implies use in u.suggested
  
 // all u : User , uf:u.follows-u | u.suggested in uf.follows and  u.suggested not in u.follows
  
  
  all u1:User, u2:User-u1 |
  	u2 in u1.suggested implies ((u2 not in u1.follows) and u2 in (u1.follows.follows))
  
}
    S93 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all disj user, user2: User | user2 not in user.follows and user2 in user.follows.follows => user in user.suggested
}
    S94 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u : User | all s : u.suggested | u.follows.follows - u = s
	
}
    S95 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u : User | all s : u.suggested | u.follows.follows - u in s
	
}
    S96 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u : User | all s : u.suggested | no(s.follows & u) implies  u.follows.follows - u = s
	
}
    S97 in valid iff {
  	all x,y,z: User | x -> y in follows and y -> z in follows implies (x -> z in suggested and not(x -> z in follows))
	// Suggested are other users followed by followed users, but not yet followed.
	
}
    S98 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u : User | all s : u.suggested | no(s.follows & u) and no(u.follows & s) implies  u.follows.follows - u = s
	
}
    S99 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | all us : u.suggested | us in u.follows and us in follows.u
}
    S100 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | all u1 : u.follows | all u2 : u1.follows | one u2 & u.suggested
	and u2 != u
}
    S101 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u : User | all s : u.suggested | no(u.follows & s) implies  u.follows.follows - u = s
	
}
    S102 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u : User | all s : u.suggested | no(u.follows & s) and u.follows.follows - u = s
	
}
    S103 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u : User | all s : u.suggested | no(u.follows & s) and u.follows.follows - u - u.follows = s
	
}
    S104 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	// 
  	all u1 : User | some u2 : u1.follows | u1.suggested in u2.follows - u1.follows 
}
    S105 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User| u.suggested = (u.follows).follows & u.follows
}
    S106 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User, u1 : u.follows, u2 : u1.follows | (one u2 - u.suggested
	and u2 != u) or u2 = u
}
    S107 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | u.follows not in u.follows.follows
}
    S108 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u : User | u.suggested = follows.u
	
}
    S109 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u:User | User in u.suggested and User in u.follows.follows 
	
}
    S110 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u : User | u.suggested = follows.u.follows
	
}
    S111 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u : User | u.suggested = follows.u.follows - u
	
}
    S112 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	
  	all u:User, s:User | s in u.suggested implies (some u1:User | u1 in u.follows and u1 in s.follows)
  
}
    S113 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1 : User, u2 : follows.u1 | u1.suggested = u2.follows - u1.follows   	
}
    S114 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1 : User, u2 : follows.u1 | u1.suggested = u2.follows - u1.follows - u1  	
}
    S115 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1 : User, u2 : u1.follows | u1.suggested = u2.follows - u1.follows - u1  	
}
    S116 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1 : User | all u2 : follows.u1 | User.suggested = u2.follows - u1 - u1.follows 	
}
    S117 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u : User | u.suggested = follows.u.follows -  u.follows - u 
  
  
	
}
    S118 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1 : User, p : follows.u1 | let u2 = follows.p | u1.suggested = u2 - u1.follows - u1  	
}
    S119 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	
  all u : User | suggested.u = (u.follows.follows - u.follows)
  
  
}
    S120 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	
  all u : User | suggested.u = (u.follows.follows - u.follows - u)
  
  
}
    S121 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	
  all u : User | suggested.u in (u.follows.follows - u.follows - u)
  
  
}
    S122 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | some(u.suggested) implies (no(u.follows&u.suggested) and some((u.follows.follows-u)&u.suggested))
	all u : User | all s : u.suggested | s not in u.follows and s in u.follows.follows
}
    S123 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	//all u : User | some(u.suggested) implies (no(u.follows&u.suggested) and some((u.follows.follows-u)&u.suggested))
	all u : User | no(u.follows&u.suggested) and some(u.follows.follows&u.suggested)
}
    S124 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	//all u : User | some(u.suggested) implies (no(u.follows&u.suggested) and some((u.follows.follows-u)&u.suggested))
	all u : User | all u2 : User | u2 in u.suggested implies u2 not in u.follows and u2 in u.follows.follows and no(u2.follows&u.follows)
}
    S125 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u1: User, u2: User - u1 |
    (u1 in u2.follows) => (u2 in u1.suggested)
}
    S126 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u1: User, u2: User - u1 |
    (u1 in u2.follows) and (u2 not in u1.follows) =>
      u2 in u1.suggested
}
    S127 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
 	all u1:User, u2: User -u1|
  		some u1.suggested 
}
    S128 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
 	all u1:User, u2: User -u1|
  		u2 in u1.follows and 
  		some(u1.suggested) 
}
    S129 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u:User,u2:User -u | 
  		some u1:u.suggested |	
  			(u1 in u2.follows) and (u2 not in u.follows) 
}
    S130 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u1,u2,u3 : User | 
  		u1 != u2 and u1 != u3 and u2 != u3 and
  		u3 in u2.follows and 
  		u2 in u1.follows 
  		implies u3 in suggested.u1
	
}
    S131 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all disj u1, u2, u3 : User | u2 in u1.follows and u3 in u2.follows and u1 not in u3.follows implies u1 in u3.suggested
}
    S132 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User |
  	all recommended: u.follows.follows | recommended not in u.follows
	
}
    S133 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u : User | all s : u.suggested | all f:u.follows |
  		(u != s) and (s not in u.follows) and (s in f.follows)
  		
	
}
    S134 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  
  all  x,y: User | y!=x and y in x.suggested implies (y in x.follows.^follows and y not in x.follows)
	
}
    S135 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all f:User.follows, u:User |
  		some use : f |
  		use in u.suggested && u not in use.follows
  		
	//all u ; Users , uf;u,follows | u.sugge
}
    S136 in valid iff {

  	// Suggested are other users followed by followed users, but not yet followed.
  all  u:User, f:u.follows |
  		some use : f.follows |
  		use in u.suggested && use not in u.follows
  
//  all u : Users , uf:u.follows | u.suggested in uf.follows and  u.suggested not in u.followers
}
    S137 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User, u2 : u.follows, u3 : u2.follows | u3 in u.follows implies not (u3 in u.suggested)
}
    S138 in valid iff {

  	// Suggested are other users followed by followed users, but not yet followed.
 // all  u:User, f:u.follows-u |
  //		all use : f.follows |
  //		use not in u.follows implies use in u.suggested
  
  all u : User , uf:u.follows | u.suggested in uf.follows and  u.suggested not in u.follows
}
    S139 in valid iff {
  all u :User, u2:User-u-u.follows | u.suggested in u2
  
	// Suggested are other users followed by followed users, but not yet followed.
	//all u1,u2 : User | u1 in u2.follows.follows and u1 not in u2.follows and u1 != u2 iff u1 in u2.suggested

}
    S140 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1, u2:User | u2.follows.follows -u1 -u1.follows in u1.suggested
}
    S141 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u1,u2 : User | u1.suggested in u2.follows.follows-u1-u1.follows
}
    S142 in valid iff {
	// Suggested are: 
  // other users followed by followed users, but not yet followed.
  all disj me,other : User | (some u : User | me != u and other in u.follows) and not (other in me.follows) implies (other in me.suggested)
}
    S143 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u1: User, u2:User-u1 | all sug : u2.follows-u1.follows | sug in u1.suggested
}
    S144 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  
  all u:User, other_follow:u.follows.follows |
  	other_follow in u.suggested iff other_follow not in u.follows
	
}
    S145 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  
  all u:User, other_follow:User |
  	(other_follow in u.follows.follows) && other_follow in u.suggested iff other_follow not in u.follows
	
}
    S146 in valid iff {
  // Suggested are other users followed by followed users, but not yet followed.
  all u: User |
    all other_follow: User -u | 
      (other_follow in u.suggested) iff 
      (other_follow in User.follows and other_follow not in u.follows)
}
    S147 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User, f:u.follows.follows | f in u.suggested implies not(f = u) and not(f in u.follows)
  
}
    S148 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | some u1,u2: User | u1 in u.suggested implies u1 in u2.follows and u2 in u.follows
}
    S149 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1, u2 : User | some sugg: u2.follows | sugg not in u1.follows and sugg != u1 implies sugg in u1.suggested
}
    S150 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1, u2 : User | u2 in suggested.u1 iff some u3 : User | u2 in follows.u3 
    and u1 in follows.u3 and u2 not in follows.u1
}
    S151 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User | u.suggested = follows.follows.u - u.follows
}
    S152 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u1: User | one u2: u1.follows.follows - u1 | u1 != u2 and u2 not in u1.follows implies u2 in u1.suggested
	
}
    S153 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u1: User | lone u2: u1.follows.follows - u1 | u1 != u2 and u2 not in u1.follows implies u2 in u1.suggested
	
}
    S154 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u1: User-Influencer, u2: u1.follows.follows - u1 | u2 not in u1.follows implies u2 in u1.suggested
	
}
    S155 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u1: User, u2: u1.follows.follows | u2 in u1.suggested iff u1 != u2 and u2 not in u1.follows
	
  
  	//all x : User | x.suggested = x.follows.follows - x.follows - x
}
    S156 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u1: User, u2: u1.follows.follows - u1 | u2 in u1.suggested iff u1 != u2 and u2 not in u1.follows
	
  
  	//all x : User | x.suggested = x.follows.follows - x.follows - x
}
    S157 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1,u2 : User | all foll: u2.follows | foll in u1.suggested iff foll not in u1.follows and u2 != u1 
}
    S158 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all disj u1,u2 : User | u1 not in u2.follows and u1 in u2.suggested implies u1 in u2.follows.follows
}
    S159 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User , uu : u.follows | u!=uu implies uu in u.suggested 
}
    S160 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | u.suggested = (u.follows.follows - u - u.suggested)
}
    S161 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
   all x:User, y:User, z:User | x in y.follows and y in z.follows and x not in z.follows implies x != y and y != z and x != z and x in z.suggested
	
}
    S162 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u : User | all u1 : u.follows | all u2 :u1.follows | 
  		u not in u.suggested and 
  		(u2 not in u.follows) => u2 in u.suggested 
	
}
    S163 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u : User | all u1 : u.follows | all u2 :u1.follows | 
  		(u2 not in u.follows) => u2 in u.suggested and u not in u.suggested
	
}
    S164 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u : User | all u1 : u.follows | all u2 :u1.follows | 
  		u not in u.suggested and 
  		(u2 not in u.follows => u2 in u.suggested and u not in u.suggested)
	
}
    S165 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	 all u: User | 
        u not in u.suggested and
        all s: u.suggested, f: u.follows  | 
            s not in u.follows and s in f.follows
  
  				
}
    S166 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.

    all u : User | all su : u.suggested | all fu : u.follows | su != u


}
    S167 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u: User | all s: u.suggested |
    	(s = u.follows.follows - u.follows) and (s not in u.follows) and u != s
	
}
    S168 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.

    all u : User | all su : u.suggested | some fu : u.follows | u!=su and u!=fu 
}
    S169 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u : User | some su : u.suggested | all fu : u.follows | su != u
        and su != fu and su in fu.follows and su not in u.follows

}
    S170 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | u.suggested in (u.follows.follows-u-u.follows) and u.suggested not in u.follows
}
    S171 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u:User | u.suggested = u.follows.follows - u.follows - u and u.suggested not in u.follows
}
    S172 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User | u.suggested not in u.follows and u.suggested = u.follows.follows-u.follows
}
    S173 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all disj u1,u2 : User | (u1.suggested not in u1.follows) and u1 in follows.u2 implies u1.suggested in u2.follows
}
    S174 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User | u.follows.follows in u.suggested and not (u.follows in u.suggested) and not (u in u.suggested)
}
    S175 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | (u.follows not in u.suggested) or u.follows.follows in u.suggested  and u not in u.suggested
}
    S176 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	//all x: User | x.suggested = (x.follows.follows-x.follows-x)
  	all x, y: User | y in x.suggested iff x!=y and (some z: User | y in z.follows and z in x.follows and z not in x.suggested)
}
    S177 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | all u2 : (User - Influencer - u) | u2 in u.suggested implies u2 in (u.follows.follows - u.follows - Influencer)
}
    S178 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | all s : u.suggested | (s not in u.follows) and (s in u.follows.follows - Influencer)
}
    S179 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User |  u in u.suggested implies u in u.follows.follows 
}
    S180 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u: User |
        u in u.suggested => {
            some f: u.follows |
                some f2: f.follows |
                    u not in f2.follows
        }
}
    S181 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u: User |
        u in u.suggested => {
            some f: u.follows |
                some f2: f.follows |
                    u not in f2.follows and u != f2
        }
}
    S182 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u: User |
        u in u.suggested => {
            some f: u.follows |
                some f2: f.follows |
                    (u not in f2.follows) and (u != f2) and (u not in f2.suggested)
        }
}
    S183 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u: User |
        u in u.suggested => {
            some f: u.follows |
                some f2: f.follows |
                    (u not in f2.follows) and (u != f2) and (u not in f2.suggested) and (u not in f.follows)
        }
}
    S184 in valid iff {
    // Suggested users are followed by followed users, but not yet followed.
    all u: User | 
        all s: u.suggested - u | 
            all f: u.follows | s in f.follows and s not in u.follows
}
    S185 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | all us : u.suggested | us not in (u.follows - Influencer - u)
}
    S186 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | all us : u.suggested | us in (u.follows.follows) and us not in (u.follows - Influencer - u)
}
    S187 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | all su: u.suggested | some fu : u.follows | (su in u.follows and su!=u and fu!=u) implies su in fu.follows 
}
    S188 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
		all u: User| u.follows.follows not in u.follows

}
    S189 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u : User | u.follows.follows in u.suggested-u.follows-u
	
}
    S190 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u : User | u.follows.follows = u.suggested-u.follows-u
	
}
    S191 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all disj u1, u2 : User | u1.suggested = u2.follows - u1.follows
}
    S192 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  //all u : User | u.suggested = u.follows.follows-u.follows-u 
	all u1, u2 : User | u1 in u2.suggested iff u2 in u1.follows.follows and u1 not in u2.follows and u1 != u2
}
    S193 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1, u2 : User | u2 in u1.suggested iff one u : u1.follows | u2 in u.follows and u2 not in u1.suggested
}
    S194 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all disj u1, u2: User | u1 in u2.suggested implies ( 
      u1 != u2 and u1 in (u2 - u1.^follows ))
}
    S195 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all disj u1, u2 : User | u2 in u1.suggested iff some u : u1.follows | u2 in u.follows and u2 not in u1.suggested
}
    S196 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1,u2 :User | all p: u2.follows | p in u1.suggested iff p != u1 and p not in u1.follows
}
    S197 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1,u2 :User | all p: u2.follows | p in u1.suggested implies p != u1 and p not in u1.follows
}
    S198 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u1, u2: User | u2 in u1.suggested implies follows.u2 in u1.follows
	
}
    S199 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all disj u1, u2: User | u2 in u1.suggested implies follows.u2 in u1.follows
	
}
    S200 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all disj u1, u2: User | u2 in u1.suggested implies u2 in u1.follows.follows
	//all u : User | u.suggested = (u.follows.follows - u) - u.follows
}
    S201 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u: User | all uu : u.follows.follows | u not in uu.follows implies u in uu.suggested 
  
}
    S202 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User | u not in u.suggested
  --all disj u1, u2: User | u2 in u1.follows => u2 not in u1.suggested 
  all disj u1, u2, u3: User | u2 in u1.follows and u3 in u2.follows and u3 not in u1.follows => u3 in u1.suggested
  --follows.~follows in suggested 
  --all disj u1, u2: User | u2 in u1.follows =>
  --((u2.follows) - (u1.follows)) in u1.suggested 
	
}
    S203 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u: User, s: u.suggested, f: u.follows |
    no f & s and
    s in User implies (some fu: u.follows | s in fu.follows)
}
    S204 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u: User, s: u.suggested, f: u.follows |
    no f & s and u not in s and
    s in User implies (some fu: u.follows | s in fu.follows)
}
    S205 in valid iff {
	suggested in follows.~follows - follows // Suggested are other users followed by followed users, but not yet followed.
	
}
    S206 in valid iff {
    // Suggested are other users followed by followed users, but not yet followed.
  	all u1, u2: User | some f: u1.follows | u2 in u1.suggested => u2 not in u1.follows and u2 in f.follows
}
    S207 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User, f: u.follows | u.suggested = f.follows - u
  
}
    S208 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User, f: u.follows | u.suggested = f.follows & f
  
}
    S209 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User |
		u.suggested = (u.follows).follows - u.follows and u not in u.suggested
  
}
    S210 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User, f: u.follows | some u.suggested => u.suggested = (f.follows - f) 
  
}
    S211 in valid iff {
    // Suggested are other users followed by followed users, but not yet followed.
  	all u: User, f: u.follows | u.suggested = f.follows - f and u not in u.suggested
}
    S212 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1,u2 : User | (u2 in u1.suggested and u1 != u2) => (u1 in u2.follows and u2 not in u1.follows) 
}
    S213 in valid iff {
  // Suggested are other users followed by followed users, but not yet followed.
  all s: User | s in s.follows.suggested and s not in s.suggested
}
    S214 in valid iff {
  // Suggested are other users followed by followed users, but not yet followed.
  all s: User | s in s.follows.suggested and s not in s.follows
}
    S215 in valid iff {
  // Suggested are other users followed by followed users, but not yet followed.
  all s: User | s in s.follows.suggested and s not in s.follows and s not in s.follows.follows
}
    S216 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u: User | u.suggested = {s: User | s in u.follows - u}
}
    S217 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	  all u1, u2: User | (u1 in u2.follows) => (u1.suggested & u2.suggested) = none
	
}
    S218 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u, s: User | s in u.suggested implies s in u.^follows
}
    S219 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u, s: User | some u1: User | s in u.suggested implies u1 in u.follows and s not in u.follows
}
    S220 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u, s: User | s not in u.follows and s in u.suggested implies s in u.follows.follows
}
    S221 in valid iff {
	// Suggested are: 
  // other users followed by followed users, but not yet followed.
  all u : User | u.suggested = (u.follows.follows - u.follows) or no u.suggested
}
    S222 in valid iff {
	// Suggested are: 
  // other users followed by followed users, but not yet followed.
  all u : User | not (u in Influencer) implies u.suggested = (u.follows.follows - u.follows) or no u.suggested
}
    S223 in valid iff {
	// Suggested are: 
  // other users followed by followed users, but not yet followed.
  all disj x,y : User | x in Influencer implies x in y.follows
  all i : Influencer | no i.suggested
  all disj me, other : User | not (other in me.follows) and (other in me.follows.follows) implies other in me.suggested
}
    S224 in valid iff {
	// Suggested are: 
  // other users followed by followed users, but not yet followed.
  all i : Influencer | no i.suggested
  all disj me, other : User | not (other in me.follows) implies other in me.suggested
}
    S225 in valid iff {
	// Suggested are: 
  // other users followed by followed users, but not yet followed.
  all i : Influencer | no i.suggested
}
    S226 in valid iff {
	// Suggested are: 
  // other users followed by followed users, but not yet followed.
  all i : Influencer | no i.suggested
  all disj me, other : User | not (other in me.follows)
}
    S227 in valid iff {
	// Suggested are: 
  // other users followed by followed users, but not yet followed.
  all i : Influencer | no i.suggested
  // all me : User, other : usersFollowedByFollowedUsers[me] | other in me.suggested
  all u : User | no u.follows & u.suggested
  all u : User | u.suggested = u.follows.follows
}
    S228 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User | u.suggested = (u.((^(follows)) + ((this.@User + this.@Photo + this.@Day + Int + String) <: iden)) - u.follows )
}
    S229 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User | u not in u.suggested
  all disj u1, u2: User | u2 in u1.follows => u2 not in u1.suggested
  all disj u1, u2: User | u2 in u1.follows =>
  (u2.follows - u1.follows) in u1.suggested
	
}
    S230 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User | u not in u.suggested
  all disj u1, u2: User | u2 in u1.follows => u2 not in u1.suggested and u1 not in u2.suggested
  all disj u1, u2: User | u2 in u1.follows =>
  (u2.follows - u1.follows) in u1.suggested
	
}
    S231 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User | u not in u.suggested
  all disj u1, u2: User | u2 in u1.follows => u2 not in u1.suggested
  all disj u1, u2: User | u2 in u1.follows <=>
  ((u2.follows) - (u1.follows)) in u1.suggested
	
}
    S232 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User | u not in u.suggested
  --all disj u1, u2: User | u2 in u1.follows => u2 not in u1.suggested 
  suggested in follows.~follows
  --all disj u1, u2: User | u2 in u1.follows =>
  --((u2.follows) - (u1.follows)) in u1.suggested 
	
}
    S233 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User | u not in u.suggested
  all disj u1, u2: User | u2 in u1.follows => u2 not in u1.suggested 
  suggested in follows.~follows
  --all disj u1, u2: User | u2 in u1.follows =>
  --((u2.follows) - (u1.follows)) in u1.suggested 
	
}
    S234 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User | u not in u.suggested
  --all disj u1, u2: User | u2 in u1.follows => u2 not in u1.suggested 
  all disj u1, u2, u3: User | u3 in u1.suggested => u2 in u1.follows and u3 in u2.follows and u3 not in u1.follows
  --follows.~follows in suggested 
  --all disj u1, u2: User | u2 in u1.follows =>
  --((u2.follows) - (u1.follows)) in u1.suggested 
	
}
    S235 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User | u not in u.suggested
  all disj u1, u2: User | u2 in u1.follows => u2 not in u1.suggested 
  --all disj u1, u3: User | u3 in u1.suggested => (some disj u2: User | u2 != u1 and u2 != u3 and u2 in u1.follows and u3 in u2.follows and u3 not in u1.follows)
	--all u: User | u.suggested = (u.follows.follows) - u.follows
  all disj u1, u2, u3: User | u1 -> u3 in suggested => u1 -> u2 in follows and u2 -> u3 in follows and u1 -> u3 not in follows
	
}
    S236 in valid iff {
  all u : User | u not in u.suggested
  all u, y, x : User | (u != x and y in u.follows and x in y.follows and x not in u.follows) implies x in u.suggested
  all u, y : User | y in u.follows implies y not in u.suggested
}
    S237 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User | u not in u.suggested
  --all disj u1, u2: User | u2 in u1.follows => u2 not in u1.suggested 
  --all disj u1, u3: User | u3 in u1.suggested => (some disj u2: User | u2 != u1 and u2 != u3 and u2 in u1.follows and u3 in u2.follows and u3 not in u1.follows)
	--all u: User | u.suggested = (u.follows.follows) - u.follows
  all disj u1, u2, u3: User | u1 -> u3 in suggested <=> u1 -> u2 in follows and u2 -> u3 in follows and u1 -> u3 not in follows
	
}
    S238 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1, u2,u3: User | u3->u1 in follows and not(u3->u2 in follows) implies u3 in u2.suggested
}
    S239 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1, u2,u3: User | u3->u1 in follows and not(u3->u2 in follows) and u2!=u3 implies u3 in u2.suggested
}
    S240 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User |
  	all recommended: u.follows.follows | recommended not in u.follows and u != recommended
	
}
    S241 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1, u2,u3: User | u3->u1 in follows and not(u3->u2 in follows) and u1!= u2 and u2!=u3 implies u3 = u2.suggested
}
    S242 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
		all u : User | u .suggested = { v: User | all f: u.follows | v in f.follows and v not in u.follows}
}
    S243 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	
  	all u1 : User, u2 : u1.follows | u1.suggested = u2.follows-u1.follows
}
    S244 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all user1 : User | some user2, user3 : User | not user1 in follows.user2 and user3 in follows.user2
}
    S245 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all user1 : User | some user2, user3 : User | not user1 in follows.user2 and user3 in follows.user2 and user1 != user2 and user1 != user3 and user2 != user3
}
    S246 in valid iff {
    // Suggested users are followed by followed users but not yet followed.
  	all u1,u2 : User | u2 in u1.suggested implies (not u2 in u1.follows and u1 in u2.follows.follows) 
}
    S247 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all x : User, y : User | x in y.suggested implies x != y and x not in y.follows and (some z : User | z != x and z != y and z in x.follows and y in z.follows)
}
    S248 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all us,u : User |
  us in u.suggested implies (us != u and us in u.~follows.~follows)
}
    S249 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User, u2 : u.suggested | some u3 : User | u3 in follows.u2 and u in follows.u3 and u2 not in follows.u and u != u2
}
    S250 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all x : User, y : User | (x != y and some z : User | x in z.follows and z in y.follows and y not in x.follows) implies x in y.suggested
}
    S251 in valid iff {
  	all x,y,z: User | x -> y in follows and y -> z in follows implies z -> x in suggested
	// Suggested are other users followed by followed users, but not yet followed.
	
}
    S252 in valid iff {
  	all x,z: User | some y: User | x -> z in suggested implies 
    (x -> y in follows) and (y -> z in follows) and not(x -> z in follows) and not(z -> x in follows) and x != z
	// Suggested are other users followed by followed users, but not yet followed.
}
    S253 in valid iff {
  	all x,z: User | some y: User | x -> z in suggested implies 
    (x -> y in follows) and (y -> z in follows) and not(x -> z in follows) and not(z -> x in follows)
	// Suggested are other users followed by followed users, but not yet followed.
}
    S254 in valid iff {
  	all x,z: User | some y: User | x -> z in suggested and x!=z implies 
    (x -> y in follows) and (y -> z in follows) and not(x -> z in follows) and not(z -> x in follows)
	// Suggested are other users followed by followed users, but not yet followed.
}
    S255 in valid iff {
  	all x,z: User | some y: User | x -> z in suggested implies 
    (x -> y in follows) and (y -> z in follows) and not(x -> z in follows) and x!=z and x not in Influencer
	// Suggested are other users followed by followed users, but not yet followed.
}
    S256 in valid iff {
  	all x,z: User | some y: User | x -> z in suggested implies 
    (x -> y in follows) and (y -> z in follows) and not(x -> z in follows) and x!=z and x not in Influencer and y not in Influencer and z not in Influencer
	// Suggested are other users followed by followed users, but not yet followed.
}
    S257 in valid iff {
  	all x,z: User | some y: User | x -> z in suggested and x not in Influencer and y not in Influencer and z not in Influencer implies 
    (x -> y in follows) and (y -> z in follows) and not(x -> z in follows) and x!=z 
	// Suggested are other users followed by followed users, but not yet followed.
}
    S258 in valid iff {
   	all x, z: User | some y: User | x -> z in suggested implies (x -> y in follows) and (y -> z in follows) and not (x -> z in follows and z -> x in follows) and x != z 
	// Suggested are other users followed by followed users, but not yet followed.
}
    S259 in valid iff {
   	all x, z: User | some y: User | x -> z in suggested implies (x -> y in follows) and (y -> z in follows) and x -> z not in follows or z -> x not in follows and x != z 
	// Suggested are other users followed by followed users, but not yet followed.
}
    S260 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  
  all u1, u2 : User | some u3 : User | u3 in u1.suggested implies (u3 in u2.follows and u3 not in u1.follows) and u2 in u1. follows and u3 != u1
}
    S261 in valid iff {
   	//all x, y, z: User | (x -> y in follows) and (y -> z in follows) and not(x -> z in follows)  and x != z implies x -> z in suggested  
    all x, y, z: User | (x -> z in suggested) and (x -> y in follows) and (y -> z in follows) implies (x -> z in follows) and z != x

	// Suggested are other users followed by followed users, but not yet followed.
}
    S262 in valid iff {
   	//all x, y, z: User | (x -> y in follows) and (y -> z in follows) and not(x -> z in follows)  and x != z implies x -> z in suggested  
    all x, y, z: User | (x -> z in suggested) and (x -> y in follows) and (y -> z in follows) and x != y and x != z implies (x -> z in follows) 
	// Suggested are other users followed by followed users, but not yet followed.
}
    S263 in valid iff {
   	//all x, y, z: User | (x -> y in follows) and (y -> z in follows) and not(x -> z in follows)  and x != z implies x -> z in suggested  
    all x, y, z: User | (x -> z in suggested) and (x -> y in follows) and (y -> z in follows) implies not (x -> z in follows) or not(z -> x in follows) 
	// Suggested are other users followed by followed users, but not yet followed.
}
    S264 in valid iff {
   	//all x, y, z: User | (x -> y in follows) and (y -> z in follows) and not(x -> z in follows)  and x != z implies x -> z in suggested  
    all x, y, z: User | (x -> z in suggested) implies (x -> y in follows) implies (y -> z in follows) implies not(x -> z in follows) implies x != z
	// Suggested are other users followed by followed users, but not yet followed.
}
    S265 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all x : User, y : User | x in y.suggested iff (x != y and some z : User | x in z.follows and z in y.follows and y not in x.follows)
}
    S266 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	
  	all u1 : User, u2 : u1.follows | u1.suggested = u2.follows-u1.follows
  	no ((this.@User + this.@Photo + this.@Day + Int + String) <: iden) & suggested
}
    S267 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	
  	all u1 : User | u1.suggested = u1.follows.follows
  	no ((this.@User + this.@Photo + this.@Day + Int + String) <: iden) & suggested
}
    S268 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	
  	all u1 : User, u2 : u1.follows, u3 : u2.follows | u1 not in u1.suggested and u1.follows not in u1.suggested and u3 in u1.suggested
}
    S269 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	
  	all u1 : User, u2 : u1.follows, u3 : u2.follows | (u1.follows not in u1.suggested) and (u3 in u1.suggested)
  	no ((this.@User + this.@Photo + this.@Day + Int + String) <: iden) & suggested
}
    S270 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	
  	no follows & suggested
  	no ((this.@User + this.@Photo + this.@Day + Int + String) <: iden) & suggested
  	all u1 : User, u2 : u1.follows.follows | u2 in u1.suggested
}
    S271 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	no suggested & ((this.@User + this.@Photo + this.@Day + Int + String) <: iden)
	and
	all u:User | (u.suggested = u.follows.follows) and (no u.suggested & u.follows)  
}
    S272 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
all u : User | u.suggested in u.follows

}
    S273 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User | u.suggested!=none implies (u.suggested in u.follows.follows) and (u.suggested not in u.follows )
}
    S274 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User | (u.suggested in u.follows.follows 
            and u.suggested not in u.follows
            and u not in u.suggested) or no u.suggested 
  
            
}
    S275 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
   all x:User, z:User, xf:x.follows, zf:z.follows, zs:z.suggested | x in zs implies some y:User, yf:y.follows | x in yf and y in zf and x not in zf 
	
}
    S276 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | all s : User | ( s in u.follows.follows ) and ( not u->s in follows ) and ( u != s ) implies u in s.suggested
  	

}
    S277 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all x : User | all y : User | x.suggested not in x.follows and y.follows in x.suggested   
}
    S278 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all x : User | all y : User-x | x.suggested not in x.follows and y.follows in x.suggested   
}
    S279 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	some s: User, u:User | some u.follows & follows.s 
}
    S280 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all s: User, u:User | lone (u.follows & follows.s )
}
    S281 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	some u:User, s:User | s in u.suggested implies s in u.follows.follows
                     and s not in (u.follows) 
                     and not s=u
}
    S282 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User | (u.suggested = u.follows.follows 
              and u.suggested not in u.follows
              and u not in u.suggested) 
             or no u.suggested 
  
            
}
    S283 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User | (u.suggested = u.follows.follows 
                  and u.suggested not in u.follows+u
                  ) 
               or no u.suggested 
  
            
}
    S284 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
    all u: User | u.follows.follows in u.suggested and u + u.follows not in u.suggested
	
}
    S285 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User | u.suggested in (User - u & User - u.follows & (User - u).follows )
	
}
    S286 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User | u.suggested = User - u & User - u.follows & (User - u).follows 
	
}
    S287 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User | u.suggested = User - u & User - u.follows & User - (User - u).follows
	
}
    S288 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User | u.suggested = User - u & User - u.follows & User - ((User - u).follows).follows
	
}
    S289 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User | u.suggested = User - u & User - u.follows &  ((User - u).follows).follows
	
}
    S290 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User | u.suggested = (User - u) & (User - u.follows) & (follows.(User - u) - u).follows 
	
}
    S291 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User, other: User - u | u.suggested = other & (User - u.follows) & (follows.(User - u) - u).follows 
	
}
    S292 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User, other: User - u | u.suggested = (User - u) & other.follows & other.follows.follows
	
}
    S293 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User, other: (User - u) | u.suggested = (other )
	
}
    S294 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
 // all u: User, other: (User - u) | u.suggested = (other & other.follows & other.follows.follows)
	all u: User | User - u in u.suggested
}
    S295 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User, other: (User - u), random: User | u.suggested = (other & (random.follows.follows))
//	all u: User, other: (User - u) | other = u.suggested 
}
    S296 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User, random: User | random.follows.follows - u in u.suggested
//	all u: User, other: (User - u) | other = u.suggested 
}
    S297 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User | User - u not in u.suggested
//	all u: User, other: (User - u) | other = u.suggested 
}
    S298 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User, o: User | u not in u.suggested and o.follows.follows in u.suggested
//	all u: User, other: (User - u) | other = u.suggested 
}
    S299 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User, o: User | some o.follows.follows implies u not in u.suggested and o.follows.follows in u.suggested and u.follows not in u.suggested 
//	all u: User, other: (User - u) | other = u.suggested 
}
    S300 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User, o: User | some u.suggested implies u not in u.suggested and o.follows.follows in u.suggested and u.follows not in u.suggested 
}
    S301 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User, o: User | one u.suggested implies u not in u.suggested and o.follows.follows in u.suggested and u.follows not in u.suggested 
}
    S302 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User, o: User | some u.suggested implies u not in u.suggested and (User - u).follows.follows in u.suggested and u.follows not in u.suggested 
}
    S303 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User, o: User | some u.suggested implies u not in u.suggested and o.follows.follows in u.suggested and u.suggested not in u.follows
}
    S304 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User, o: User | one u.suggested implies u not in u.suggested and o.follows.follows in u.suggested and u.suggested not in u.follows
}
    S305 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all disj x,y,z : User | 
  		z in x.suggested implies(
          y in x.follows and z in y.follows) 
}
    S306 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all disj x,z : User |
    	(x not in Influencer and z in x.suggested implies z in x.follows.follows)
  
    /* ????
    all u: User |
    u.suggested = ((u.follows.follows) - u.follows) - u
    */
}
    S307 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u1, u2, u3 : User | (u1 != u2 and u2 != u3 and u1 != u3 and u2 in u1.follows and u3 in u2.follows and u3 not in u1.follows) iff u3 in u1.suggested
	
}
    S308 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u : User | all s : u.suggested | (u.follows.follows - u.follows) in s
}
    S309 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User, s:u.suggested, af:User.follows  | s in af and not( s in u.follows)
}
    S310 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User, s:u.suggested, af:User.follows | s in af and not( s in u.follows) and not (s = u)
}
    S311 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User, s:u.suggested, f:u.follows | not (s = u) and not(s in f)
}
    S312 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User | u.suggested in u.follows.follows and not (u.follows in u.suggested)
}
    S313 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all s:User.suggested | not(s in Influencer)
	all u:User, f:u.follows.follows | not(f in Influencer) and not(f = u) and not(f in u.follows) implies f in u.suggested
  
}
    S314 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u:User | not(u in u.suggested)
	all u:User, f:u.follows.follows | f in u.suggested implies not(f in u.follows) 
  
}
    S315 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User, u2 : u.suggested | some u3 : User | u3 in follows.u2 and u in follows.u3 and u2 not in follows.u
}
    S316 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User, u2 : u.suggested - u.follows | u != u2 and some (u.follows & follows.u2)
}
    S317 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u: User | all u2: User - u.follows| u2 in u.suggested iff u2 in (u.follows.follows - u.follows)
}
    S318 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | some u.suggested implies u != u.suggested
}
    S319 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | some u.suggested-u-u.follows implies some (u.follows & follows.(u.suggested-u-u.follows))
}
    S320 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | some u.suggested-u.follows implies u not in u.suggested and some (u.follows & follows.(u.suggested-u-u.follows))
}
    S321 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | some u.suggested implies u not in (u.suggested+u.follows) and some (u.follows & follows.(u.suggested-u.follows))
}
    S322 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | some u.suggested implies u not in (u.suggested+u.follows) and some (u.follows & follows.(u.suggested))
}
    S323 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | some u.suggested implies u not in (u.suggested) and some (u.follows & follows.(u.suggested))
  	all u : User, u2 : u.follows, u3 : u2.follows-u | u3 not in u.follows implies u3 in u.suggested
}
    S324 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User | u.suggested = u.follows.follows-u and (no u.suggested & u.follows)
  
}
    S325 in valid iff {
  	// Suggested are other users followed by followed users, but not yet followed.
  	all u: User |
		all o : User - u |
  			some f : u.follows |
  				(o in f.follows and o not in u.follows) implies o in u.suggested 
}
    S326 in valid iff {
  	// Suggested are other users followed by followed users, but not yet followed.
  	all u: User |
		all o : User |
  			some f : u.follows |
  				(o in f.follows and o not in u.follows) implies o in u.suggested 
}
    S327 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all disj u,z : User |
        z in u.suggested implies
        	(some y : User | z in y.follows and z not in u.follows)
}
    S328 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | some s : User | u -> s in suggested implies not u -> s in follows and u != s
}
    S329 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
      all x: User | (x.suggested in (x.^follows - x.follows - x) and x.suggested != none)

	
}
    S330 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
      all x: User | (x.suggested = (^follows.x - follows.x - x))

	
}
    S331 in valid iff {
    // Os usuários sugeridos são outros usuários seguidos por usuários que o usuário segue, mas não são seguidos por ele.
    all u1, u2 : User | 
        all u3 : User | 
  			(u1 != u2 and u1 != u3 and u2 != u3) implies (
            (u3 in u2.suggested) implies 
            (u2 in u1.follows and u3 in u2.follows and (not u3 in u1.follows)))
}
    S332 in valid iff {
    // Os usuários sugeridos são outros usuários seguidos por usuários que o usuário segue, mas não são seguidos por ele.
    all u1, u2 : User | 
        (u2 in u1.follows) implies 
        (all u3 : User | 
            (u3 in u2.follows and not u3 in u1.follows) implies (u3 in u2.suggested)
        )
}
    S333 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all x, s: User | x in s.suggested implies (some y: User | s not in x.follows and s in y.follows and y in x.follows)
}
    S334 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u,u2 : User | u2 in u.suggested iff u2!=u and (some z : User | z in u2.follows and z not in u.follows)
}
    S335 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u,u2 : User | u2 in u.suggested iff u2!=u and (some z : User | z in u.follows and z not in u2.follows)
}
    S336 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
		
  	all u1, u2: User | some u3 : User | u2 in u1.suggested implies u2 not in u1.follows and u2 in u3.follows 
  
}
    S337 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u :User| no (u.suggested & (u.follows + u)) and no(u.suggested-(User- u.follows.^(follows)))
}
    S338 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u :User| no (u.suggested & (u.follows + u)) and no(u.suggested-(User- u.follows.^(follows))) and u not in u.suggested.follows
}
    S339 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u :User| no (u.suggested & (u.follows + u)) and no(u.suggested-(User- u.follows.follows)) 
}
    S340 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User, followers_following: u.follows.follows | followers_following-u-u.follows = u.suggested 
}
    S341 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User, followers_following: u.follows.follows-u | followers_following-u.follows = u.suggested 
}
    S342 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | some u.suggested & (u.follows).follows
}
    S343 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1,u2 : User | u2 in u1.suggested implies u1.follows.follows in u2.follows 
}
    S344 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all disj u1,u2,u3:User | u2 not in u1.follows and u3 in u1.follows and u2 in u3.follows implies u3 in u1.suggested
}
    S345 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all disj u1,u3:User | some u2:User | (u3 in u1.follows and u2 in u3.follows and u2 not in u1.follows) iff u3 in u1.suggested
}
    S346 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all disj u1,u2,u3:User | (u3 in u1.follows and u2 in u3.follows and u2 not in u1.follows) iff u3 in u1.suggested
}
    S347 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u : User | u.suggested  not in follows.u.follows 
  
  
	
}
    S348 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u : User | u.suggested   in follows.u.follows 
  
  
	
}
    S349 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u : User | u.suggested in follows.u.follows && u.suggested not in u.follows
  
  
	
}
    S350 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u : User | u.suggested in follows.u.follows -  u.follows
  
  
	
}
    S351 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u: User | all s: u.suggested | u.suggested = u.follows.follows and u.suggested not in u.follows
}
    S352 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u: User | u.suggested not in (u.follows.follows - u.follows - u)
}
    S353 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u1,u2,u3 : User | 
  		u1 != u2 and u1 != u3 and u2 != u3 and
  		u1 not in Influencer and
  		u2 not in Influencer and
  		u3 not in Influencer and
  		u3 in u2.follows and 
  		u2 in u1.follows 
  		implies u3 in suggested.u1
	
}
    S354 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u1,u2,u3 : User | 
  		u1 != u2 and u1 != u3 and u2 != u3 and
  		u3 in u2.follows and 
  		u2 in u1.follows and
  		u3 not in u1.follows
  		implies u3 = u1.suggested
}
    S355 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1: User | all u2 : User| some u3: User |
  		u1 in follows.u2 implies
   			u3 in follows.u2 and not u3 in follows.u1 and u3 in u1.suggested
}
    S356 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1: User | all u2 : User| some u3: User |
  		u1 in follows.u2 implies
   			u3 in follows.u2 and not u3 in follows.u1 and u3 in u1.suggested and u3 != u1 
}
    S357 in valid iff {
    // Suggested users are those followed by users followed by u1, but not yet followed by u1, and not u1 themselves.
    all u1: User | 
        all u2: User | 
            (u1 in follows.u2) implies 
                (some u3: User | 
                    (u2 in follows.u3) and 
                    not (u3 in follows.u1) and 
                    u3 != u1 and 
                    u3 in u1.suggested)
}
    S358 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  
  all x,y: (User-Influencer) | y in x.suggested implies y in x.^follows
	
}
    S359 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  
  all disj x,y: (User-Influencer) | y in x.suggested implies y in x.^follows
	
}
    S360 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  
  all disj x,y: User | x!=y and  y in x.suggested implies y in x.^follows
	
}
    S361 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  
  all  x,y: User | y!=x and y in x.suggested implies y in x.follows
	
}
    S362 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  
  all  x,y: User | y!=x and y in x.suggested implies y in x.follows.^follows
	
}
    S363 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  
  all  x,y: (User-Influencer) | y!=x and y in x.suggested implies y in x.follows.^follows
	
}
    S364 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  
  all  x,y: (User-Influencer) | y!=x and y in x.suggested implies (y in x.follows.^follows and y not in x.follows)
	
}
    S365 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  
  all x, y: (User - Influencer) |
  y != x and y in x.suggested implies (y in (x.follows).follows and y not in x.follows)

}
    S366 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User, f: u.follows, s: u.suggested |u not in f.follows and 
  			s in f.follows and s not in u.follows
}
    S367 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User, f: u.follows, s: u.suggested |u not in f.follows and 
  			s in f.follows implies s not in u.follows
}
    S368 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User, f: u.follows, s: u.suggested |
  			s not in u.follows and s!= u implies s in f.follows 
}
    S369 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User, f: u.follows, s: u.suggested | 
  			u not in f.follows and s not in u.follows 
  				implies
  			s in f.follows 
}
    S370 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User, f: u.follows, s:f.follows | 
  			u not in f.follows and s not in u.follows 
  				implies
  			s in u.suggested
}
    S371 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User, f: u.follows, s:f.follows | 
  			u not in f.follows and s not in u.follows 
  				implies
  			s in u.suggested and s not in s.suggested
}
    S372 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User, f: u.follows, s:f.follows | 
  			u not in f.follows and s not in u.follows 
  				implies
  			s in u.suggested and u not in s.suggested
}
    S373 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User | some f: u.follows, s:f.follows | 
  			u not in f.follows and s not in u.follows 
  				implies
  			s in u.suggested and u not in s.suggested
}
    S374 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User | some f: u.follows, s:f.follows | 
  			 s not in u.follows 
  				implies
  			s in u.suggested and u not in s.suggested
}
    S375 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User | some f: u.follows, s:f.follows | 
  			u not in f.follows and s not in u.follows 
  				implies
  			s in u.suggested 
}
    S376 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User, f: u.follows, s: u.suggested| 
  			u not in f.follows and s not in u.follows 
  				
}
    S377 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User, f: u.follows, s: u.suggested| 
  			u not in f.follows and s not in u.follows and u not in u.suggested
  				
}
    S378 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User , s: u.suggested | some f: u.follows |
  			u not in f.follows and s in f.follows and s not in u.follows 
  
  				
}
    S379 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User, s: u.suggested | 
  			u not in (u.follows).follows and s in (u.follows).follows and s not in u.follows 
  
  				
}
    S380 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	 all u: User,s: u.suggested, f: u.follows  | 
             u not in u.suggested implies s not in u.follows and s in f.follows
//???????
  				
}
    S381 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	 all u: User,s: u.suggested, f: u.follows  | 
              s not in u.follows and s in f.follows implies u not in u.suggested 
//???????
  				
}
    S382 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	 all u: User, s: u.suggested - u, f: u.follows  | 
             u not in u.suggested and s not in u.follows and s in f.follows
  		
//???????
  // all u: User | u.suggested = (((u.follows).follows) - (u.follows + u))
  				
}
    S383 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u: User | ((u.follows.follows - u - u.follows) & u.suggested != none)
}
    S384 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u: User | all u2: User-u.follows | u2 in u.^follows
}
    S385 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u: User | all u2: User-u.follows | u2 in u.suggested implies (u2 in (u.^follows-u.follows) and u!=u2)
}
    S386 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u: User | all u2: User - u.follows | u2 in u.suggested iff (u2 in (u.^follows - u.follows) and u!=u2)
}
    S387 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all disj u,u2: User | u2 in u.suggested iff (u2 in u.^follows and u2 not in u.follows and u not in u2.follows)
}
    S388 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u,u2: User | u2 in u.suggested iff (u2 in u.^follows and u2 not in u.follows and u not in u2.follows and u!=u2)
}
    S389 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u,u2: User | u2 in u.suggested iff (u2 in u.follows.follows and u2 not in u.follows and u not in u2.follows and u!=u2)
}
    S390 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u: User | all u2: (User - u.follows)| u2 in u.suggested iff u2 in u.follows.follows and u2 not in u.follows and u2 != u
}
    S391 in valid iff {
  all disj u,u1,u2 : User | u1 in u.suggested and u1 not in u.follows 
	// Suggested are other users followed by followed users, but not yet followed.
	
}
    S392 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all disj u1,u2,u3:User | u3 in suggested.u2 and u1 in follows.u3 and u1 in u2.follows and u3 not in u1.follows
	
}
    S393 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u,v:User | v in (u.suggested-u) iff v in (u.follows.follows-u)
	
}
    S394 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all s, u: User | (s in u.suggested implies s not in u.follows.follows)
	
}
    S395 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u : User | follows.u.follows & User - u.follows = u.suggested 
}
    S396 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u : User | follows.u.follows & User - u.follows = u.suggested - u
}
    S397 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u : User | u.suggested not in (u.follows + u)
	
}
    S398 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | u in User.suggested
}
    S399 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u,f,s : User | (f in u.follows and s in f.follows and u not in s.follows) 	  implies s in u.suggested 
}
    S400 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all f,u : User | all s : f.follows - u.follows | u.follows in s
}
    S401 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all f,u : User | all s : f.follows - u.follows | 		u.suggested in s 
}
    S402 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User |all f : u.follows| all s : f.follows - u.follows - u | u.suggested in s 
}
    S403 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User |all f : u.follows| all s : f.follows - f - u | 			u.suggested in s and s in u.suggested
}
    S404 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u: User | {
        u.suggested = { s: u.follows.follows | 
            some u.follows & u.follows.follows and 
            u.follows.follows not in u.follows and 
            u.follows.follows != u
        }
    }
}
    S405 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u1, u2 : User | u1 in u2.suggested implies (u2 in u1.follows and u1 not in u2.follows)
}
    S406 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u1, u2: User | some u3: User | (u3->u1 in suggested) implies (u1 -> u2 in follows and u2 -> u3 in follows and u3 -> u1 not in follows)
}
    S407 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | u.suggested in (User - u).^follows
}
    S408 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | u.suggested = (User - u).^follows
}
    S409 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User | u.follows.follows not in u.follows + u.suggested 
}
    S410 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u : User | u not in u.^(follows.follows)
	
}
    S411 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
all u : User | u not in u.^suggested
}
    S412 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all x,y : User | (x not in y.follows) implies x in y.suggested
	
}
    S413 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u, u2: User | u2 in u.suggested implies u2 not in u.follows and u2 not in u.follows.follows
}
    S414 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all disj u,s,f:User | s in u.suggested and f in u.follows implies 
  		s not in u.follows and s in f.follows
}
    S415 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u:User | all s:User | some f:User | s in u.suggested implies
  		s!=u and s not in u.follows and s in f.follows
}
    S416 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	// all s, x: User | s in x.suggested iff (some y: User | y in x.follows and s in y.follows and s not in x.follows and s not in x)
	all s, u: User | s in u.suggested iff (some y: u.follows + follows.s | s not in (u.follows + u))
}
    S417 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
    some user: User | 
        some suggested: User | 
            suggested in (user.follows.follows) and 
            not (suggested in user.follows)
}
    S418 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u: User | ((u.follows.follows - u) & u.suggested != none)
}
    S419 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all  disj u: User, u1: User |   (u1 in u.follows.follows and u1 != u and #(u.follows & u.suggested)=0) => u1 in u.suggested
	
}
    S420 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u: User |
  		some s: User |
  			s in u.suggested iff 
  				(s not in u.follows and
  				 some u2: User |
                  u2 in u.follows and
                  s in u2.follows)
  		
}
    S421 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u: User |
  		some s: User |
  			(s in u.suggested) iff 
  				(s not in u.follows + u and
  				 some u2: User |
                  u2 in u.follows and
                  s in u2.follows)
  		
}
    S422 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u:User | not no u.suggested implies u.suggested in u.follows.follows and u.suggested not in u.follows
  	all i:Influencer | i.suggested in i.follows.follows and i.suggested not in i.follows
}
    S423 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u:User | not no u.suggested implies u.suggested = u.follows.follows - u and u.suggested not in u.follows
  	all i:Influencer | not no i.suggested implies i.suggested = i.follows.follows - i and i.suggested not in i.follows
}
    S424 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u:User | not no u.suggested implies u.suggested = u.follows.follows - u.follows - u and u.suggested not in u.follows
}
    S425 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u1, u2 : User | ((u1 != u2 and u2 in u1.suggested) iff (u2 not in u1.follows and (some u3 : User | u1 != u3 and u2 != u3 and u3 in u1.follows and u2 in u3.follows)))
	
}
    S426 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
    all u: User |
        u.suggested = { u1: User | u1 in (User - u) - u.follows + (u.follows.follows & (User - u)) }
}
    S427 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all us,u : User |
  us in u.suggested implies (us != u and u in u.~follows.~follows)
}
    S428 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u, u1, u2 : User | (u!=u1 and u1!=u2 and u!=u2) and u in follows.u1 and u not in follows.u2 and u1 in follows.u2 implies u in suggested.u2 and u not in u.suggested
}
    S429 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | some f : u.follows.follows | u -> f in suggested implies f not in (u.follows)
}
    S430 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | all f : u.follows.follows | u.suggested = u - f
}
    S431 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | all f : u.follows.follows | u.suggested = f - u.follows
}
    S432 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | all f : u.follows.follows | u.suggested = f - u.follows + u
}
    S433 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User.suggested | all f : u.follows.follows | u in f and u not in u.follows
}
    S434 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | all s : u.suggested | all f : u.follows.follows | u in f and u not in u.follows
}
    S435 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | all f : u.follows.follows | u.suggested in f - u.follows
}
    S436 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u : User | all f : u.follows.follows | u.suggested in f - u.follows - u 
}
    S437 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u,u1,u2 : User | u!=u1 and u1!=u2 and u in suggested.u2 iff (u in follows.u1 and u not in follows.u2 and u1 in follows.u2)
	
}
    S438 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u,u1,u2 : User | u!=u1 and u1!=u2 and u != u2 and u in suggested.u2 iff (u in follows.u1 and u not in follows.u2 and u1 in follows.u2)
	
}
    S439 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u : User | all s : User | u.suggested = s
}
    S440 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u : User | all s : User - u | u.suggested = (s & u.follows)
}
    S441 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all u : User | all s : User - u | u.suggested = (s & u.follows.follows - u.follows -u)
}
    S442 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u: User | u.suggested in u.follows.follows implies u.follows.follows not in u.follows
	
}
    S443 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  //all u: User | u.suggested in u.follows.follows implies u.follows.follows not in u.follows
  
   all u, u1: User | u->u1 in follows and u.suggested in u1.follows implies u1.follows not in u.follows
	
}
    S444 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  //all u: User | u.suggested in u.follows.follows implies u.follows.follows not in u.follows
  
   all u, u1: User | u->u1 in follows and u.suggested in u1.follows iff u1.follows not in u.follows
	
}
    S445 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
   //all u, u1: User | u->u1 in follows and u.suggested in u1.follows implies u1.follows not in u.follows
  
     all u, u1: User | u.suggested in u1.follows iff u->u1 in follows and u1.follows not in u.follows
	
}
    S446 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
all u :User | all uf:User | all us:User | (u!=uf and uf!=us) => (uf in u.follows and us in uf.follows and us not in u.follows)<=> us in u.suggested
  
  
	
}
    S447 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u : User | u.suggested in (follows.User - u.follows)
	
}
    S448 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u : User | u.suggested in (follows.User - u.follows - u)
	
}
    S449 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  // This allows users to be suggested follows
  //all u : User | u.suggested in (u.follows.follows - u)
  
  // This allows users to be suggested themselves
//  all u : User | u.suggested in (u.follows.follows - u.follows)
  all u : User | not u in u.suggested and u.suggested in u.follows.^follows
	
}
    S450 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  // This allows users to be suggested follows
  //all u : User | u.suggested in (u.follows.follows - u)
  
  // This allows users to be suggested themselves
//  all u : User | u.suggested in (u.follows.follows - u.follows)
  all u : User | not u in u.suggested 
  	and not u.follows in u.suggested 
  	and u.suggested in u.follows.^follows
	
}
    S451 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  // This allows users to be suggested follows
  //all u : User | u.suggested in (u.follows.follows - u)
  
  // This allows users to be suggested themselves
//  all u : User | u.suggested in (u.follows.follows - u.follows)
  all u : User | (not u in u.suggested 
  	and not u.follows in u.suggested 
  	and u.suggested in u.follows.^follows) or no u.suggested
	
}
    S452 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  // This allows users to be suggested follows
  //all u : User | u.suggested in (u.follows.follows - u)
  
  // This allows users to be suggested themselves
//  all u : User | u.suggested in (u.follows.follows - u.follows)
  all u : User | 
  some u.suggested implies (
    not u in u.suggested // A user's suggestions canot contain that user
  	and not u.follows in u.suggested // suggestions cannot contain follows
  	and u.suggested in u.follows.follows
  )
	
}
    S453 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  // This allows users to be suggested follows
  //all u : User | u.suggested in (u.follows.follows - u)
  
  // This allows users to be suggested themselves
//  all u : User | u.suggested in (u.follows.follows - u.follows)
  all u : User | (
    not u in u.suggested // A user's suggestions canot contain that user
  	and not u.follows in u.suggested // suggestions cannot contain follows
  	and u.suggested in u.follows.follows
  ) 
	
}
    S454 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  // This allows users to be suggested follows
  //all u : User | u.suggested in (u.follows.follows - u)
  
  // This allows users to be suggested themselves
//  all u : User | u.suggested in (u.follows.follows - u.follows)
  all u : User | 
  some u.suggested implies (
    not u in u.suggested // A user's suggestions canot contain that user
  	and not u.follows in u.suggested // suggestions cannot contain follows
  	and u.suggested in u.follows.follows
    and u.suggested in User
  ) else no suggested
	
}
    S455 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all x,y : User | y in x.suggested implies x->y not in follows and x not in Influencer
	
}
    S456 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  	all x,y : User | y in suggested.x implies x->y not in follows
	
}
    S457 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u :User | all s: User - u.follows  | s in u.follows.follows
	
}
    S458 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u:User | some s:User | s in u.follows.follows
	
}
    S459 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u:User | some s:User | not s in u.suggested and s in u.follows.follows 
	
}
    S460 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u:User | all s:User | not s in u.suggested and s in u.follows.follows 
	
}
    S461 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u:User | not User in u.suggested and User in u.follows.follows 
	
}
    S462 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u:User | User in u.suggested iff User in u.follows.follows 
	
}
    S463 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
  all u:User | User in u.suggested implies User in u.follows.follows 
	
}
    S464 in valid iff {
	// Suggested are other users followed by followed users, but not yet followed.
	all u: User | u.suggested in ((u.follows) - (u.follows.follows))
}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, S74, S75, S76, S77, S78, S79, S80, S81, S82, S83, S84, S85, S86, S87, S88, S89, S90, S91, S92, S93, S94, S95, S96, S97, S98, S99, S100, S101, S102, S103, S104, S105, S106, S107, S108, S109, S110, S111, S112, S113, S114, S115, S116, S117, S118, S119, S120, S121, S122, S123, S124, S125, S126, S127, S128, S129, S130, S131, S132, S133, S134, S135, S136, S137, S138, S139, S140, S141, S142, S143, S144, S145, S146, S147, S148, S149, S150, S151, S152, S153, S154, S155, S156, S157, S158, S159, S160, S161, S162, S163, S164, S165, S166, S167, S168, S169, S170, S171, S172, S173, S174, S175, S176, S177, S178, S179, S180, S181, S182, S183, S184, S185, S186, S187, S188, S189, S190, S191, S192, S193, S194, S195, S196, S197, S198, S199, S200, S201, S202, S203, S204, S205, S206, S207, S208, S209, S210, S211, S212, S213, S214, S215, S216, S217, S218, S219, S220, S221, S222, S223, S224, S225, S226, S227, S228, S229, S230, S231, S232, S233, S234, S235, S236, S237, S238, S239, S240, S241, S242, S243, S244, S245, S246, S247, S248, S249, S250, S251, S252, S253, S254, S255, S256, S257, S258, S259, S260, S261, S262, S263, S264, S265, S266, S267, S268, S269, S270, S271, S272, S273, S274, S275, S276, S277, S278, S279, S280, S281, S282, S283, S284, S285, S286, S287, S288, S289, S290, S291, S292, S293, S294, S295, S296, S297, S298, S299, S300, S301, S302, S303, S304, S305, S306, S307, S308, S309, S310, S311, S312, S313, S314, S315, S316, S317, S318, S319, S320, S321, S322, S323, S324, S325, S326, S327, S328, S329, S330, S331, S332, S333, S334, S335, S336, S337, S338, S339, S340, S341, S342, S343, S344, S345, S346, S347, S348, S349, S350, S351, S352, S353, S354, S355, S356, S357, S358, S359, S360, S361, S362, S363, S364, S365, S366, S367, S368, S369, S370, S371, S372, S373, S374, S375, S376, S377, S378, S379, S380, S381, S382, S383, S384, S385, S386, S387, S388, S389, S390, S391, S392, S393, S394, S395, S396, S397, S398, S399, S400, S401, S402, S403, S404, S405, S406, S407, S408, S409, S410, S411, S412, S413, S414, S415, S416, S417, S418, S419, S420, S421, S422, S423, S424, S425, S426, S427, S428, S429, S430, S431, S432, S433, S434, S435, S436, S437, S438, S439, S440, S441, S442, S443, S444, S445, S446, S447, S448, S449, S450, S451, S452, S453, S454, S455, S456, S457, S458, S459, S460, S461, S462, S463, S464 extends Formula {}

run {
    #valid.Oracle = 1
    #(Instance - valid.Oracle) = 1
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 12 Atom, exactly 4 UserAtom, exactly 4 PhotoAtom, exactly 4 DayAtom,
       exactly 2 Instance, 6 Int
