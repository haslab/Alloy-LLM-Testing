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
    Oracle in valid iff {
	// Influencers post every day.
	all d : Day, i : Influencer | d in i.posts.date
}
    S1 in valid iff {
	// Influencers post every day.
    Influencer.posts.date = Day

}
    S2 in valid iff {
	// Influencers post every day.
  

}
    S3 in valid iff {
	// Influencers post every day.
  all d: Day, i: Influencer | i.posts.date in d

}
    S4 in valid iff {
	// Influencers post every day.
  all d: Day, i: Influencer | (i.posts.date++i.sees.date) in d

}
    S5 in valid iff {
	// Influencers post every day.
  all i: Influencer, d: Day | some i.posts.date
}
    S6 in valid iff {
	// Influencers post every day.
  	all d: Day | d in Influencer.posts

}
    S7 in valid iff {
	// Influencers post every day.
	all d: Day | all i: Influencer | i.posts in d
}
    S8 in valid iff {
	// Influencers post every day.
	all d: Day | all i: Influencer | i.posts.date not in d
}
    S9 in valid iff {
	// Influencers post every day.
	all d: Day | some i: Influencer | i.posts.date in d
}
    S10 in valid iff {
	// Influencers post every day.
	all p: Photo, i: Influencer | p.date in i
}
    S11 in valid iff {
	// Influencers post every day.
	all p: Photo| p.date in Influencer
}
    S12 in valid iff {
	// Influencers post every day.
	all d: Day | some i: Influencer | some i.posts.date
}
    S13 in valid iff {
	// Influencers post every day.
  
// all x:User | x in Influencer implies 
//    (all d:Day | some z:Photo | x->z in posts and z->d in date)
  
// all x:Influencer | 
//      (all d:Day | some z:Photo | x in posts.z and z in date.d)
 
    // all x:Influencer, d:Day | x in posts.date.d
 
     some Influencer.posts & date.Day
}
    S14 in valid iff {
	// Influencers post every day.
  
// all x:User | x in Influencer implies 
//    (all d:Day | some z:Photo | x->z in posts and z->d in date)
  
// all x:Influencer | 
//      (all d:Day | some z:Photo | x in posts.z and z in date.d)
 
    // all x:Influencer, d:Day | x in posts.date.d
 
     Influencer in posts.date.Day
}
    S15 in valid iff {
	// Influencers post every day.
  all x : Influencer | some y: Photo | all z: Day | y in z.date and y in x.posts
}
    S16 in valid iff {
	// Influencers post every day.
    all i: Influencer | all d: Day|  i.posts.date = d

}
    S17 in valid iff {
	// Influencers post every day.
  all d:Day, i:Influencer | d in i.posts

}
    S18 in valid iff {
	// Influencers post every day.
	all i : Influencer | all d : Day | one p : i.posts | p.date = d
}
    S19 in valid iff {
	// Influencers post every day.
  all i : Influencer | i.posts.date = User.posts.date

}
    S20 in valid iff {
    // Influencers post every day.
  	all i: Influencer | all d: Day | some p: Photo | p.date = d

}
    S21 in valid iff {
	// Influencers post every day.
  all d : Day, i : Influencer | i.posts.date = d
  all d : Day, p : Photo | p in d

}
    S22 in valid iff {
	// Influencers post every day.
  all d : Day, i : Influencer | i.posts.date = d
  all d : Day, p : Photo | p.date in d

}
    S23 in valid iff {
	// Influencers post every day.
  all u: Influencer, d: Day, p: Photo | p in u.posts and d in p.date 

}
    S24 in valid iff {
	// Influencers post every day.
	all d:Day | some p: Photo | Influencer.posts in p
}
    S25 in valid iff {
	// Influencers post every day.
  all d : Day | lone posts.date.d & Influencer

}
    S26 in valid iff {
	// Influencers post every day.
  all d : Day | some i : Influencer | some p: Photo | p in posts.i implies p.date in d

}
    S27 in valid iff {
	// Influencers post every day.
  all d : Day | all i : Influencer | some p: Photo | p in posts.i implies p.date in d

}
    S28 in valid iff {
	// Influencers post every day.
	all i : Influencer | all d : Day | some p : Photo | i->p in posts implies p->d in date
}
    S29 in valid iff {
	// Influencers post every day.
	all i: Influencer | all disj p1, p2: Photo | p1 in i.posts and p2 in i.posts implies p1.date = p2.date
}
    S30 in valid iff {
	// Influencers post every day.
  	all d : Day | posts.date.d in Influencer

}
    S31 in valid iff {
	// Influencers post every day.
  	all d : Day, i: Influencer | date.d in i.posts

}
    S32 in valid iff {
	// Influencers post every day.
  	all d : Day | some posts.date.d 

}
    S33 in valid iff {
	// Influencers post every day.
	
  	all d : Day | some Influencer implies some date.d & Influencer.posts
}
    S34 in valid iff {
	
  	// Influencers post every day
  	//all d: Day | Influencer in posts.date.d
	// all i: Influencer | i.posts.date = Day
  
  	// ~date.~post :> Influencer in Day some -> some Influencer
  
  	// Influencer <: posts.date in Influencer some -> some Day
  
  	Influencer -> Influencer = (posts.date).~date.~posts
  
}
    S35 in valid iff {
	
  	// Influencers post every day
  	//all d: Day | Influencer in posts.date.d
	// all i: Influencer | i.posts.date = Day
  
  	// ~date.~post :> Influencer in Day some -> some Influencer
  
  	// Influencer <: posts.date in Influencer some -> some Day
  
  	Influencer -> Influencer & ((this.@User + this.@Photo + this.@Day + Int + String) <: iden) = (posts.date).~date.~posts
  
}
    S36 in valid iff {
	
  	// Influencers post every day
  	//all d: Day | Influencer in posts.date.d
	// all i: Influencer | i.posts.date = Day
  
  	// ~date.~post :> Influencer in Day some -> some Influencer
  
  	// Influencer <: posts.date in Influencer some -> some Day
  
  	Influencer -> Influencer & ((this.@User + this.@Photo + this.@Day + Int + String) <: iden) = posts.date.~date.~posts
  	Day -> Day & ((this.@User + this.@Photo + this.@Day + Int + String) <: iden) = ~date.~posts.posts.date
  
}
    S37 in valid iff {
	
  	// Influencers post every day
  	//all d: Day | Influencer in posts.date.d
	// all i: Influencer | i.posts.date = Day
  
  	// ~date.~post :> Influencer in Day some -> some Influencer
  
  	// Influencer <: posts.date in Influencer some -> some Day
  
  	Influencer -> Influencer & ((this.@User + this.@Photo + this.@Day + Int + String) <: iden) in posts.date.~date.~posts
  	Day -> Day & ((this.@User + this.@Photo + this.@Day + Int + String) <: iden) in ~date.~posts.posts.date
  
}
    S38 in valid iff {
	
  	// Influencers post every day
  	//all d: Day | Influencer in posts.date.d
	// all i: Influencer | i.posts.date = Day
  
  	// ~date.~post :> Influencer in Day some -> some Influencer
  
  	// Influencer <: posts.date in Influencer some -> some Day
  
  	some date + posts => (
      Influencer -> Influencer & ((this.@User + this.@Photo + this.@Day + Int + String) <: iden) in posts.date.~date.~posts and
  	  Day -> Day & ((this.@User + this.@Photo + this.@Day + Int + String) <: iden) in ~date.~posts.posts.date)
  
}
    S39 in valid iff {
	
  	// Influencers post every day
  	//all d: Day | Influencer in posts.date.d
	// all i: Influencer | i.posts.date = Day
  
  	// ~date.~post :> Influencer in Day some -> some Influencer
  
  	// Influencer <: posts.date in Influencer some -> some Day
  
  	some Day => (
      Influencer -> Influencer & ((this.@User + this.@Photo + this.@Day + Int + String) <: iden) in posts.date.~date.~posts and
  	  Day -> Day & ((this.@User + this.@Photo + this.@Day + Int + String) <: iden) in ~date.~posts.posts.date)
  
}
    S40 in valid iff {
	
  	// Influencers post every day
  	//all d: Day | Influencer in posts.date.d
	// all i: Influencer | i.posts.date = Day
  
  	// ~date.~post :> Influencer in Day some -> some Influencer
  
  	// Influencer <: posts.date in Influencer some -> some Day
  
  	some Day => (
      Influencer -> Influencer & ((this.@User + this.@Photo + this.@Day + Int + String) <: iden) in posts.date.~date.~posts and
  	  Day -> Day & ((this.@User + this.@Photo + this.@Day + Int + String) <: iden) in ~date.~(Influencer <: posts).(Influencer <: posts).date )
  
}
    S41 in valid iff {
	
  	// Influencers post every day
  	//all d: Day | Influencer in posts.date.d
	// all i: Influencer | i.posts.date = Day
  
  	// ~date.~post :> Influencer in Day some -> some Influencer
  
  	// Influencer <: posts.date in Influencer some -> some Day
  
  	some Day and some Influencer => (
      Influencer -> Influencer & ((this.@User + this.@Photo + this.@Day + Int + String) <: iden) in posts.date.~date.~posts and
  	  Day -> Day & ((this.@User + this.@Photo + this.@Day + Int + String) <: iden) in ~date.~(Influencer <: posts).(Influencer <: posts).date )
  
}
    S42 in valid iff {
	
  	// Influencers post every day
  	//all d: Day | Influencer in posts.date.d
	// all i: Influencer | i.posts.date = Day
  
  	// ~date.~post :> Influencer in Day some -> some Influencer
  
  	// Influencer <: posts.date in Influencer some -> some Day
  
  	some Day and some Influencer => (
      Influencer -> Influencer & ((this.@User + this.@Photo + this.@Day + Int + String) <: iden) = (Influencer <: posts).date.~date.~(Influencer <: posts) and
  	  Day -> Day & ((this.@User + this.@Photo + this.@Day + Int + String) <: iden) in ~date.~(Influencer <: posts).(Influencer <: posts).date )
  
}
    S43 in valid iff {
	// Influencers post every day.
  all d : Day | some u : Influencer | u.posts.date = d

}
    S44 in valid iff {
	// Influencers post every day.
	posts in Influencer -> some Photo.date
}
    S45 in valid iff {
	// Influencers post every day.
	all d : Day | some i : Influencer | i.posts.date->d in date
}
    S46 in valid iff {
	// Influencers post every day.
  all i:Influencer, d:Day | some z:Photo | z in i.posts implies d in i.date

}
    S47 in valid iff {
	// Influencers post every day.
  all i:Influencer, d:Day, z:Photo | z in i.posts implies d in i.posts.date

}
    S48 in valid iff {
	// Influencers post every day.
  all i:Influencer, d:Day, z:Photo | z in i.posts iff d in i.posts.date

}
    S49 in valid iff {
	// Influencers post every day.
  all i:Influencer, d:Day, z:Photo | z in i.posts and d in i.posts.date

}
    S50 in valid iff {
	// Influencers post every day.
  	all i: Influencer | some p : Photo | all a : Day | p in i.posts and a in p.date

}
    S51 in valid iff {
  // Influencers post every day.
  
  all i : Influencer, p : Photo, d : Day | some p : i.posts | p.date = d
}
    S52 in valid iff {
	// Influencers post every day.
  all d : Day | one date.d

}
    S53 in valid iff {
     // Influencers post every day.
  
     // all x : User | x in Influencer implies 
     //    all d : Day | some z : Photo | x->z in posts and z->d in date
  
     // all x : Influencer, d : Day |
     //    some z : Photo | z in x.posts and z in date.d
 
     // all x : Influencer, d : Day |
     //    some z : Photo | z in x.posts & date.d
 
     all x : Influencer, d : Day | some x.posts & date.d
 
     // all x : Influencer, d : Day | x in posts.date.d
 
     all d : Day | Influencer in posts.date.d

     // WRONG!!
     Influencer in posts.date.Day

     //all x : Influencer, d : Day | d in x.posts.date
 
     all x : Influencer | Day in x.posts.date

     // WRONG!!
     // Day in Influencer.posts.date

}
    S54 in valid iff {
	// Influencers post every day.
  all i : Influencer | all d : Day | lone p : Photo | d in p.date and p in i.posts
}
    S55 in valid iff {
	// Influencers post every day.
	all u : Influencer, d : Day|
  		one p : Photo | 
  			p in u.posts implies p.date = d
}
    S56 in valid iff {
	// Influencers post every day.
  	all i: Influencer | #i.posts = #Day

}
    S57 in valid iff {
	// Influencers post every day.
  
  all i : Influencer , p : Photo, d : Day 	| i.posts in p && i.posts in date.d
  

}
    S58 in valid iff {
	// Influencers post every day.
	all i: Influencer | all disj p1, p2: Photo | p1 in i.posts and p2 in i.posts implies p1.date = p2.date.next
}
    S59 in valid iff {
	// Influencers post every day.
	all i : User-Influencer, d : Day | some z : Photo | i->z in posts and z->d in date
  
}
    S60 in valid iff {
	// Influencers post every day.
	all d : Day | all i : Influencer | some p : Photo |d = p.date implies p in i.posts
}
    S61 in valid iff {
	// Influencers post every day.
  all u:User, d:Day | (some p: Photo | p in u.posts and d in p.date)

}
    S62 in valid iff {
	// Influencers post every day.
	all d : Day | some p : Influencer.posts | p.date = Day
}
    S63 in valid iff {
	// Influencers post every day.
	all i : Influencer, p1, p2 : Photo | p1 != p2 implies p1 in i.posts and p2 in i.posts
}
    S64 in valid iff {
	// Influencers post every day.
	all i:Influencer, d: Day | some p:Photo, a:Ad | (p in i.posts and p.date = d) or 
  													(a in i.posts and a.date = d)
}
    S65 in valid iff {
	// Influencers post every day.
  	all u : User, d :Day | some p : Photo | u in Influencer implies u in posts.p and p in date.d

}
    S66 in valid iff {
	// Influencers post every day.
  all d : Day | lone posts.date.d

}
    S67 in valid iff {
	// Influencers post every day.
  	//one d1: Date, d2: Date| all i: Influencer, p1: date.d1, p2: date.d2|  

  	all i: Influencer, p: Photo| one d1: Day, d2:Day | some posts.i implies posts.d1!=posts.d2
}
    S68 in valid iff {
	// Influencers post every day.
  all i: Influencer, disj d1,d2: Day |  some date.d1 and some date.d2

}
    S69 in valid iff {
	// Influencers post every day.
	all u: Influencer, disj d1,d2:Day|some i:u.posts | i in d1 and i in d2 implies d1!=d2
}
    S70 in valid iff {
	// Influencers post every day.
	date in Influencer.posts some -> Day
}
    S71 in valid iff {
	// Influencers post every day.
	// all i: Influencer, d: Day |
	// 	d in i.posts.date
	// (Influencer <: posts.date & Day)
	all i: Influencer |
		i.posts <: (Photo -> Day) in Photo some -> some Day
}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71 extends Formula {}

run {
    #valid.Oracle = 3
    #(Instance - valid.Oracle) = 3
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 12 Atom, exactly 4 UserAtom, exactly 4 PhotoAtom, exactly 4 DayAtom,
       exactly 6 Instance, 6 Int
