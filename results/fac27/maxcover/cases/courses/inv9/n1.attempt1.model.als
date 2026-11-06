abstract sig Atom {}
sig PersonAtom, ProjectAtom, GradeAtom extends Atom {}
abstract sig CourseAtom extends Atom {}
one sig CourseSlot1, CourseSlot2, CourseSlot3, CourseSlot4 extends CourseAtom {}
one sig OrderingAtom {}
abstract sig Formula {}
one sig Oracle extends Formula {}
sig detected in Formula {}
sig Instance {
    valid : set Formula,
    Person : set PersonAtom,
    Professor : set PersonAtom,
    Student : set PersonAtom,
    Course : set CourseAtom,
    Project : set ProjectAtom,
    Grade : set GradeAtom,
    teaches : PersonAtom -> CourseAtom,
    enrolled : PersonAtom -> CourseAtom,
    personProjects : PersonAtom -> ProjectAtom,
    courseProjects : CourseAtom -> ProjectAtom,
    gradeNext : GradeAtom -> GradeAtom,
    grades1 : PersonAtom -> GradeAtom,
    grades2 : PersonAtom -> GradeAtom,
    grades3 : PersonAtom -> GradeAtom,
    grades4 : PersonAtom -> GradeAtom
} {
    teaches in Person -> Course
    enrolled in Person -> Course
    personProjects in Person -> Project
    courseProjects in Course -> Project
    gradeNext in Grade -> Grade
    grades1 in Person -> Grade
    CourseSlot1 not in Course implies no grades1
    grades2 in Person -> Grade
    CourseSlot2 not in Course implies no grades2
    grades3 in Person -> Grade
    CourseSlot3 not in Course implies no grades3
    grades4 in Person -> Grade
    CourseSlot4 not in Course implies no grades4
    Professor + Student in Person
    some Grade
    gradeNext in Grade -> lone Grade
    one Grade - Grade.gradeNext
    Grade = (Grade - Grade.gradeNext).*gradeNext
    no iden & ^gradeNext
    // Earlier requirement 0, required in every Instance.
{
	// Only students can be enrolled in courses
	all p : Person | some p.enrolled implies p in Student
}
    // Earlier requirement 1, required in every Instance.
{
	// Only professors can teach courses
    all p : Person | some p.teaches implies p in Professor
}
    // Earlier requirement 2, required in every Instance.
{
	// Courses must have teachers
    all c: Course | some teaches.c
}
    // Earlier requirement 3, required in every Instance.
{
	// Projects are proposed by one course
	all p: Project | one c: Course | p in c.courseProjects
}
    // Earlier requirement 4, required in every Instance.
{
	// Only students work on projects and 
	// projects must have someone working on them

	// all p : Person | (some pr : Project | p->pr in projects) implies p in Student 

	// all p : Person | (some p.projects) implies p in Student 

	// all pr : Project | all p : Person | p->pr in projects implies p in Student 
  
	// all pr : Project | all p : Person | p in projects.pr implies p in Student 

	all pr : Project | (Person <: personProjects).pr in Student


	// all pr : Project | some p : Person | p->pr in projects

	all pr : Project | some (Person <: personProjects).pr
}
    // Earlier requirement 5, required in every Instance.
{
	// Students only work on projects of courses they are enrolled in
    all s: Student | s.personProjects in s.enrolled.courseProjects
    //all p: Student.projects | p in projects.p.enrolled.projects
    //Course.projects in Student.projects
}
    // Earlier requirement 6, required in every Instance.
{
	// Students work on at most one project per course
  all s: Student, c: Course | lone s.personProjects & c.courseProjects
}
    // Earlier requirement 7, required in every Instance.
{
	// A professor cannot teach herself
	no enrolled&teaches
}
    Oracle in valid iff {
	// A professor cannot teach colleagues
	all p : Person | no (p.teaches.~teaches - p) & p.teaches.~enrolled
}
    S1 in valid iff {
	// A professor cannot teach colleagues
    all a : Professor | no a.enrolled
}
    S2 in valid iff {
	// A professor cannot teach colleagues

}
    S3 in valid iff {
	// A professor cannot teach colleagues
	all disj p1: Professor, p2: Professor | all c: p1.teaches | p2 not in teaches.c
}
    S4 in valid iff {
	// A professor cannot teach colleagues
	//all disj p1: Professor, p2: Professor | all c: Course | (p1 in teaches.c) implies (p2 not in enrolled.c)
	all disj p1: Professor, p2: Professor | some (p1.teaches & p2.teaches)
}
    S5 in valid iff { 
	// A professor cannot teach colleagues

	// all p1, p2 : Professor | all c1, c2 : Course |
	//   not (p1->c1 in teaches and p2->c1 in teaches and p1->c2 in teaches and p2->c2 in enrolled)

	// all p1, p2 : Professor | 
	//   (some c1 : Course | p1->c1 in teaches and p2->c1 in teaches)
	//    implies
	//    no c2: Course | p1->c2 in teaches and p2->c2 in enrolled

	// all p1, p2 : Professor | 
	//   (some c1 : Course | c1 in p1.teaches and c1 in p2.teaches)
	//    implies
	//    no c2: Course | c2 in p1.teaches and c2 in p2.enrolled

	all p1 : Professor | no p2 : Professor | 
	  (some p1.teaches & p2.teaches)
	   implies
	  (no p1.teaches & p2.enrolled)

	// TRY WITH A SINGLE VARIABLE BUT SIMPLER THAN THE FOLLOWING:  

	// all p : Person | no (p.teaches.~teaches - p) & p.teaches.~enrolled
}
    S6 in valid iff {
	// A professor cannot teach colleagues
  	//all p:Professor | all c:p.teaches | teaches.c not in enrolled.c   
	all p:Professor | no p1:Professor | some (p.teaches & p1.teaches) implies p1.enrolled in p.teaches
}
    S7 in valid iff {
	// A professor cannot teach colleagues
  	 all p:Professor | all c:p.teaches | all pe:enrolled.c| p in Student 
  	//all p:Professor | all c:p.teaches | teaches.c not in enrolled.c   
	//all p:Professor | no p1:Professor | some (p.teaches & p1.teaches) implies (p1.enrolled in p.teaches)
}
    S8 in valid iff {
	// A professor cannot teach colleagues
	all p1,p2 : Professor, c : Course | c in p1.teaches and c in p2.teaches implies p1.enrolled not in p2.teaches and p2.enrolled not in p1.teaches
}
    S9 in valid iff {
	// A professor cannot teach colleagues
	all disj p1,p2: Professor | some p1.teaches & p2.teaches => p1.enrolled not in p2.teaches and 
  																p2.enrolled not in p1.teaches
}
    S10 in valid iff {
	// A professor cannot teach colleagues 
  	//all p:Professor | all c:p.teaches | teaches.c not in enrolled.c   
	all p:Professor | no p1:Professor |  some (p.teaches & p1.teaches) implies  (p1.enrolled in p.teaches and p1!=p)
}
    S11 in valid iff {
	// A professor cannot teach colleagues 
  	//all p:Professor | all c:p.teaches | teaches.c not in enrolled.c   
	all p:Professor | no p1:Professor | some (p.teaches & p1.teaches) implies  some (p1.enrolled & p.teaches )
}
    S12 in valid iff {
	// A professor cannot teach colleagues
    all a,b : Person , c :Course | c in a.teaches implies c not in b.enrolled 
  	

}
    S13 in valid iff {
	// A professor cannot teach colleagues
    all a,b : Professor, c : Course | c in a.teaches iff c not in b.enrolled 
  	

}
    S14 in valid iff {
	// A professor cannot teach colleagues
    all a: Person | some a.teaches implies no a.enrolled 
  	

}
    S15 in valid iff {
	// A professor cannot teach colleagues
    all a,b : Professor | b.enrolled not in a.teaches
  	

}
    S16 in valid iff {
	// A professor cannot teach colleagues
  all p1:Professor | all p2:Professor -p1 | p2.enrolled not in p1.teaches
}
    S17 in valid iff {
	// A professor cannot teach colleagues
    all disj a,b : Person | b.enrolled not in a.teaches
  	

}
    S18 in valid iff {
	// A professor cannot teach colleagues
    all a,b : Person | a.enrolled in b.teaches implies a in Student
  	

}
    S19 in valid iff {
	// A professor cannot teach colleagues
	all c : Course | teaches.c in Student
}
    S20 in valid iff {
	// A professor cannot teach colleagues
    all a,b : Person | a.enrolled in b.teaches implies b.enrolled not in a.teaches
  	

}
    S21 in valid iff {
	// A professor cannot teach colleagues
    all a,b : Person | some a.teaches and some b.teaches implies a.enrolled not in b.teaches and b.enrolled not in a.teaches
  	

}
    S22 in valid iff {
	// A professor cannot teach colleagues
    all a,b : Person, c : Course | c in a.teaches and c in b.enrolled implies a.enrolled not in b.teaches
}
    S23 in valid iff {
	// A professor cannot teach colleagues
    all a,b : Professor | a.teaches != b.enrolled
}
    S24 in valid iff {
	// A professor cannot teach colleagues
    all a,b : Person | a.teaches != b.enrolled and b.teaches!= a.enrolled
}
    S25 in valid iff {
	// A professor cannot teach colleagues
    all a,b : Person-Student | a.teaches != b.enrolled and b.teaches!= a.enrolled
}
    S26 in valid iff {
	// A professor cannot teach colleagues
    all a,b : Professor | a.teaches not in b.enrolled
}
    S27 in valid iff {
	// A professor cannot teach colleagues
  all p : Professor | p.teaches not in (Professor-p).enrolled 


}
    S28 in valid iff {
	// A professor cannot teach colleagues
  all t : Professor, t1 : Professor - Student | no t.enrolled & t1.teaches and no t.teaches & t1.enrolled

}
    S29 in valid iff {
	// A professor cannot teach colleagues
  	all p1,p2 : Professor | some c : Course | p1.teaches in c and p2.teaches in c implies p1.teaches not in p2.enrolled and p2.teaches not in p1.enrolled

}
    S30 in valid iff {
	// A professor cannot teach colleagues
  	all p1,p2 : Professor | all c : Course | p1.teaches in c and p2.teaches in c implies p1.teaches not in p2.enrolled and p2.teaches not in p1.enrolled

}
    S31 in valid iff {
	// A professor cannot teach colleagues
  	all p1,p2 : Professor | some c : Course | c in p1.teaches and p2.teaches in c implies p1.teaches not in p2.enrolled and p2.teaches not in p1.enrolled

}
    S32 in valid iff {
	// A professor cannot teach colleagues 
  	all a,b : Professor | some c : Course | c in a.teaches and c in b.teaches implies  c not in b.enrolled and  c not in a.enrolled  
}
    S33 in valid iff {
	// A professor cannot teach colleagues
  	all disj p1,p2 : Professor | some c : Course | c in p1.teaches and c in p2.teaches implies p1.teaches not in p2.enrolled and p2.teaches not in p1.enrolled

}
    S34 in valid iff {
	// A professor cannot teach colleagues
	all c:Course | lone teaches.c 
}
    S35 in valid iff {
	// A professor cannot teach colleagues
	all p : Professor | Professor-p in p.teaches  
}
    S36 in valid iff {
	// A professor cannot teach colleagues
	all p : Professor | Professor-p not in p.teaches  
}
    S37 in valid iff {
	// A professor cannot teach colleagues
	all p : Professor | (Professor-p).enrolled not in p.teaches  
}
    S38 in valid iff {
	// A professor cannot teach colleagues
	all p : (Professor-Student) | ((Professor-Student)-p).enrolled not in p.teaches  
}
    S39 in valid iff {
	// A professor cannot teach colleagues
	all p : Professor | all c : p.teaches | enrolled.c in Professor 
}
    S40 in valid iff {
	// A professor cannot teach colleagues
	all p : Professor | all c : p.teaches | enrolled.c not in Professor 
}
    S41 in valid iff {
	// A professor cannot teach colleagues
	all p : Professor | all c : p.teaches | all p : Person | p.enrolled in c => p in Student
}
    S42 in valid iff {
	// A professor cannot teach colleagues
	all p : Person | some c : Course | c in p.teaches implies no p.enrolled
}
    S43 in valid iff {
	// A professor cannot teach colleagues
  	some p1 : Person, p2 : Person | all c : Course | c in (p1.teaches & p2.teaches) implies no (p1.teaches & p2.enrolled)
}
    S44 in valid iff {
	// A professor cannot teach colleagues
  	some disj p1, p2 : Person | some (p1.teaches & p2.teaches) implies no (p1.teaches & p2.enrolled) 
}
    S45 in valid iff {
	// A professor cannot teach colleagues
	all t : Professor | (all te : t.enrolled | (Professor - t).enrolled not in  t.teaches ) 
}
    S46 in valid iff {
	// A professor cannot teach colleagues
  	all p : Professor | no enrolled.(p.teaches) & teaches.(p.enrolled) 

}
    S47 in valid iff {
	// A professor cannot teach colleagues
	all p: Professor, c: Course |
  		c in p.teaches => no (enrolled.c & (Professor->(p.personProjects)).Project)
}
    S48 in valid iff {
	// A professor cannot teach colleagues
	all p: Professor | one c: Course | c not in p.enrolled
}
    S49 in valid iff {
  // Um professor não pode ensinar o mesmo curso para colegas professores
  all p1, p2: Professor, c: Course |
    p1.teaches = c and p2 in Professor - p1 implies c not in p2.enrolled
}
    S50 in valid iff {
	// A professor cannot teach colleagues
  all p : Professor | all c : p.teaches | c.(instanceGrades[this]) not in p.(instanceGrades[this])

}
    S51 in valid iff {
	// A professor cannot teach colleagues
	all p : Professor | no p1 : Professor | no(p.teaches & p1.enrolled) and no(p.teaches & p1.teaches)
}
    S52 in valid iff {
	// A professor cannot teach colleagues
	all p1:Professor| Professor.^enrolled not in p1.^teaches 
}
    S53 in valid iff {
	// A professor cannot teach colleagues
	all p,z : Professor | some p.enrolled & z.enrolled implies no p.teaches & z.enrolled and no z.teaches & p.enrolled
}
    S54 in valid iff {
	// A professor cannot teach colleagues
	all p1 : Professor, p2 : Professor | some (p1.teaches & p2.teaches) implies 
  		no ( p1.teaches & p2.enrolled) or no ( p2.teaches & p1.enrolled)
  
}
    S55 in valid iff {
	// A professor cannot teach colleagues
	all p,p1: Person | all c : p.enrolled | c not in p1.teaches => p1.enrolled not in c
}
    S56 in valid iff {
	// A professor cannot teach colleagues
  	all disj p1, p2 : Professor, disj c1, c2 : Course | (c1 in p1.teaches and c2 in p1.teaches) implies (c2 not in p1.teaches and c2 not in p2.enrolled)
 

}
    S57 in valid iff {
	// A professor cannot teach colleagues
  	all disj p1, p2 : Professor, disj c1, c2 : Course | (c1 in p1.teaches and c1 in p2.teaches) implies (c2 not in p1.teaches and c2 not in p2.enrolled)
 

}
    S58 in valid iff {
	// A professor cannot teach colleagues
	all  disj t,t1 : Person | t in Professor and t1 in Professor and no t.teaches&t1.enrolled 
}
    S59 in valid iff { all p : Professor & Student | no ((Professor & Student - p).enrolled & p.teaches) }
    S60 in valid iff {
	// A professor cannot teach colleagues
	all p : Professor | all c : p.teaches | p.enrolled not in c
}
    S61 in valid iff {
	// A professor cannot teach colleagues
	all disj p1,p2: Professor | some p1.teaches & p2.teaches => no p1.enrolled & p2.enrolled
}
    S62 in valid iff {
	// A professor cannot teach colleagues
  	no Professor & Student
    no Professor -> Professor & teaches.~enrolled
}
    S63 in valid iff {
	// A professor cannot teach colleagues
	
  	all p : Professor, c : p.enrolled, s : enrolled.c | not (some c1 : Course | p->c1 in teaches and s->c1 in enrolled)
}
    S64 in valid iff {
	// A professor cannot teach colleagues
	all p1, p2 : Person | some c : Course | p1 in Professor and p2 in Professor and c in p1.teaches implies c not in p2.enrolled
}
    S65 in valid iff {
	// A professor cannot teach colleagues
	all disj p1, p2 : Person | p1 in Professor and p2 in Professor and p2 not in Person.enrolled
}
    S66 in valid iff {
	// A professor cannot teach colleagues
	 all p1, p2: Professor, c: Course |
        (p1.teaches & c.(instanceGrades[this]).p1 in Professor) => (p2.teaches & c.(instanceGrades[this]).p2 in Professor) => p1 = p2
}
    S67 in valid iff {
	// A professor cannot teach colleagues
	all prof : Professor, col : Professor - prof | prof.teaches not in col.enrolled
}
    S68 in valid iff {
	// A professor cannot teach colleagues
	all disj p1,p2 : Professor | p1 not in Student implies p1.teaches not in p2.enrolled
}
    S69 in valid iff {
	// A professor cannot teach colleagues
	all disj p1,p2 : Professor | p2 not in Student implies p1.teaches not in p2.enrolled
}
    S70 in valid iff {
	// A professor cannot teach colleagues
	all disj p1,p2 : Professor | p1 not in Student implies no (p1.teaches&p2.teaches)
}
    S71 in valid iff {
	// A professor cannot teach colleagues
  all p,p2:  Professor | all c : Course| p.teaches in c

}
    S72 in valid iff {
	// A professor cannot teach colleagues
  all p,p2:  Professor | all c : Course| p.teaches in c implies not (p2.enrolled in c)

}
    S73 in valid iff {
	// A professor cannot teach colleagues
  no disj p1,p2 : Professor | all c:Course | c in p1.teaches and c in p2.enrolled

}
    S74 in valid iff {
	// A professor cannot teach colleagues
  no c:Course | all disj p1,p2:Professor | c in p1.teaches and c in p2.enrolled

}
    S75 in valid iff {
	// A professor cannot teach colleagues
	no p : Professor | all c1 : Course, c2: Course, x : Person | c1 in p.enrolled and c1 in x.enrolled and c2 in p.teaches implies c2 not in x.enrolled
}
    S76 in valid iff {
	// A professor cannot teach colleagues
	all p1 : Professor | all p2 : Professor-p1 | all c : p1.teaches | p2.enrolled not in c
}
    S77 in valid iff {
	// A professor cannot teach colleagues
  one c : Course | all p,ps : Professor |
  (c in p.teaches and c in ps.enrolled and ps != p) implies c not in ps.teaches 
  

}
    S78 in valid iff {
	// A professor cannot teach colleagues
	all p: Professor | no p.teaches.(instanceGrades[this])[Professor]
}
    S79 in valid iff {
	// A professor cannot teach colleagues
	all p : Professor | all c : Course |
		c in p.teaches implies no p2 : Professor | c.(instanceGrades[this])[p2] = none
}
    S80 in valid iff {
	// A professor cannot teach colleagues
	all p1,p2: Person | some c1, c2: Course | c1 in p1.teaches and c1 in p2.enrolled implies c2 not in p1.teaches and c2 not in p2.teaches
}
    S81 in valid iff {
	// A professor cannot teach colleagues
	all p1,p2: Person | one c1,c2: Course | c1 in p1.teaches and c1 in p2.teaches and c2 in p1.teaches implies c2 not in p2.enrolled
}
    S82 in valid iff {
	// A professor cannot teach colleagues
	all pr : Professor, p : Person | p.enrolled in pr.teaches implies p in Student 
}
    S83 in valid iff {
	// A professor cannot teach colleagues
	all c:Course | one teaches.c-Student
}
    S84 in valid iff {
	// A professor cannot teach colleagues
	all c:Course | lone teaches.c-Student
}
    S85 in valid iff {
    // A professor cannot teach colleagues
  	not (Professor in Student)

}
    S86 in valid iff {
	// A professor cannot teach colleagues
	all p1:Professor | all p2:Professor | p1.enrolled not in (p1.teaches & p2.teaches)
}
    S87 in valid iff {
	// A professor cannot teach colleagues
	all p:Professor, c: p.teaches| enrolled.c not in Person-Professor 
}
    S88 in valid iff {
	// A professor cannot teach colleagues
	all p1:Person | all p2:Person | p1.enrolled not in (p1.teaches & p2.teaches)
}
    S89 in valid iff {
    // A professor cannot teach colleagues
 all p: Professor | all p2: Professor | some p2.enrolled implies not(p.teaches in p2.enrolled)

}
    S90 in valid iff {
	// A professor cannot teach colleagues
	all p:Professor, c: p.teaches| enrolled.c not in Professor-Student
}
    S91 in valid iff {
	// A professor cannot teach colleagues
	all p1:Professor | all p2:Professor-p1 | no (p1.enrolled & p2.enrolled)
}
    S92 in valid iff {
	// A professor cannot teach colleagues
	all p1:Professor | all p2:Professor-p1 | no (p1.enrolled & p2.enrolled) and no (p1.teaches & p2.teaches)
}
    S93 in valid iff {
	// A professor cannot teach colleagues
	all p1:Person | all p2:Person-p1 | no (p1.enrolled & p2.enrolled) and no (p1.teaches & p2.teaches)
}
    S94 in valid iff {
	// A professor cannot teach colleagues
	//all p1:Professor | all p2:Professor-p1 | no (p1.enrolled & p2.enrolled)
  	//all p1:Professor | all p2:Professor-p1 | no (p1.teaches & p2.teaches)
  
  all p1:Professor | all p2:Professor-p1 | some p1.enrolled implies no (p1.teaches & p2.teaches)
}
    S95 in valid iff {
	// A professor cannot teach colleagues
	all p1:Professor | all p2:Professor-p1 | (some p1.enrolled and p1.enrolled in p2.teaches) implies no (p1.teaches & p2.teaches) 

}
    S96 in valid iff {
	// A professor cannot teach colleagues
	all p1:Professor | all p2:Professor-p1 | no (p1.teaches & p2.teaches) implies (some p1.enrolled and p1.enrolled in p2.teaches)

}
    S97 in valid iff {
	// A professor cannot teach colleagues
  	// all professors, all courses c in p.teaches implies p2 not in p
  	all p,p2 : Professor | all c : p.teaches |
  		p2.teaches in c implies (
          p2.enrolled not in c)
}
    S98 in valid iff {
	// A professor cannot teach colleagues
  	// all professors, all courses c in p.teaches implies p2 not in p
  	all p,p2 : Professor | all c : p.teaches |
  		p2.teaches in c and p.teaches in c implies (
          p2.enrolled not in c)
}
    S99 in valid iff {
	// A professor cannot teach colleagues
	 all p,p1 : Professor | p!=p1 and (some p.teaches & p1.teaches) implies (some p.enrolled & p1.enrolled)
}
    S100 in valid iff {
	// A professor cannot teach colleagues
  	// all professors, all courses c in p.teaches implies p2 not in p
  	all disj p,p2 : Professor | all c : p.teaches |
  		c in p2.teaches or c in p2.enrolled
}
    S101 in valid iff {
	// A professor cannot teach colleagues
  	// all professors, all courses c in p.teaches implies p2 not in p
  	all p,p2 : Professor | all c : Course |
  		p.teaches != p.enrolled
}
    S102 in valid iff {
	// A professor cannot teach colleagues
  	// all professors, all courses c in p.teaches implies p2 not in p
  	all p,p2 : Professor | all c : Course |
  		p.teaches != p2.enrolled
}
    S103 in valid iff {
	// A professor cannot teach colleagues
	all p1 : Professor | all c:Course | one p2 : Person |
  		(c in p1.teaches and c in p2.enrolled) implies p2 in Student 
}
    S104 in valid iff {
	// A professor cannot teach colleagues
	all disj p1,p2 : Professor |
  		some c:Course | c in p1.teaches implies not (c in p2.teaches)
}
    S105 in valid iff {
	// A professor cannot teach colleagues
 	all disj p1,p2:Professor | all c:Course|
  		c in p1.teaches implies ((not c in p2.teaches) and (not c in p2.enrolled))
}
    S106 in valid iff {
	// A professor cannot teach colleagues
  	all p1, p2: Professor, c1, c2: Course | some s: Student | p1->c1 in teaches and p2->c2 in teaches and s in c1.enrolled and s in c2.enrolled implies p2 not in p1.teaches
}
    S107 in valid iff {
	// A professor cannot teach colleagues
  all p: Person, c: Course, g: Grade | c->p->g in (instanceGrades[this]) implies p in Student
}
    S108 in valid iff {
	// A professor cannot teach colleagues
	all x,y : Professor | some c : Course | c in x.teaches implies not c in y.teaches
}
    S109 in valid iff {
	// A professor cannot teach colleagues
	all p1 : Professor | no p2 : Professor | (p2.enrolled in p1.teaches) and (p2.teaches in p1.teaches)
}
    S110 in valid iff {
	// A professor cannot teach colleagues
	all p1 : Professor | no p2 : Professor | p2 in enrolled.(p1.teaches) and p2.teaches in teaches.(p1.teaches)
}
    S111 in valid iff {
	// A professor cannot teach colleagues
	all disj p1, p2:Professor, c:Course | c in p1.teaches implies c in p2.enrolled 
}
    S112 in valid iff {
	// A professor cannot teach colleagues
  all p1,p2: Person | p1 != p2 and (p1.teaches & p2.enrolled) = none
    

}
    S113 in valid iff {
	// A professor cannot teach colleagues
	all p1, p2: Professor | p1.teaches!=none iff (p1.enrolled & p2.teaches) = none
}
    S114 in valid iff {
	// A professor cannot teach colleagues
	all p,p1: Professor | no (p.teaches & p1.teaches) implies no (p.teaches & p1.enrolled)
}
    S115 in valid iff {
	// A professor cannot teach colleagues
	all p, p1 : Professor | all c : Course | p != p1 implies (p in teaches.c => p1 not in enrolled.c)implies p1 not in enrolled.c
  
}
    S116 in valid iff {
	// A professor cannot teach colleagues
  Professor.enrolled not in Professor.teaches
}
    S117 in valid iff {
 
  // A professor cannot teach colleagues
  some p: Professor | p in Person 
}
    S118 in valid iff {
    // Um professor não pode ensinar colegas
    all p1 : Professor | all p2 : Person - Professor |
  		p2 in teaches.(p1.teaches) and p2 in enrolled.(p1.teaches)

}
    S119 in valid iff {
	// A professor cannot teach colleagues
  	all p: Professor, c: p.teaches | (teaches.c - p) not in enrolled.c
}
    S120 in valid iff {
	// A professor cannot teach colleagues
  	// all p: Professor, c: p.teaches, ac: Course | ac in p.teaches implies ac not in teaches.c.enrolled
  	all disj p1, p2: Professor | #(p1.teaches & p2.enrolled) <= 1
}
    S121 in valid iff {
	// A professor cannot teach colleagues
	all p : Professor | no ( p.teaches.(instanceGrades[this]).Grade & p.enrolled.(instanceGrades[this]).Grade)
}
    S122 in valid iff {
	// A professor cannot teach colleagues
	all p : Professor | (enrolled.(p.teaches) & Professor) not in p.teaches
}
    S123 in valid iff {
	// A professor cannot teach colleagues
  
  all p : Professor | enrolled.(p.teaches) not in Professor 

}
    S124 in valid iff {
	// A professor cannot teach colleagues
  	all p : Professor | some s : Person - Student | no (p.teaches & s.enrolled)

}
    S125 in valid iff {
	// A professor cannot teach colleagues
	some c : Course | no p : c.(~enrolled) | (some c.~teaches & Professor) and (some p & Professor)
}
    S126 in valid iff {
	// A professor cannot teach colleagues
	no p : Professor | p.teaches.~enrolled in (Person - Student)
}
    S127 in valid iff {
	// A professor cannot teach colleagues
	no disj p,p1 : Professor | (some p1.enrolled & p.teaches) or p1 in Student
}
    S128 in valid iff {
	// A professor cannot teach colleagues
	 all p: Professor | {
        // Per ogni corso che insegna
        all c: p.teaches | {
            // Nessun professore può essere iscritto
            no c.~enrolled & Professor
            // Nessun professore può essere valutato
            no c.(instanceGrades[this])[Professor]}}
}
    S129 in valid iff {
	// A professor cannot teach colleagues
	 all disj p,p1 : Professor | some c : p.teaches | p not in Student 
  		implies (c in p1.enrolled implies p1 in Student)
}
    S130 in valid iff {
	// A professor cannot teach colleagues
	 all disj p1,p2 : Professor | p1.teaches & p2.enrolled = none and 
  		p1.teaches & p2.teaches != none
}
    S131 in valid iff {
  // A professor cannot teach colleagues or herself
  all p:Person | p in Professor <=> p not in Student
  all p: Professor | 
    all c: p.teaches | 
      no p2: Professor | c in p2.enrolled
}
    S132 in valid iff {
	// A professor cannot teach colleagues
  	all disj p, p2 : Professor |p not in Student and p2 not in Student iff p.teaches & p2.enrolled = none and p.enrolled & p2.teaches = none
  

}
    S133 in valid iff {
	// A professor cannot teach colleagues
	all p: Professor | p.teaches not in p.teaches.(~teaches).enrolled
}
    S134 in valid iff {
	// A professor cannot teach colleagues
	all disj p1, p2: Professor | p1.teaches in p2.teaches implies p2.teaches not in p1.enrolled
}
    S135 in valid iff {
	// A professor cannot teach colleagues
	all disj p1, p2: Professor |
  		p1.teaches in p2.teaches iff p2.teaches not in p1.enrolled
}
    S136 in valid iff {
	// A professor cannot teach colleagues
	all p1: Person | all p2: Professor |
  		p1.teaches in p2.teaches implies p2.teaches not in p1.enrolled
}
    S137 in valid iff {
	// A professor cannot teach colleagues
	all p: Professor | all coll: Person-p | coll.teaches in p.teaches implies p.teaches & coll.enrolled = none
}
    S138 in valid iff {
	// A professor cannot teach colleagues
	all p: Professor | all coll: Professor-p | coll.teaches in p.teaches implies p.teaches & coll.enrolled = none
}
    S139 in valid iff {
	// A professor cannot teach colleagues
	all p : Professor | (p.teaches.~teaches - p) not in p.teaches.~enrolled
}
    S140 in valid iff {
	// A professor cannot teach colleagues
	teaches.~enrolled.teaches not in ((this.@Person + this.@Course + this.@Project + this.@Grade + Int + String + OrderingAtom) <: iden)
}
    S141 in valid iff {
	// A professor cannot teach colleagues
	all disj p1, p2 : Professor | p2.teaches in p1.teaches => p2.enrolled not in p1.teaches
}
    S142 in valid iff {
	// A professor cannot teach colleagues
	all disj p1, p2 : Professor | p1.teaches in p2.teaches => p2.enrolled not in p1.teaches
}
    S143 in valid iff {
	// A professor cannot teach colleagues
	all disj p1, p2 : Professor | p2.teaches not in none && p2.teaches in p1.teaches => p2.enrolled not in p1.teaches
}
    S144 in valid iff {
	// A professor cannot teach colleagues
  	all p1, p2 : Professor, c : Course | not (p1.enrolled in p2.teaches) and not (p2.teaches in p1.enrolled)

}
    S145 in valid iff {
	// A professor cannot teach colleagues
	teaches.~enrolled not in Professor -> Professor
}
    S146 in valid iff {
	// A professor cannot teach colleagues
	all c: Course, t: Professor | t in teaches.c => no p: Person | p.enrolled in c and t in p.teaches.~enrolled
}
    S147 in valid iff {
	// A professor cannot teach colleagues
	all c: Course, t: Professor | t in teaches.c => no c: Course, p: Student | p in enrolled.c and t in p.teaches.~enrolled
}
    S148 in valid iff {
	// A professor cannot teach colleagues
	all disj p1, p2: Person | no (p1.teaches.~enrolled & p2.teaches.~enrolled)
}
    S149 in valid iff {
	// A professor cannot teach colleagues
	all p: Person | Person - Professor in p.enrolled.~teaches
}
    S150 in valid iff {
	// A professor cannot teach colleagues
	all p: Professor | Person - Professor in p.teaches.~enrolled
}
    S151 in valid iff {
	// A professor cannot teach colleagues
  	all disj p1, p2: Person | some c: Course | c in p1.enrolled and c in p2.enrolled => p2 not in (p1.teaches.~enrolled) 
}
    S152 in valid iff {
	// A professor cannot teach colleagues
  	all c: Course | some disj p1, p2: Person | c in p1.enrolled and c in p2.enrolled => no (teaches.~enrolled & enrolled.~teaches)
}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, S74, S75, S76, S77, S78, S79, S80, S81, S82, S83, S84, S85, S86, S87, S88, S89, S90, S91, S92, S93, S94, S95, S96, S97, S98, S99, S100, S101, S102, S103, S104, S105, S106, S107, S108, S109, S110, S111, S112, S113, S114, S115, S116, S117, S118, S119, S120, S121, S122, S123, S124, S125, S126, S127, S128, S129, S130, S131, S132, S133, S134, S135, S136, S137, S138, S139, S140, S141, S142, S143, S144, S145, S146, S147, S148, S149, S150, S151, S152 extends Formula {}

fun instanceGrades[i : Instance] : CourseAtom -> PersonAtom -> GradeAtom {
    CourseSlot1 -> i.grades1 + CourseSlot2 -> i.grades2 + CourseSlot3 -> i.grades3 + CourseSlot4 -> i.grades4
}
fun order_first[i : Instance] : one GradeAtom { i.Grade - i.Grade.(i.gradeNext) }
fun order_last[i : Instance] : one GradeAtom { i.Grade - (i.gradeNext).(i.Grade) }
fun order_next[i : Instance] : GradeAtom -> GradeAtom { i.gradeNext }
fun order_prev[i : Instance] : GradeAtom -> GradeAtom { ~(i.gradeNext) }
fun order_prevs[i : Instance, e : GradeAtom] : set GradeAtom { e.^(~(i.gradeNext)) }
fun order_nexts[i : Instance, e : GradeAtom] : set GradeAtom { e.^(i.gradeNext) }
pred order_lt[i : Instance, a, b : GradeAtom] { b in a.^(i.gradeNext) }
pred order_gt[i : Instance, a, b : GradeAtom] { a in b.^(i.gradeNext) }
pred order_lte[i : Instance, a, b : GradeAtom] { a = b or order_lt[i, a, b] }
pred order_gte[i : Instance, a, b : GradeAtom] { a = b or order_gt[i, a, b] }
fun order_larger[i : Instance, a, b : GradeAtom] : GradeAtom { order_lt[i, a, b] => b else a }
fun order_smaller[i : Instance, a, b : GradeAtom] : GradeAtom { order_lt[i, a, b] => a else b }
fun order_max[i : Instance, es : set GradeAtom] : lone GradeAtom { es - es.^(~(i.gradeNext)) }
fun order_min[i : Instance, es : set GradeAtom] : lone GradeAtom { es - es.^(i.gradeNext) }

run {
    #valid.Oracle = 1
    #(Instance - valid.Oracle) = 1
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 16 Atom, exactly 4 PersonAtom, exactly 4 CourseAtom, exactly 4 ProjectAtom, exactly 4 GradeAtom,
       exactly 2 Instance, 8 Int
