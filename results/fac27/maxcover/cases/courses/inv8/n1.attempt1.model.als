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
    Oracle in valid iff {
	// A professor cannot teach herself
	no enrolled&teaches
}
    S1 in valid iff {
	// A professor cannot teach herself
  all p: Professor | p not in p.teaches
}
    S2 in valid iff {
	// A professor cannot teach herself
	all p: Professor | p.enrolled not in p.teaches
}
    S3 in valid iff {
	// A professor cannot teach herself
	all p: Professor | p.enrolled != p.teaches
}
    S4 in valid iff {
	// A professor cannot teach herself
  Professor.enrolled not in Professor.teaches

}
    S5 in valid iff {
	// A professor cannot teach herself  
	all p : Professor | p.teaches not in p.enrolled
}
    S6 in valid iff {
	// A professor cannot teach herself  
	all p : Professor | enrolled.(p.teaches) & teaches.(p.teaches) = none
}
    S7 in valid iff {
	// A professor cannot teach herself
  all p:Professor | not (some g:Grade| (p->g) in p.teaches.(instanceGrades[this]))

}
    S8 in valid iff {
	// A professor cannot teach herself
 	all p: Professor | all c: Course |
  	p->c in enrolled implies p->c in teaches

}
    S9 in valid iff {
	// A professor cannot teach herself
	all p : Person | p.teaches in Person-p
}
    S10 in valid iff {
	// A professor cannot teach herself
	all p:Professor , c:p.teaches| c in p.enrolled
}
    S11 in valid iff {
	// A professor cannot teach herself
	no(Person.teaches & Person.enrolled)
}
    S12 in valid iff {
	// A professor cannot teach herself
	no(Professor.teaches & Professor.enrolled)
}
    S13 in valid iff {
	// A professor cannot teach herself

  all pr :  Professor, p : Person | p.teaches in Person implies p!=pr 
}
    S14 in valid iff {
	// A professor cannot teach herself
	all c : Course | not one teaches.c & enrolled.c
}
    S15 in valid iff {
	// A professor cannot teach herself

  all pr :  Professor, c : pr.enrolled | pr.teaches != c
}
    S16 in valid iff {
	// A professor cannot teach herself
 	all p: Person, c: Course | p not in teaches.c implies p in Professor

}
    S17 in valid iff {
	// A professor cannot teach herself
	all p1 : Professor | one c : Course | c in p1.teaches implies (c not in p1.enrolled)
}
    S18 in valid iff {
	// A professor cannot teach herself
	all p : Professor | all c : p.teaches | p.enrolled not in c
}
    S19 in valid iff {
	// A professor cannot teach herself
	all p : Professor | all c : p.teaches | p.enrolled != c
}
    S20 in valid iff {
	// A professor cannot teach herself
  	all p : Person | p.enrolled not in p.teaches

}
    S21 in valid iff {
	// A professor cannot teach herself
  	all p: Professor | lone (p.teaches & p.enrolled)

}
    S22 in valid iff {
	// A professor cannot teach herself
	all p1:Professor, p2:teaches.(p1.teaches)-p1 | no (p1.teaches & p2.enrolled)
}
    S23 in valid iff {
	// A professor cannot teach herself
	all p : Professor | teaches.p=Person-p
}
    S24 in valid iff {
	// A professor cannot teach herself
	all p : Professor | p.teaches=Person-p
}
    S25 in valid iff {
	// A professor cannot teach herself
  	all c:Course | teaches.c not in enrolled.c

}
    S26 in valid iff {
	// A professor cannot teach herself
	all p:Professor | p in p.teaches
}
    S27 in valid iff {
	// A professor cannot teach herself
	all p:Professor, c:Course | p in teaches.c implies (some g:Grade | p not in c.(instanceGrades[this]).g)
}
    S28 in valid iff {
	// A professor cannot teach herself
	all p:Professor | some c:Course |
  		c in p.teaches implies not(c in p.enrolled)
}
    S29 in valid iff {
	// A professor cannot teach herself
	all t : Professor | not one (t.enrolled & t.teaches)
}
    S30 in valid iff {
	// A professor cannot teach herself
  
  	all x : Person - Student | x->x in teaches

}
    S31 in valid iff {
	// A professor cannot teach herself
  	all pe : Person | pe.teaches != pe.enrolled 
}
    S32 in valid iff {
	// A professor cannot teach herself
  one p : Person | p.teaches != p.enrolled
	
}
    S33 in valid iff {
	// A professor cannot teach herself
 all p: Person | p.^enrolled !=none implies p.^teaches=none
}
    S34 in valid iff {
	// A professor cannot teach herself
	all p : Person | some c : Course | p in Professor and c in p.teaches implies c not in p.enrolled
}
    S35 in valid iff {
	// A professor cannot teach herself
	all p : Person | some c : Course | p in Professor and c in p.teaches and c not in p.enrolled
}
    S36 in valid iff {
	// A professor cannot teach herself
	all p : Person | some p.teaches => p not in Student
}
    S37 in valid iff {
	// A professor cannot teach herself
	all p : Professor | some p.teaches => p.teaches not in p.enrolled
}
    S38 in valid iff {
	// A professor cannot teach herself
	all p : Professor|some c : Course | p.teaches= c implies not p.enrolled in c
}
    S39 in valid iff {
	// A professor cannot teach herself\
  all p:Professor | all c: Course | c in p.teaches => all t:Project | t in c.courseProjects => t not in p.personProjects  

}
    S40 in valid iff {
	// A professor cannot teach herself
	
  	Professor.teaches != Professor.enrolled
}
    S41 in valid iff {
	// A professor cannot teach herself
  all c : Course | one p : Professor |
 not (c in p.teaches and c in p.enrolled)
  

}
    S42 in valid iff {
	// A professor cannot teach herself
  all c : Course | one p : Person |
 not (c in p.teaches and c in p.enrolled)
  

}
    S43 in valid iff {
	// A professor cannot teach herself
	all p1 : Professor | all p2 : Professor - p1 | all c : p1.teaches | p2 not in enrolled.c 
}
    S44 in valid iff {
	// A professor cannot teach herself
	// all p : Professor, c : Course | c in p.teaches implies not c in p.enrolled
 	all p : Professor, c : Course | p.teaches not in p.enrolled 	
}
    S45 in valid iff {
  all p: Professor, c: Course | p -> c in teaches and
  some p2: Professor | p2 -> c in teaches and p != p2
	// A professor cannot teach herself

}
    S46 in valid iff {
  all p: Professor, c: Course | p -> c in teaches implies
  some p2: Professor | p2 -> c in teaches and p != p2
	// A professor cannot teach herself

}
    S47 in valid iff {
  no p: Professor | p in Student
  all p: Professor, c: Course | p -> c in teaches implies
  some p2: Professor | p2 -> c in teaches and p != p2
	// A professor cannot teach herself

}
    S48 in valid iff {
  all p: Professor, c: Course | p -> c in teaches and no (p.enrolled) implies
  some p2: Professor | p2 -> c in teaches and no (p.enrolled) and p != p2 
	// A professor cannot teach herself

}
    S49 in valid iff {
  all p: Professor, c: Course | p -> c in teaches and no(p.enrolled) implies
  some p2: Professor | p2 -> c in teaches and no(p2.enrolled) and p != p2 
	// A professor cannot teach herself

}
    S50 in valid iff {
	// A professor cannot teach herself
	all p : Professor | all c : p.enrolled | p.teaches not in c
}
    S51 in valid iff {
	// A professor cannot teach herself
  
  all p : Person |  (p.teaches & p.enrolled) = 0 

}
    S52 in valid iff {
	// A professor cannot teach herself
	all p : Person | one c : Course |
  		no (p.enrolled & p.teaches)
}
    S53 in valid iff {
	// A professor cannot teach herself
	no p : Professor | all c : Course | p in teaches.c and p in enrolled.c 
  
  	all p : Professor | no (p.teaches & p.enrolled)

	// OR, symmetrically, 

	// all c : Course | no (teaches.c & enrolled.c)
}
    S54 in valid iff {
	// A professor cannot teach herself
	not (all p:Professor, c:Course | c in p.enrolled and c in p.teaches)
}
    S55 in valid iff {
	// A professor cannot teach herself
	no p : Professor | no p.teaches & p.enrolled
}
    S56 in valid iff {
	// A professor cannot teach herself
	all p : Professor| all c : Course |not p in enrolled.c and p in teaches.c
  
}
    S57 in valid iff {
	// A professor cannot teach herself
	all p : Professor| all c : Course | p in enrolled.c and p in teaches.c
  
}
    S58 in valid iff {
	// A professor cannot teach herself
            teaches.(~(enrolled)) not in ((this.@Person + this.@Course + this.@Project + this.@Grade + Int + String + OrderingAtom) <: iden)



}
    S59 in valid iff {
	// A professor cannot teach herself
           no (teaches.(~(enrolled))) or (teaches.(~(enrolled)) not in ((this.@Person + this.@Course + this.@Project + this.@Grade + Int + String + OrderingAtom) <: iden))





}
    S60 in valid iff {
	// A professor cannot teach herself
	teaches.~enrolled in ((this.@Person + this.@Course + this.@Project + this.@Grade + Int + String + OrderingAtom) <: iden)
}
    S61 in valid iff {
	// A professor cannot teach herself
    all c:Course | no Professor & (c.(instanceGrades[this])).Grade

}
    S62 in valid iff {
	// A professor cannot teach herself
    all c:Course | teaches.c not in (c.(instanceGrades[this])).Grade

}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62 extends Formula {}

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
