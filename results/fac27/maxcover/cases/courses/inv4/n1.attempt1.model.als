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
    Oracle in valid iff {
	// Projects are proposed by one course
	all p: Project | one c: Course | p in c.courseProjects
}
    S1 in valid iff {
	// Projects are proposed by one course

}
    S2 in valid iff {
	// Projects are proposed by one course
  all p: Project | one none
}
    S3 in valid iff {
	// Projects are proposed by one course
  all c:Course | one c.courseProjects

}
    S4 in valid iff {
	// Projects are proposed by one course
	all c: Course | some c.courseProjects
}
    S5 in valid iff {
	// Projects are proposed by one course
	all p: Project | one Course
}
    S6 in valid iff {
	// Projects are proposed by one course
  //all c:Course | one c.projects
  all p: Project | one Course.courseProjects

}
    S7 in valid iff {
	// Projects are proposed by one course
  //all c:Course | one c.projects
  all p: Project | all c: Course | one c.courseProjects

}
    S8 in valid iff {
	// Projects are proposed by one course
	all p: Project | all c: Course | some c.courseProjects
}
    S9 in valid iff {
	// Projects are proposed by one course
	one c: Course | all p: Project | c.courseProjects in Course
}
    S10 in valid iff {
	// Projects are proposed by one course
	one c : Course | all p : Project | p in c.courseProjects
}
    S11 in valid iff {
	// Projects are proposed by one course
  //all c:Course | one c.projects
  //all p: Project | one c: Course | c->p in projects
  all p: Project | one c: Course | c.courseProjects in p

}
    S12 in valid iff {
	// Projects are proposed by one course
  all c: Course | lone c.courseProjects

}
    S13 in valid iff {
  	all p : Project | (some c : Course | c.courseProjects = p)
	// Projects are proposed by one course

}
    S14 in valid iff {
  	all p : Project | (one c : Course | c.courseProjects = p)
	// Projects are proposed by one course

}
    S15 in valid iff {
  	all p : Project | (one c : Course | c.courseProjects = p)
    all x, y : Course | x != y implies no (x.courseProjects & y.courseProjects)
	// Projects are proposed by one course

}
    S16 in valid iff {
	// Projects are proposed by one course
  	all c1, c2: Course | all p: Project | p in c1.courseProjects and p in c2.courseProjects implies c1 = c2
	
}
    S17 in valid iff {
	// Projects are proposed by one course
  	all p:Project | some c:Course | p in c.courseProjects

}
    S18 in valid iff {
	// Projects are proposed by one course
  // projects.p -> projetos do curso
  all c : Course, p: Project | one (Course<:courseProjects).p

}
    S19 in valid iff {
	// Projects are proposed by one course
	all p : Project | some c1, c2 : Course | c1 in courseProjects.p implies not c2 in courseProjects.p
}
    S20 in valid iff {
	// Projects are proposed by one course
    all c1: Course, c2: Course | no (c1.courseProjects & c2.courseProjects)

}
    S21 in valid iff {
	// Projects are proposed by one course
  some (Course<:courseProjects).Project
}
    S22 in valid iff {
	// Projects are proposed by one course
  	some c:Course | one c.courseProjects

}
    S23 in valid iff {
	// Projects are proposed by one course
  	all c: Course | all p: Project | p in c.courseProjects 

}
    S24 in valid iff {
	// Projects are proposed by one course
  one Course.courseProjects -> Project
}
    S25 in valid iff {
	// Projects are proposed by one course
  all p:Project | all disj c1,c2:Course | p in c1.courseProjects implies p in c2.courseProjects
}
    S26 in valid iff {
	// Projects are proposed by one course
  	all pr : Project | lone (Course <:courseProjects).pr implies  pr in Course
  	

}
    S27 in valid iff {
	// Projects are proposed by one course
	all p: Project | one (Course->(Course.courseProjects)).p
}
    S28 in valid iff {
	// Projects are proposed by one course
  all c:Course ,cnot:Course-c |
  	some p:Project |
  		p in c.courseProjects and p not in cnot

}
    S29 in valid iff {
	// Projects are proposed by one course
  all c:Course ,cnot:Course-c |
  	some p:Project |
  		p in c.courseProjects implies p not in cnot

}
    S30 in valid iff {
	// Projects are proposed by one course
  	lone c: Course | all p: Project | p in c.courseProjects
}
    S31 in valid iff {
	// Projects are proposed by one course
  some p : Project | one c : Course | p in c.courseProjects

}
    S32 in valid iff {
	// Projects are proposed by one course

	all p: Project | some c: Course | c.courseProjects in p
}
    S33 in valid iff {
	// Projects are proposed by one course
	all c:Course | c.courseProjects not in (Course - c).courseProjects
}
    S34 in valid iff {
	// Projects are proposed by one course
	lone Course <: courseProjects.Project
}
    S35 in valid iff {
	// Projects are proposed by one course
	one c : Course | one p : Project | c in courseProjects.p
}
    S36 in valid iff {
	// Projects are proposed by one course
  	all p : Project | some c : Course | lone (Course :> courseProjects.p)

}
    S37 in valid iff {
	// Projects are proposed by one course
	one(Course -> Project)
}
    S38 in valid iff {
	// Projects are proposed by one course
	all p : Project | one c : Course | c in Course :> courseProjects.Project
}
    S39 in valid iff {
	// Projects are proposed by one course
	one c : Course | some c.courseProjects
}
    S40 in valid iff {
	// Projects are proposed by one course
	all p : Project | all c : Course.courseProjects | one p&c
}
    S41 in valid iff {
	// Projects are proposed by one course
	all p : Project, p1 : Person | one c : Course | p in p1.personProjects and p in c.courseProjects
}
    S42 in valid iff {
	// Projects are proposed by one course
  all c : Course, p : Project | p in c.courseProjects and p not in Person.personProjects

}
    S43 in valid iff {
	// Projects are proposed by one course
	(all p: Project|all disj c1, c2: Course| p in c1.courseProjects iff p not in c2.courseProjects)
}
    S44 in valid iff {
	// Projects are proposed by one course
	Person <: personProjects in ((this.@Person + this.@Course + this.@Project + this.@Grade + Int + String + OrderingAtom) <: iden)
}
    S45 in valid iff {
	// Projects are proposed by one course
	(all p: Professor| p.personProjects = p.teaches.courseProjects)
}
    S46 in valid iff {
	// Projects are proposed by one course
	(all p: Professor| p.personProjects = p.teaches.courseProjects) and (all p: Project|all c: Course| p in c.courseProjects implies (no c2: Course| not c2 = c and p in c2.courseProjects))
}
    S47 in valid iff {
	// Projects are proposed by one course
	(all p: Professor| p.teaches = p.teaches.courseProjects) and (all p: Project|all c: Course| p in c.courseProjects implies (no c2: Course| not c2 = c and p in c2.courseProjects))
}
    S48 in valid iff {
	// Projects are proposed by one course
 	some p : Project | one c : Course | some a: Person | p in teaches.c and c in courseProjects.p
  

}
    S49 in valid iff {
	// Projects are proposed by one course
	one c : Course | c.courseProjects in Project
}
    S50 in valid iff {
	// Projects are proposed by one course
	all c : Course | one Course.courseProjects
}
    S51 in valid iff {
	// Projects are proposed by one course
  	some Course.courseProjects
	all disj c1,c2 : Course | no (c1.courseProjects&c2.courseProjects)
}
    S52 in valid iff {
	// Projects are proposed by one course
  	all c : Course | some c.courseProjects
	all disj c1,c2 : Course | no (c1.courseProjects&c2.courseProjects)
}
    S53 in valid iff {
	// Projects are proposed by one course
     one Course.courseProjects


}
    S54 in valid iff {
	// Projects are proposed by one course
  all p:Course.courseProjects | one Course

}
    S55 in valid iff {
	// Projects are proposed by one course
	all disj c1, c2: Course | all p: Project | p in c1.courseProjects and p not in c2.courseProjects
}
    S56 in valid iff {
	// Projects are proposed by one course
  no disj c1, c2:Course | no p1:Project | p1 in c1.courseProjects => p1 in c2.courseProjects

}
    S57 in valid iff {
	// Projects are proposed by one course
	// Assuming one and only one
  
  all x : Project | one p : Professor, c : Course| x in c.courseProjects and p in teaches.c
}
    S58 in valid iff {
	// Projects are proposed by one course
  	// for all projects, it is projects by 1 course
  	all p : Project | one c : Course |
  		one c.courseProjects
	
}
    S59 in valid iff {
	// Projects are proposed by one course
	all x: Project | one Course <: courseProjects
}
    S60 in valid iff {
	// Projects are proposed by one course
	all x: Project | lone Course <: courseProjects
}
    S61 in valid iff {
	// Projects are proposed by one course
	lone Course.courseProjects
}
    S62 in valid iff {
	// Projects are proposed by one course
	all p:Project | some c1,c2:Course | p in c1.courseProjects and p in c2.courseProjects implies c1 = c2
}
    S63 in valid iff {
	// Projects are proposed by one course
  some cx:Course, cy:Course | all p:Project | p in cx.courseProjects implies p not in cy.courseProjects
}
    S64 in valid iff {
	// Projects are proposed by one course
  some cx:Course | all p:Project | p in cx.courseProjects implies all cy:Course | cy != cx and p not in cy.courseProjects
}
    S65 in valid iff {
	// Projects are proposed by one course
  	all c : Course | one Project
}
    S66 in valid iff {
	// Projects are proposed by one course
	// all p: Project | one c: Course | p in c.projects
  	one p: Project | all c: Course.courseProjects | one p & c
}
    S67 in valid iff {
	// Projects are proposed by one course
  all c:Course | some p:Project | p in c.courseProjects
	all p:Project | some c1,c2:Course | p in c1.courseProjects and p in c2.courseProjects implies c1 = c2
}
    S68 in valid iff {
	// Projects are proposed by one course
  all c1,c2:Course | some p:Project | p in c1.courseProjects and p in c2.courseProjects implies c1 = c2
}
    S69 in valid iff {
	// Projects are proposed by one course
  	all disj c1,c2:Course | c1.courseProjects not in c2.courseProjects

}
    S70 in valid iff {
	// Projects are proposed by one course
  	all disj c1,c2:Course |  all p: Project | c1.courseProjects not in c2.courseProjects and (p in c1.courseProjects or p in c2.courseProjects)

}
    S71 in valid iff {
	// Projects are proposed by one course
	all c : Course | some p: Person | p.personProjects in c.courseProjects
}
    S72 in valid iff {
	// Projects are proposed by one course
	some c : Course | all p: Person | p.personProjects in c.courseProjects
}
    S73 in valid iff {
	// Projects are proposed by one course
	all p: Person | some c : Course | c.courseProjects in p.personProjects
}
    S74 in valid iff {
	// Projects are proposed by one course
  one c : Course | all p : Project | p in c
  

}
    S75 in valid iff {
	// Projects are proposed by one course
  	all p : Project | p in Course.courseProjects
  	all a,b : Course | a != b implies a.courseProjects not in b.courseProjects
	all p : Project,  a,b : Course | p in a.courseProjects and a != b implies p not in b.courseProjects    
}
    S76 in valid iff {
	// Projects are proposed by one course
  	all p : Project | p in Course.courseProjects
  	all a,b : Course | a != b implies a.courseProjects not in b.courseProjects
	//all p : Project,  a,b : Course | p in a.projects and a != b implies p not in b.projects    
}
    S77 in valid iff {
	// Projects are proposed by one course
  	all p: Project, c1,c2: Course | ( p in c1.courseProjects and p in c2.courseProjects ) iff c1 = c2

}
    S78 in valid iff {
	// Projects are proposed by one course
  	all p : Project, c : Course | one(c.courseProjects) implies c.courseProjects in p
  	
}
    S79 in valid iff {
	// Projects are proposed by one course
  all p: Project | one c: Course | lone c.courseProjects
  
}
    S80 in valid iff {
	// Projects are proposed by one course
	all c: Course | all c1: Course | one p: Project | (p in c.courseProjects) implies (p not in c1.courseProjects)
}
    S81 in valid iff {
	// Projects are proposed by one course
	Person <: personProjects.~courseProjects :> Course in ((this.@Person + this.@Course + this.@Project + this.@Grade + Int + String + OrderingAtom) <: iden)
}
    S82 in valid iff {
	// Projects are proposed by one course
	one Person <: personProjects.~courseProjects :> Course
}
    S83 in valid iff {
	// Projects are proposed by one course
	Course.courseProjects in Person.personProjects
}
    S84 in valid iff {
	// Projects are proposed by one course
	Person.personProjects in Course.courseProjects
}
    S85 in valid iff {
	// Projects are proposed by one course
	Person.personProjects = Course.courseProjects
}
    S86 in valid iff {
	// Projects are proposed by one course
	Course <: courseProjects in Course one -> some Project
}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, S74, S75, S76, S77, S78, S79, S80, S81, S82, S83, S84, S85, S86 extends Formula {}

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
