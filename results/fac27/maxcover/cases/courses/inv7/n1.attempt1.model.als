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
    Oracle in valid iff {
	// Students work on at most one project per course
  all s: Student, c: Course | lone s.personProjects & c.courseProjects
}
    S1 in valid iff {
	// Students work on at most one project per course
    lone enrolled.courseProjects
}
    S2 in valid iff {
	// Students work on at most one project per course
	Person <: personProjects in (Student -> lone Project)
}
    S3 in valid iff {
	// Students work on at most one project per course

}
    S4 in valid iff {
	// Students work on at most one project per course
	all s: Student | all c: s.enrolled | lone c.courseProjects
}
    S5 in valid iff {
	// Students work on at most one project per course
	all s: Student | one c: s.enrolled | s.personProjects in c
}
    S6 in valid iff {
	// Students work on at most one project per course
	//all c : Course, p : Student | lone c.projects & p.projects
  	all s:Student, c : Course | #s.personProjects&c.courseProjects <= 0 
}
    S7 in valid iff {
	// Students work on at most one project per course
  	//all s : Student, c : Course, p1,p2 : Project | c in s.enrolled and p1 in c.projects and p2 in c.projects and p1 in s.projects and p2 in s.projects implies p1 = p2
  
  all s : Student, c : Course | c in s.enrolled implies one s.enrolled.courseProjects

}
    S8 in valid iff {
	// Students work on at most one project per course
  all s : Student | one c : Course | s.personProjects in c 

}
    S9 in valid iff {
	// Students work on at most one project per course
	all s : Student | all c : s.enrolled | one(s.personProjects & c.courseProjects)
}
    S10 in valid iff {
	// Students work on at most one project per course
  	all s:Student | all pr1, pr2:Project | one c: Course | 
  	pr1 in s.personProjects and pr2 in s.personProjects and pr1 in c.courseProjects and c in s.enrolled implies pr2 not in c.courseProjects

}
    S11 in valid iff {
	// Students work on at most one project per course
  all s : Student, c:Course | one(s.personProjects & c.courseProjects) 

}
    S12 in valid iff {
	// Students work on at most one project per course
	all s : Student | some c : Course | lone(s.personProjects &  c.courseProjects)
}
    S13 in valid iff {
	// Students work on at most one project per course
	all s : Student | some c : Course | one p : c.courseProjects | p in s.personProjects
}
    S14 in valid iff {
	// Students work on at most one project per course
  all s:Student | all c:s.enrolled | #(s.personProjects) = 1

}
    S15 in valid iff {
	// Students work on at most one project per course
  	all s: Student | one s.enrolled.courseProjects  
}
    S16 in valid iff {
	// Students work on at most one project per course
  	all s: Student | lone s.enrolled.courseProjects 
}
    S17 in valid iff {
	// Students work on at most one project per course
	all s : Student | lone p : Project | all c : Course | c in s.enrolled implies p in c.courseProjects
}
    S18 in valid iff {
	// Students work on at most one project per course
  	all s: Student | some s.personProjects
}
    S19 in valid iff {
	// Students work on at most one project per course
	all s: Student | one c:s.enrolled | one proj:s.personProjects | c = proj 
}
    S20 in valid iff {
	// Students work on at most one project per course
	all s : Student | one p : Project | p in s.personProjects
}
    S21 in valid iff {
	// Students work on at most one project per course
  	one (Person <: personProjects).{p:Project, c:Course | c->p in courseProjects}

}
    S22 in valid iff {
	// Students work on at most one project per course
	all s : Student | some c : Course | c in s.enrolled => lone(s.enrolled.courseProjects - s.personProjects)
}
    S23 in valid iff {
	// Students work on at most one project per course
	all s : Student | all c : s.enrolled | one p : Project | c.courseProjects=p
}
    S24 in valid iff {
	// Students work on at most one project per course
	all s : Student | some c : Course | c in s.enrolled => 								lone(s.enrolled.courseProjects & s.personProjects)
}
    S25 in valid iff {
	// Students work on at most one project per course
	all s : Student | all c : s.enrolled | lone (s.enrolled.courseProjects - 					c.courseProjects)
}
    S26 in valid iff {
	// Students work on at most one project per course
	all s : Student | all c : s.enrolled | lone(s.personProjects - c.courseProjects)
}
    S27 in valid iff {
	// Students work on at most one project per course

        // all s : Student | all c : Course | lone pr : Project | c->pr in projects and s->pr in projects

        // all s : Student | all c : Course | lone pr : Project | pr in c.projects and pr in s.projects

        // all s : Student | all c : Course | lone pr : Project | pr in (c.projects & s.projects)

        all s : Student, c : Course | some (c.courseProjects & s.personProjects)
}
    S28 in valid iff {
	// Students work on at most one project per course
  all s:Student | some s.enrolled
}
    S29 in valid iff {
	// Students work on at most one project per course
  all s:Student | some s.enrolled.courseProjects
}
    S30 in valid iff {
	// Students work on at most one project per course
  all s:Student, c:s.enrolled | (lone ((courseProjects)))

}
    S31 in valid iff {
	// Students work on at most one project per course
  all s:Student | lone s.enrolled

}
    S32 in valid iff {
	// Students work on at most one project per course
  all s:Student | lone enrolled->(s.personProjects)

}
    S33 in valid iff {
	// Students work on at most one project per course
  //all c : Course | all disj x, y : c.projects | no ((Person<:projects).x & (Person<:projects).y
  
  //(Person<:projects)
    
  all c : Course | all mitglieder : enrolled.c | lone (Person<:personProjects).(c.courseProjects)

}
    S34 in valid iff {
	// Students work on at most one project per course
	all c : Course | one c.courseProjects
}
    S35 in valid iff {
	// Students work on at most one project per course
  all s: Student, c: Course | one p: Project | p in s.enrolled.courseProjects 

}
    S36 in valid iff {
	// Students work on at most one project per course
	// all c : Course | one c.projects
  
  	all s : Student, c : Course | one s.enrolled.courseProjects and one c.courseProjects
   
  	// all s : Student, c : Course, p1,p2 : Project | c in s.enrolled and p1 in c.projects and p2 in c.projects and p1 in s.projects and p2 in s.projects implies p1 = p2
}
    S37 in valid iff {
	// Students work on at most one project per course
  	all s : Student, c : s.enrolled | lone c.courseProjects and lone s.personProjects
  	
    // all s : Student, c : Course, p1,p2 : Project | c in s.enrolled and p1 in c.projects and p2 in c.projects and p1 in s.projects and p2 in s.projects implies p1 = p2
}
    S38 in valid iff {
	// Students work on at most one project per course 
  	all s:Student,proj:s.personProjects|some c:Course | proj in c.courseProjects implies c.courseProjects - proj not in s.personProjects
}
    S39 in valid iff {
	// Students work on at most one project per course 
  	all s:Student , proj:s.personProjects | one c:Course | proj in c.courseProjects implies c.courseProjects - proj not in s.personProjects
}
    S40 in valid iff {
	// Students work on at most one project per course
	all s: Student, p: s.enrolled |
  		(s.personProjects not in p.courseProjects) or (one proj: s.personProjects | proj not in p.courseProjects - proj)
}
    S41 in valid iff {
	// Students work on at most one project per course
	all s : Student, c : Course | one c.courseProjects implies s in enrolled.c
}
    S42 in valid iff {
	// Students work on at most one project per course
	all s : Student, c : Course | lone c.courseProjects implies s in enrolled.c
}
    S43 in valid iff {
	// Students work on at most one project per course
	all s: Student | lone c: s.enrolled.courseProjects | s.personProjects in c
}
    S44 in valid iff {
	// Students work on at most one project per course
	all s : Student |all c : s.enrolled | s.personProjects & c.courseProjects = 1
}
    S45 in valid iff {
	// Students work on at most one project per course
  	all s : Student | all c : Course | lone p : Project | c in s.enrolled implies p in s.personProjects

}
    S46 in valid iff {
	// Students work on at most one project per course
	all s : Person - Professor | all c : s.enrolled | one p : s.personProjects | p in c.courseProjects 
}
    S47 in valid iff {
	// Students work on at most one project per course
	all s : Person - Professor | all c : s.enrolled | lone(s.personProjects & c.courseProjects)
}
    S48 in valid iff {
	// Students work on at most one project per course
	all s: Student, c : s.enrolled, p : s.personProjects | lone( c.courseProjects + p)
}
    S49 in valid iff {
	// Students work on at most one project per course
  	all s : Student | all c : Course | lone p : Project | c in s.enrolled implies
  		((c.courseProjects & s.personProjects) = p)

}
    S50 in valid iff {
	// Students work on at most one project per course
  	all s : Student, c : Course | one p : Project | c in s.enrolled implies
  		((c.courseProjects & s.personProjects) = p)

}
    S51 in valid iff {
	// Students work on at most one project per course
	all s:Student, c:Course | one s.personProjects <: Person & c.courseProjects <: Course
}
    S52 in valid iff {
	// Students work on at most one project per course

	all s: Student | one p: Project | s.personProjects in p

}
    S53 in valid iff {
	// Students work on at most one project per course
    // all s : Student, c : Course, p1,p2 : Project | c in s.enrolled and p1 in c.projects and p2 in c.projects and p1 in s.projects and p2 in s.projects implies p1 = p2
   all s : Student, c : Course, p1 : Project | c in s.enrolled and lone c.courseProjects
}
    S54 in valid iff {
	// Students work on at most one project per course
    // all s : Student, c : Course, p1,p2 : Project | c in s.enrolled and p1 in c.projects and p2 in c.projects and p1 in s.projects and p2 in s.projects implies p1 = p2
   all s : Student, c : Course | c in s.enrolled and lone c.courseProjects
}
    S55 in valid iff {
	// Students work on at most one project per course
  	~enrolled.personProjects in Course -> lone Project

}
    S56 in valid iff {
	// Students work on at most one project per course
  	one enrolled.courseProjects & Student <: personProjects

}
    S57 in valid iff {
	// Students work on at most one project per course
	all p : Person | one pr : Project | p in Student and pr in p.enrolled
}
    S58 in valid iff {
	// Students work on at most one project per course
	all p : Person | all pr1, pr2 : Project | some c : Course | p in Student and pr1 in p.personProjects and pr2 in p.personProjects and pr1 in c.courseProjects and pr2 in c.courseProjects implies pr1 = pr2
}
    S59 in valid iff {
	// Students work on at most one project per course
	all p : Person | one pr : Project | some c : Course | p in Student and c in p.enrolled implies pr in p.personProjects
}
    S60 in valid iff {
	// Students work on at most one project per course
	all p : Person | one pr : Project | some c : Course | p in Student and c in p.enrolled and pr in p.personProjects implies pr in c.courseProjects
}
    S61 in valid iff {
	// Students work on at most one project per course
	all p : Person | all pr : Project | one c : Course | p in Student and c in p.enrolled and pr in p.personProjects implies pr in c.courseProjects
}
    S62 in valid iff {
	// Students work on at most one project per course
  	all s : Person | some p : Project | all c : Course | s in Student and c in s.enrolled and p in s.personProjects implies p in c.courseProjects
}
    S63 in valid iff {
	// Students work on at most one project per course
  	all s : Person | some p : Project | all c : Course | s in Student and c in s.enrolled and p in c.courseProjects implies p in s.personProjects
}
    S64 in valid iff {
	// Students work on at most one project per course
  	all s : Student |
  		all c : s.enrolled |
  			some p : s.personProjects | p in c.courseProjects
}
    S65 in valid iff {
	// Students work on at most one project per course
   no disj s1, s2: Student, c: Course | s1.personProjects & c.courseProjects & s2.personProjects != none

}
    S66 in valid iff {
	// Students work on at most one project per course
	all x : Student, c : Course | lone p : Project | p in x.personProjects and c in x.enrolled implies p in c.courseProjects
}
    S67 in valid iff {
	// Students work on at most one project per course
all x : Student, p1,p2 : Project, c1,c2 : Course | (x->p1 in personProjects and x->p2 in personProjects and c1->p1 in courseProjects and c2->p2 in courseProjects ) implies(c1=c2)

}
    S68 in valid iff {
	// Students work on at most one project per course
	all s : Student | all p : s.personProjects | some c : Course | p in c.courseProjects implies no p2 : c.courseProjects | p != p2 implies not p2 in s.enrolled
}
    S69 in valid iff {
	// Students work on at most one project per course
	all s : Student | all p : s.personProjects | no c : Course | p in c.courseProjects implies no p2 : c.courseProjects | p != p2 implies p2 in s.enrolled
}
    S70 in valid iff {
	// Students work on at most one project per course
  	all s : Student | lone c : s.enrolled | one p : s.personProjects | p in c.courseProjects

}
    S71 in valid iff {
	// Students work on at most one project per course
	all s : Student | all c : Course | c in s.enrolled implies ((one pro : Project | pro in c.courseProjects and pro in s.personProjects) or (all pro: Project | pro in c.courseProjects and pro not in s.personProjects))
}
    S72 in valid iff {
	// Students work on at most one project per course
	all s : Student , p : Project| p in s.personProjects and lone (Course<:courseProjects).p
}
    S73 in valid iff {
	// Students work on at most one project per course
	all s : Student | all c : Course | ((one pro : Project | pro in c.courseProjects and pro in s.personProjects) or (all pro: Project | (pro in c.courseProjects) and not (pro in s.personProjects)))
}
    S74 in valid iff {
	// Students work on at most one project per course
	all s : Person | all c : Course | ((one pro : Project | pro in c.courseProjects and pro in s.personProjects) or (all pro: Project | (pro in c.courseProjects) and not (pro in s.personProjects)))
}
    S75 in valid iff {
	// Students work on at most one project per course
	all s : Student | s.personProjects = s.enrolled.courseProjects
}
    S76 in valid iff {
	// Students work on at most one project per course
  	all s: Student | some (Course.courseProjects)
  	// all s: Student, c: s.enrolled | lone (s.projects & c.projects)
}
    S77 in valid iff {
	// Students work on at most one project per course
  	all s: Student | one (Course.courseProjects)
  	// all s: Student, c: s.enrolled | lone (s.projects & c.projects)
}
    S78 in valid iff {
	// Students work on at most one project per course
      lone ((personProjects & (Person->Project)) & (enrolled.(courseProjects & (Course->Project))))


}
    S79 in valid iff {
	// Students work on at most one project per course
	all s:Student | lone p:Project | all c:Course |
  		c in s.enrolled implies p in s.personProjects
  
}
    S80 in valid iff {
	// Students work on at most one project per course
	all s:Student | lone p:Project | all c:Course |
  		c in s.enrolled and p in s.personProjects implies p in c.courseProjects
  
}
    S81 in valid iff {
	// Students work on at most one project per course
	all s:Student | lone p:Project | all c:Course |
  		c in s.enrolled implies p in s.personProjects and (p in c.courseProjects)
}
    S82 in valid iff {
	// Students work on at most one project per course
	all s : Student | some c : s.enrolled | lone s.personProjects & c.courseProjects
}
    S83 in valid iff {
	// Students work on at most one project per course
	#Student<:personProjects <= 1
}
    S84 in valid iff {
	// Students work on at most one project per course
	Course <: courseProjects in Course one -> one Student
}
    S85 in valid iff {
	// Students work on at most one project per course
	all s : Student, c : Course | one pr : Project | pr in s.personProjects implies (c in s.enrolled and pr in c.courseProjects)
}
    S86 in valid iff {
	// Students work on at most one project per course
	all s : Student| some c : Course | one pr : Project | pr in s.personProjects implies (c in s.enrolled and pr in c.courseProjects)
}
    S87 in valid iff {
	// Students work on at most one project per course
	all s : Student, c : Course | lone pr : Project | pr in s.personProjects implies (c in s.enrolled and pr in c.courseProjects)
}
    S88 in valid iff {
	// Students work on at most one project per course
	all s: Student | one sCourse : s.enrolled | 
  		#(sCourse.courseProjects & s.personProjects) <=1
}
    S89 in valid iff {
	// Students work on at most one project per course
	all s: Student | one c: Course | c in s.enrolled implies
  		#(c.courseProjects & s.personProjects) <=1
}
    S90 in valid iff {
	// Students work on at most one project per course
  	all s : Student, c : Course | one p : Project | p in c.courseProjects and p in s.personProjects implies c in s.enrolled

}
    S91 in valid iff {
	// Students work on at most one project per course
 all s:Student | all c:Course | all p1,p2:Project | p1 in s.personProjects and  p2 in s.personProjects and c in s.enrolled implies p1 in c.courseProjects and p2 in c.courseProjects and p1 = p2
}
    S92 in valid iff {
	// Students work on at most one project per course
	all p: Project | all c: Course | one s: Student | c in s.enrolled and p in c.courseProjects and p in s.personProjects
}
    S93 in valid iff {
	// Students work on at most one project per course
	all p: Project | all c: Course | one s: Student | c in s.enrolled and lone s.personProjects }
    S94 in valid iff {
	// Students work on at most one project per course
	    all s: Student | all c: Course| c in s.enrolled and lone p: c.courseProjects | p in s.personProjects
}
    S95 in valid iff {
	// Students work on at most one project per course
  all c : Course | some enrolled.c.personProjects

}
    S96 in valid iff {
	// Students work on at most one project per course
  all s:Person,c:Course | s in Student && lone (s.personProjects & c.courseProjects)
   
  // Só pode ser um estudante a trabalhar num projeto por curso

}
    S97 in valid iff {
	// Students work on at most one project per course
  one s : Student | all p : Project | (p in s.personProjects) or not(p in s.personProjects)
}
    S98 in valid iff {
	// Students work on at most one project per course
	all s : Student | all p1,p2 : s.personProjects | one c : Course | p1 in c.courseProjects and p2 in c.courseProjects implies p1 = p2

}
    S99 in valid iff {
	// Students work on at most one project per course
	all s:Student | all c: Course | lone p: Project | c in s.enrolled and p in c.courseProjects implies p in s.personProjects
}
    S100 in valid iff {
	// Students work on at most one project per course
	all s:Student | all c: Course | c in s.enrolled and lone p: Project | p in c.courseProjects implies p in s.personProjects
  
 
  //all s: Student | all c: s.enrolled | lone p: c.projects | p in s.projects

}
    S101 in valid iff {
	// Students work on at most one project per course
	  all s : Student | one (Course <: courseProjects).(s.personProjects) 

  
  
}
    S102 in valid iff {
	// Students work on at most one project per course
	all c : Course | some s : Student | one p : c.courseProjects | p in s.personProjects
}
    S103 in valid iff {
	// Students work on at most one project per course
	no s : Student | some c : Course | lone c.courseProjects & s.personProjects 
}
    S104 in valid iff {
	// Students work on at most one project per course
  	all s : Student | s not in Professor and  all c : Course | c in s.enrolled implies #(c.courseProjects) <= 1
}
    S105 in valid iff {
	// Students work on at most one project per course
  all s: Student, c: Course | lone p: Project | c in s.enrolled implies p in s.personProjects & c.courseProjects

}
    S106 in valid iff {
	// Students work on at most one project per course
	//all p: Student, c: Course| one y: Project| p in enrolled.c and c in projects.y implies project.y
	all p: Student, c: Course| one y: Project | p in enrolled.c implies y in p.personProjects //and c.projects in p.enrolled 

}
    S107 in valid iff {
	// Students work on at most one project per course
	lone {s: Student, c: Course, p: c.courseProjects | p = s.personProjects}
}
    S108 in valid iff {
	// Students work on at most one project per course
	enrolled.courseProjects in Person -> one Project
}
    S109 in valid iff {
	// Students work on at most one project per course
  all s: Student, c:Course | lone p: Project | p in c.courseProjects implies p in s.personProjects

}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, S74, S75, S76, S77, S78, S79, S80, S81, S82, S83, S84, S85, S86, S87, S88, S89, S90, S91, S92, S93, S94, S95, S96, S97, S98, S99, S100, S101, S102, S103, S104, S105, S106, S107, S108, S109 extends Formula {}

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
