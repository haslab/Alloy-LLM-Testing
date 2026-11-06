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
    // Earlier requirement 8, required in every Instance.
{
	// A professor cannot teach colleagues
	all p : Person | no (p.teaches.~teaches - p) & p.teaches.~enrolled
}
    // Earlier requirement 9, required in every Instance.
{
	// Only students have grades
	Course.(instanceGrades[this]).Grade in Student
}
    // Earlier requirement 10, required in every Instance.
{
	// Students only have grades in courses they are enrolled
	all s : Student, c : Course | some c.(instanceGrades[this])[s] implies c in s.enrolled
}
    Oracle in valid iff {
	// Students have at most one grade per course
	all s : Student, c : Course | lone c.(instanceGrades[this])[s] 
}
    S1 in valid iff {
	// Students have at most one grade per course
	all s:Student, c:Course | lone c.(instanceGrades[this]).s
}
    S2 in valid iff {
	// Students have at most one grade per course
	all p: Student | all c: Course | (one c.(instanceGrades[this])[p])
}
    S3 in valid iff {
	// Students have at most one grade per course
	// all s : Student | all c : Course |
	//   lone g : Grade | c->s->g in grades

	// all s : Student, c : Course | lone s.(c.grades)

	lone Student.(Course.(instanceGrades[this]))
}
    S4 in valid iff {
	// Students have at most one grade per course
	// all s : Student | all c : Course |
	//   lone g : Grade | c->s->g in grades

	// all s : Student, c : Course | lone s.(c.grades)

	all s : Student | lone s.(Course.(instanceGrades[this]))

  	// WRONG!! 
	// lone Student.(Course.grades)
}
    S5 in valid iff {
	// Students have at most one grade per course
	// all s : Student | all c : Course |
	//   lone g : Grade | c->s->g in grades

	// all s : Student, c : Course | lone s.(c.grades)

	all c : Course | lone Student.(c.(instanceGrades[this]))

  	// WRONG!! 
	// lone Student.(Course.grades)
}
    S6 in valid iff {
	// Students have at most one grade per course
	one Course.(instanceGrades[this]).Person
}
    S7 in valid iff {
	// Students have at most one grade per course
	all s : Student | one Course.(instanceGrades[this]).s
}
    S8 in valid iff {
	// Students have at most one grade per course
  	all p : Person , c : Course | one p.(c.(instanceGrades[this]))
  	

}
    S9 in valid iff {
	// Students have at most one grade per course
	all p : Professor | all c : p.enrolled | lone(p.(c.(instanceGrades[this])))
}
    S10 in valid iff {
	// Students have at most one grade per course
  all s: Student , c: Course | one c.(instanceGrades[this]).s

}
    S11 in valid iff {
	// Students have at most one grade per course
    all s : Student, c : Course | lone (s.enrolled.(instanceGrades[this]) & c.(instanceGrades[this]))

}
    S12 in valid iff {
	// Students have at most one grade per course
    all s : Student, c : Course | lone (s.enrolled.(instanceGrades[this]) - c.(instanceGrades[this]))

}
    S13 in valid iff {
	// Students have at most one grade per course
	all s : Student | all c : Course | some (s.enrolled & c) implies one (c.(instanceGrades[this]).Grade & s)
}
    S14 in valid iff {
	// Students have at most one grade per course
	all s1, s2 : Student, c : Course | some s1.(c.(instanceGrades[this])) and some s2.(c.(instanceGrades[this])) implies s1 = s2
}
    S15 in valid iff {
	// Students have at most one grade per course
  	all s : Student, c : s.enrolled | one c.(instanceGrades[this]).Grade 

}
    S16 in valid iff {
	// Students have at most one grade per course
  all s:Student | all c:s.enrolled | one s.(c.(instanceGrades[this]))

}
    S17 in valid iff {
	// Students have at most one grade per course
	all s : Student | one(s.enrolled.(instanceGrades[this])) 
}
    S18 in valid iff {
	// Students have at most one grade per course
	all s : Student | lone(s.enrolled.(instanceGrades[this])) 
}
    S19 in valid iff {
	// Students have at most one grade per course
  all c: Course | all g1, g2: Person.(c.(instanceGrades[this])) | 
  		(g1 != g2) 

}
    S20 in valid iff {
	// Students have at most one grade per course
  	all c : Course | all p : Student | lone g : Grade | c in p.enrolled implies p->g in c.(instanceGrades[this])

}
    S21 in valid iff {
	// Students have at most one grade per course
	all s : Student | lone g : Grade | all c : s.enrolled | c.(instanceGrades[this])[s] = g
}
    S22 in valid iff {
	// Students have at most one grade per course
	all s : Student | lone g : Grade | all c : Course | c.(instanceGrades[this])[s] = g
}
    S23 in valid iff {
	// Students have at most one grade per course
	all s : Student, c : Course | one (c.(instanceGrades[this]).Grade)
}
    S24 in valid iff {
	// Students have at most one grade per course
	all s : Student, g : Grade, c : Course | lone s->g => s->g in c.(instanceGrades[this])
}
    S25 in valid iff {
	// Students have at most one grade per course
    one s: Student, c: Course | lone s.enrolled.(instanceGrades[this])


}
    S26 in valid iff {
	// Students have at most one grade per course
    some s: Student, c: Course | lone s.enrolled.(instanceGrades[this])


}
    S27 in valid iff {
	// Students have at most one grade per course
	all s : Student, c : Course |
  		some s.(c.(instanceGrades[this]))
}
    S28 in valid iff {
	// Students have at most one grade per course
  	all s : Student, c : Course | one s->c.(instanceGrades[this])

}
    S29 in valid iff {
	// Students have at most one grade per course
	
  all c : Course , g : Grade | one ( c.(instanceGrades[this]).g) 
  
  
}
    S30 in valid iff {
	// Students have at most one grade per course
	
  all c : Course , p : Person | one ( c.(instanceGrades[this]))
  
  
}
    S31 in valid iff {
	// Students have at most one grade per course
  	all c: Course, g: Grade | lone (enrolled.c & c.(instanceGrades[this]).g) 

}
    S32 in valid iff {
	// Students have at most one grade per course
	all c: Course | all s: Student | one (s.enrolled.(instanceGrades[this]).Grade) 
}
    S33 in valid iff {
	// Students have at most one grade per course
	all s: Student | all g: Grade | all c: Course | 
  		(#(((instanceGrades[this])))) <= 1
}
    S34 in valid iff {
	// Students have at most one grade per course
	all s: Student | all g: Grade | one c: Course | 
  		#(c->s->g & (instanceGrades[this])) <=  1
}
    S35 in valid iff {
	// Students have at most one grade per course
	all s: Student | all g: Grade | all c1, c2: Course | 
  		c1->s->g in (instanceGrades[this]) and c2->s->g in (instanceGrades[this])
  			implies c1 = c2
}
    S36 in valid iff {
	// Students have at most one grade per course
	
    all c : Course | lone g : Grade | all s : Student | s in c.(instanceGrades[this]).g
  
}
    S37 in valid iff {
	// Students have at most one grade per course
  all s: Student | lone (Course.(instanceGrades[this]).Grade)

}
    S38 in valid iff {
	// Students have at most one grade per course
	all p:Student | some c:Course | all g1,g2:Grade | p->g2 in c.(instanceGrades[this]) and p->g2 in c.(instanceGrades[this]) implies g1=g2
}
    S39 in valid iff {
	// Students have at most one grade per course
 all x: Student | some (x.enrolled.(instanceGrades[this]))
}
    S40 in valid iff {
	// Students have at most one grade per course
	all s:Student, c:s.enrolled | #(s & c.(instanceGrades[this]).Grade) >1
}
    S41 in valid iff {
   all c : Course | all s : Student| lone c.(instanceGrades[this])[s] implies c in s.enrolled
	// Students have at most one grade per course

}
    S42 in valid iff {
	// Students have at most one grade per course
	all p : Person | one Course.(instanceGrades[this]).p
}
    S43 in valid iff {
	// Students have at most one grade per course
	one Course.(instanceGrades[this]).Grade
}
    S44 in valid iff {
	// Students have at most one grade per course
	all s: Student, g: Grade, c: s.enrolled | s->g in c.(instanceGrades[this])
}
    S45 in valid iff {
	// Students have at most one grade per course
	//all s: Student, c: Course | lone ( s <: c.grades)
	lone (Student <: Course.(instanceGrades[this]))
}
    S46 in valid iff {
	// Students have at most one grade per course
  all s : Student | lone s.enrolled.(instanceGrades[this]).Grade

}
    S47 in valid iff {
	// Students have at most one grade per course
  all s:Student | #(s.(Course.(instanceGrades[this]))) = 1

}
    S48 in valid iff {
	// Students have at most one grade per course
  all s:Student|one c:Course | lone s.(Course.(instanceGrades[this]))

}
    S49 in valid iff {
	// Students have at most one grade per course
  all s:Student|one c:Course | lone s.(c.(instanceGrades[this]))

}
    S50 in valid iff {
	// Students have at most one grade per course
  all s: Student, c: Course | s in enrolled.c implies (one c.(instanceGrades[this]))
}
    S51 in valid iff {
	// Students have at most one grade per course
	all c : Course | all p : c.(instanceGrades[this]).Grade | lone p.enrolled.(instanceGrades[this])
}
    S52 in valid iff {
	// Students have at most one grade per course
  all s: Student, c: Course | one g: Grade| (s->g in c.(instanceGrades[this])) implies (lone c.(instanceGrades[this]))
}
    S53 in valid iff {
	// Students have at most one grade per course
  all s: Student, c: Course | lone g: Grade| (s->g in c.(instanceGrades[this])) implies (lone c.(instanceGrades[this]))
}
    S54 in valid iff {
	// Students have at most one grade per course
	some Student -> Course -> Grade
}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54 extends Formula {}

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
