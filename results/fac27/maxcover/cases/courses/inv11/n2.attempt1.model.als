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
    Oracle in valid iff {
	// Students only have grades in courses they are enrolled
	all s : Student, c : Course | some c.(instanceGrades[this])[s] implies c in s.enrolled
}
    S1 in valid iff {
	// Students only have grades in courses they are enrolled

}
    S2 in valid iff {
	all c: Course | c.(instanceGrades[this]).Grade in c.enrolled
}
    S3 in valid iff {
	// Students only have grades in courses they are enrolled
	Course.(instanceGrades[this]).Grade in enrolled.Course
}
    S4 in valid iff {
	// Students only have grades in courses they are enrolled
	no c : Course | some s : Student - c.~enrolled | s -> c.(instanceGrades[this])[s] in c.(instanceGrades[this])
}
    S5 in valid iff {
	// Students only have grades in courses they are enrolled
	all s:Student | s.enrolled.(instanceGrades[this])[s] = Course.(instanceGrades[this])[s]
}
    S6 in valid iff {
	// Students only have grades in courses they are enrolled
	all s : Student | all c : s.enrolled | some(c.(instanceGrades[this]))
}
    S7 in valid iff {
	// Students only have grades in courses they are enrolled
      all s: Student |
    all c: s.enrolled |
    some g: Grade | g in c.(instanceGrades[this])[s]

}
    S8 in valid iff {
	// Students only have grades in courses they are enrolled
	all s : Student | all c : Course | some((instanceGrades[this]).Grade) => c in s.enrolled
}
    S9 in valid iff {
	// Students only have grades in courses they are enrolled
	all s : Student, c : Course | some(c.(instanceGrades[this])) implies c in s.enrolled
}
    S10 in valid iff {
	// Students only have grades in courses they are enrolled
	all s: Student | some c: Course | some s.(c.(instanceGrades[this])) implies c in s.enrolled and some s.enrolled
}
    S11 in valid iff {
	// Students only have grades in courses they are enrolled
	all s: Student, c: Course |
  		(s->Grade) in c.(instanceGrades[this]) => c in s.enrolled
}
    S12 in valid iff {
	// Students only have grades in courses they are enrolled
  	all p: Student | all g: p.(p.enrolled.(instanceGrades[this])) | p.(Course.(instanceGrades[this])) in g

}
    S13 in valid iff {
	// Students only have grades in courses they are enrolled
	all s:Student,c:s.enrolled | one c.(instanceGrades[this])[s]
}
    S14 in valid iff {
	// Students only have grades in courses they are enrolled
  all p: Student , c: Course | p in c.(instanceGrades[this]).Grade & p.enrolled

}
    S15 in valid iff {
	// Students only have grades in courses they are enrolled
  	((instanceGrades[this]).Grade) = ~enrolled

}
    S16 in valid iff {
	// Students only have grades in courses they are enrolled
	all s : Student, c : Course | lone(c.(instanceGrades[this])) implies c in s.enrolled
}
    S17 in valid iff {
	// Students only have grades in courses they are enrolled
	all s:Student | Student.enrolled.(instanceGrades[this])[s] = Course.(instanceGrades[this])[s]
}
    S18 in valid iff {
	// Students only have grades in courses they are enrolled
	all s:Student | s.enrolled.(instanceGrades[this])[s] = Course.(instanceGrades[this])[s]
    all disj c1,c2:Course | no (c1.(instanceGrades[this]) & c2.(instanceGrades[this]))
}
    S19 in valid iff {
	// Students only have grades in courses they are enrolled
   all c: Course | all p: Student | c in p.enrolled implies lone p.(c.(instanceGrades[this]))

}
    S20 in valid iff {
	// Students only have grades in courses they are enrolled
	all s: Student, c: Course | c in c.(instanceGrades[this]).Grade  iff c in s.enrolled
  
  //pe not in Student implies pe not in Course.grades.Grade 
}
    S21 in valid iff {
	// Students only have grades in courses they are enrolled
	all s : Person - Professor | all c : Course - s.enrolled | s not in c.(instanceGrades[this]).Grade
}
    S22 in valid iff {
	// Students only have grades in courses they are enrolled
  	some teaches.Course

}
    S23 in valid iff {
	// Students only have grades in courses they are enrolled
	all s : Student | s.enrolled.(instanceGrades[this]) in s.enrolled->Grade
}
    S24 in valid iff {
	// Students only have grades in courses they are enrolled
	all s: Student | some ((instanceGrades[this]).s)
}
    S25 in valid iff {
	// Students only have grades in courses they are enrolled
	all s : Student, c : Course | c in s.enrolled implies some((instanceGrades[this]).Grade.s)
}
    S26 in valid iff {
	// Students only have grades in courses they are enrolled

	all p: Person, c: Course, g: Grade | g in c.(instanceGrades[this])[p] implies p.enrolled in c

}
    S27 in valid iff {
	// Students only have grades in courses they are enrolled
	all s:Student | all g : Grade | some c:Course | s in c.(instanceGrades[this]).g implies c in s.enrolled 
}
    S28 in valid iff {
	// Students only have grades in courses they are enrolled
	all s : Person | all g : Grade | some c : Course | s->g in c.(instanceGrades[this]) implies c in s.enrolled
}
    S29 in valid iff {
	// Students only have grades in courses they are enrolled
	all s : Person | some g : Grade | some c : Course | s->g in c.(instanceGrades[this]) implies (c in s.enrolled and s in Student)
}
    S30 in valid iff {
	// Students only have grades in courses they are enrolled
    all s : Student | (instanceGrades[this]) in s.enrolled -> s -> Grade
}
    S31 in valid iff {
	// Students only have grades in courses they are enrolled
	all p : Person, g : Grade, c : Course | some p.enrolled implies p->g in c.(instanceGrades[this])
}
    S32 in valid iff {
	// Students only have grades in courses they are enrolled
	all c:Course | all s:Student | c.(instanceGrades[this]).Grade in s implies c in s.enrolled
}
    S33 in valid iff {
	// Students only have grades in courses they are enrolled
	all c:Course | all s:Student | ((instanceGrades[this]).Grade.s in c) implies (c in s.enrolled)
}
    S34 in valid iff {
	// Students only have grades in courses they are enrolled
	all s:Student | one c:s.enrolled | ((instanceGrades[this]).Grade).s in c
}
    S35 in valid iff {
	// Students only have grades in courses they are enrolled
	all s:Student | some c:s.enrolled | ((instanceGrades[this]).Grade).s in c
}
    S36 in valid iff {
	// Students only have grades in courses they are enrolled
	all s : Student | Course.(instanceGrades[this]) = s.enrolled->Grade
}
    S37 in valid iff {
	// Students only have grades in courses they are enrolled
all s : Student | all c : Course | s.enrolled not in c implies no(s->Grade)
}
    S38 in valid iff {
	// Students only have grades in courses they are enrolled
 	all s : Student, c:Course, g:Grade| g = s.(c.(instanceGrades[this])) implies s in enrolled.c
}
    S39 in valid iff {
	// Students only have grades in courses they are enrolled
  all s: Student, c: Course , g: Grade | s in enrolled.c implies s->g in c.(instanceGrades[this])

}
    S40 in valid iff {
	// Students only have grades in courses they are enrolled
  all c : Course | c in c.(instanceGrades[this]).Person.enrolled

}
    S41 in valid iff {
	// Students only have grades in courses they are enrolled
	//all c : Course | all p : c.grades.Grade | c in p.enrolled
  	all c : Course | c in c.(instanceGrades[this]).Grade.enrolled
}
    S42 in valid iff {
    // Students only have grades in courses they are enrolled
  all p: Person | all g:Grade | p->g in Course.(instanceGrades[this]) implies p->Course in enrolled

}
    S43 in valid iff {
	// Students only have grades in courses they are enrolled
  	all s : Student | some c : s.enrolled |
  	s in c.(instanceGrades[this]).Grade  
  	

}
    S44 in valid iff {
	// Students only have grades in courses they are enrolled
	//all s: Student, c: Course | c not in s.enrolled => s not in c.grades.Grade
	Course.(instanceGrades[this]) in Student -> some Grade
}
    S45 in valid iff {
	// Students only have grades in courses they are enrolled
	all c: Course | some c.(instanceGrades[this]).Grade implies c in c.(instanceGrades[this]).Grade.enrolled
}
    S46 in valid iff {
	// Students only have grades in courses they are enrolled
   all c: Course | all p: Student | c in p.enrolled and lone p.(c.(instanceGrades[this]))

}
    S47 in valid iff {
	// Students only have grades in courses they are enrolled
   all c: Course | all p: Person - Professor| c in p.enrolled and lone p.(c.(instanceGrades[this]))

}
    S48 in valid iff {
	// Students only have grades in courses they are enrolled
	all c: Course, s: Student | lone s.(c.(instanceGrades[this])) => c in s.enrolled
}
    S49 in valid iff {
	// Students only have grades in courses they are enrolled
	all s : Student, e : s.enrolled, t: s.teaches | no s <: (Course - e - t).(instanceGrades[this])
}
    S50 in valid iff {
	// Students only have grades in courses they are enrolled
	all s : Student, c : s.enrolled | no (s <: Course.(instanceGrades[this]))
}
    S51 in valid iff {
	// Students only have grades in courses they are enrolled
	enrolled.Course->Grade in Course.(instanceGrades[this]) 
}
    S52 in valid iff {
	// Students only have grades in courses they are enrolled
	all s : Student | s.enrolled.(instanceGrades[this]) in s->Grade
}
    S53 in valid iff {
	// Students only have grades in courses they are enrolled
	all s : Student | s->Grade in s.enrolled.(instanceGrades[this])
}
    S54 in valid iff {
	// Students only have grades in courses they are enrolled
	all s : Student | s->Grade = s.enrolled.(instanceGrades[this])
}
    S55 in valid iff {
	// Students only have grades in courses they are enrolled
	all s : Student | s->Grade not in (Course - s.enrolled).(instanceGrades[this])
}
    S56 in valid iff {
	// Students only have grades in courses they are enrolled
	all s : Student | (Course - s.enrolled).(instanceGrades[this]) not in s->Grade
}
    S57 in valid iff {
	// Students only have grades in courses they are enrolled -> ESTA MAL
  all s: Person, c: Course , g: Grade | s in enrolled.c implies s->g in c.(instanceGrades[this])
  
  all s: Person, c: Course , g: Grade | s in Student
}
    S58 in valid iff {
	// Students only have grades in courses they are enrolled -> ESTA MAL
  all s: Person, c: Course , g: Grade | s in enrolled.c implies s->g in c.(instanceGrades[this])
  
  all s: Person | s in Student
}
    S59 in valid iff {
	// Students only have grades in courses they are enrolled
  	all x: Student, g: Grade | x in Course.(instanceGrades[this]).g implies (some c: Course | x in enrolled.c and x in c.(instanceGrades[this]).g)
	all x: Student, g1, g2: Grade, c: Course | x in c.(instanceGrades[this]).g1 and x in c.(instanceGrades[this]).g2 implies g1 = g2
}
    S60 in valid iff {
	// Students only have grades in courses they are enrolled
	all c : Course | some s : Student | s in c.~enrolled and 
  		c.(instanceGrades[this])[s] in  Grade
}
    S61 in valid iff {
	// Students only have grades in courses they are enrolled
	//no c : Course | some s : Student | s not in c.~enrolled and 
  		//c.grades[s] in  Grade
  all c: Course, p: Person |
        p -> Grade in c.(instanceGrades[this]) implies p in c.enrolled
}
    S62 in valid iff {
	// Students only have grades in courses they are enrolled
	Course.(instanceGrades[this]) & Professor->Grade = none->none 
}
    S63 in valid iff {
	// Students only have grades in courses they are enrolled
  all s: Student, c: Course, g: Grade | c in s.enrolled implies c.(instanceGrades[this]).g in enrolled.c

}
    S64 in valid iff {
	// Students only have grades in courses they are enrolled
	all s: Student, c: Course, g:Grade | c->s->g in (instanceGrades[this])
}
    S65 in valid iff {
	// Students only have grades in courses they are enrolled
	Student -> Grade in Course.(instanceGrades[this])
}
    S66 in valid iff {
	// Students only have grades in courses they are enrolled
	Student -> Grade in Student.enrolled.(instanceGrades[this])
}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66 extends Formula {}

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
    #valid.Oracle = 2
    #(Instance - valid.Oracle) = 2
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 16 Atom, exactly 4 PersonAtom, exactly 4 CourseAtom, exactly 4 ProjectAtom, exactly 4 GradeAtom,
       exactly 4 Instance, 8 Int
