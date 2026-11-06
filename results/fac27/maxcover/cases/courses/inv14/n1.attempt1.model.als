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
    // Earlier requirement 11, required in every Instance.
{
	// Students have at most one grade per course
	all s : Student, c : Course | lone c.(instanceGrades[this])[s] 
}
    // Earlier requirement 12, required in every Instance.
{
	// A student with the highest mark in a course must have worked on a project on that course
	all c : Course, p : Person | (order_last[this]) in p.(c.(instanceGrades[this])) implies some p.personProjects & c.courseProjects
}
    Oracle in valid iff {
	// A student cannot work with the same student in different projects
	all disj a, b : Student | lone a.personProjects & b.personProjects
}
    S1 in valid iff {
	// A student cannot work with the same student in different projects

}
    S2 in valid iff {
	// A student cannot work with the same student in different projects
	all disj s1: Student, s2: Student | all disj p1: Project, p2: Project | ((p1 in s1.personProjects) && (p1 in s2.personProjects)) implies !( (p2 in s1.personProjects) && (p2 in s2.personProjects) )
}
    S3 in valid iff {
	// A student cannot work with the same student in different projects

	// all s1 : Student | all s2 : Student | all p1 : Project | all p2 : Project |  
	// s1->p1 in projects and s2->p1 in projects and 
        // s1->p2 in projects implies not s2->p2 in projects

	all s1 : Student | all s2 : Student | lone (s1.personProjects & s2.personProjects)

}
    S4 in valid iff {
	// A student cannot work with the same student in different projects
  all s1, s2 : Student | all p1, p2 : Project | p1 in s1.personProjects and p2 in s1.personProjects and p1 in s2.personProjects and s1 != s2 implies p2 not in s2.personProjects
  

}
    S5 in valid iff {
	// A student cannot work with the same student in different projects
  	all disj s1,s2 : Student | lone(s1.personProjects & s1.personProjects)

}
    S6 in valid iff {
	// A student cannot work with the same student in different projects
	all s1,s2 : Student | lone p1 : s1.personProjects | s1 != s2 and p1 not in s2.personProjects
}
    S7 in valid iff {
	// A student cannot work with the same student in different projects
	all s : Student | all s1 : Student | one (s.personProjects & s1.personProjects)
}
    S8 in valid iff {
	// A student cannot work with the same student in different projects
	all s1, s2: Student | s1 != s2 implies no p1, p2: s1.personProjects | p1 != p2 and p2 in s2.personProjects
}
    S9 in valid iff {
	// A student cannot work with the same student in different projects
  	all s1,s2 : Student | s1 != s2 implies one (s1.personProjects & s2.personProjects)

}
    S10 in valid iff {
  all disj s, s1 : Student | all disj p , p1 : Project | (p in s.personProjects and p in s1.personProjects) implies ( p1 in s.personProjects and p1 not in s1.personProjects) 
	// A student cannot work with the same student in different projects

}
    S11 in valid iff {
	// A student cannot work with the same student in different projects
    
    all disj c1,c2:Course | no (c1.(instanceGrades[this]) & c2.(instanceGrades[this]))
}
    S12 in valid iff {
	// A student cannot work with the same student in different projects
	all s : Student | one s.personProjects & s.^(personProjects)
}
    S13 in valid iff {
	// A student cannot work with the same student in different projects
  	all s1,s2 :Student | all p1:s1.personProjects | all p2:s2.personProjects | p1 = p2 and s1 != s2 implies s1.personProjects-p1 not in s2.personProjects -p1
}
    S14 in valid iff {
	// A student cannot work with the same student in different projects
	all s1:Student, s2:Student| s1!=s2 and lone(s1.personProjects & s2.personProjects)
}
    S15 in valid iff {
	// A student cannot work with the same student in different projects
  all s: Person, p: s.personProjects | one (Person-s).personProjects & p 

}
    S16 in valid iff {
	// A student cannot work with the same student in different projects
  all s: Person | one (Person-s).personProjects & s.personProjects 

}
    S17 in valid iff {
	// A student cannot work with the same student in different projects
  all s: Person | lone (Person-s).personProjects & s.personProjects 

}
    S18 in valid iff {
	// A student cannot work with the same student in different projects
	all disj s1, s2: Student | lone s1.personProjects.~(Course <: courseProjects) & s2.personProjects.~(Course <: courseProjects)
}
    S19 in valid iff {
	// A student cannot work with the same student in different projects
	all s1, s2 : Student | 
    some p1 : Project | (p1 in s1.personProjects and p1 in s2.personProjects)
    implies no p2 : Project | 
    p2 != p1 and (p2 in s1.personProjects and p2 in s2.personProjects)
}
    S20 in valid iff {
  all s: Student, s2: Student, c: Course| no(s.personProjects & s2.personProjects) and s != s2
	// A student cannot work with the same student in different projects

}
    S21 in valid iff {
  all p: Person, p2: Person| no(p.personProjects & p2.personProjects) implies (p & p2) in Student
	// A student cannot work with the same student in different projects

}
    S22 in valid iff {
  all p: Person, p2: Person| no(p.personProjects & p2.personProjects) and (p & p2) in Student
	// A student cannot work with the same student in different projects

}
    S23 in valid iff {
	// A student cannot work with the same student in different projects
	all disj s1,s2:Student | one p:Project |
  		p in s1.personProjects and p in s2.personProjects implies (all p2:Project | p2 in s1.personProjects implies not p2 in s2.personProjects)
}
    S24 in valid iff {
	// A student cannot work with the same student in different projects
	all disj s1,s2:Student | lone p:Project |
  		p in s1.personProjects and p in s2.personProjects implies (all p2:Project | p2 in s1.personProjects implies not p2 in s2.personProjects)
}
    S25 in valid iff {
	// A student cannot work with the same student in different projects
	all s1: Student | some s2: Student | lone (s1 & s2).personProjects
}
    S26 in valid iff {
	// A student cannot work with the same student in different projects
	some s1: Student | some s2: Student | lone (s1 & s2).personProjects
}
    S27 in valid iff {
	// A student cannot work with the same student in different projects
	all s1, s2: Student | one (s1 & s2).personProjects
}
    S28 in valid iff {
	// A student cannot work with the same student in different projects
  	all s1, s2: Student, p1, p2: Project | (p1 in (s1.enrolled).courseProjects and p1 in (s2.enrolled).courseProjects and p2 in (s1.enrolled).courseProjects and p2 in (s2.enrolled).courseProjects) implies p1=p2
}
    S29 in valid iff {
	// A student cannot work with the same student in different projects
	all disj s1, s2: Student | #(s1.personProjects & s2.personProjects) > 2
}
    S30 in valid iff {
	// A student cannot work with the same student in different projects
	all disj s1,s2:Student | one p1:Project | all p2:Project | p1 in s1.personProjects and p2 in s2.personProjects and p2 in s1.personProjects implies p2 not in s2.personProjects
}
    S31 in valid iff {
	// A student cannot work with the same student in different projects
	all disj s1,s2:Student | one p1:Project | all p2:Project | p1 != p2 and p1 in s1.personProjects and p2 in s2.personProjects and p2 in s1.personProjects implies p2 not in s2.personProjects
}
    S32 in valid iff {
	// A student cannot work with the same student in different projects
	all disj s1,s2:Student | one p1:Project | all p2:Project | p1 != p2 and p1 in s1.personProjects and p1 in s2.personProjects and p2 in s1.personProjects implies p2 not in s2.personProjects
}
    S33 in valid iff {
	// A student cannot work with the same student in different projects
	all disj s1, s2: Student | some p:s1.personProjects | p not in s2.personProjects
}
    S34 in valid iff {
  all disj s, s1 : Student | all  p : Project | (p in s.personProjects and p in s1.personProjects) implies no p1 : Project | p != p1 and p1 in s.personProjects and p1 not in s1.personProjects
	// A student cannot work with the same student in different projects

}
    S35 in valid iff {
	// A student cannot work with the same student in different projects
	all disj s, t : Student | lone (s.enrolled & t.enrolled)
}
    S36 in valid iff {
	// A student cannot work with the same student in different projects
	all s1,s2 : Student | all p : s1.personProjects | lone pro : Project | p in s2.personProjects implies pro in s1.personProjects and pro in s2.personProjects
}
    S37 in valid iff {
	// A student cannot work with the same student in different projects
	all disj s1, s2: Student, p1, p2: Project | p1 in s1.personProjects and p2 in s2.personProjects => p1 = p2 
}
    S38 in valid iff {
	// A student cannot work with the same student in different projects
	all disj s1, s2: Student, p1, p2: Project |
  		some p: s1.personProjects | p in s2.personProjects implies s1.personProjects - p != s2.personProjects - p
}
    S39 in valid iff {
	// A student cannot work with the same student in different projects
	all s1,s2 : Student | some p1,p2 : s1.personProjects | p1 in s2.personProjects and p2 in s2.personProjects implies p1 = p2
  
}
    S40 in valid iff {
	// A student cannot work with the same student in different projects
  all s1, s2 : Student | some p : Project | p in (s1.personProjects & s2.personProjects) implies p not in (s1.personProjects & s2.personProjects) - p
}
    S41 in valid iff {
	// A student cannot work with the same student in different projects
  	all s1, s2: Student, c1, c2: Course, p1, p2: Project | s1 in enrolled.c1 and s2 in enrolled.c1 and s1 in enrolled.c2 and s2 in enrolled.c2 and p1 in c1.courseProjects and p2 in c2.courseProjects and p1 in s1.personProjects and p2 in s2.personProjects implies c1 = c2 and p1 = p2

}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41 extends Formula {}

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
