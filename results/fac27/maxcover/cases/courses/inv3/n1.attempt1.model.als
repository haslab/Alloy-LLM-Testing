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
    Oracle in valid iff {
	// Courses must have teachers
    all c: Course | some teaches.c
}
    S1 in valid iff {
	// Courses must have teachers
    some teaches.Course
}
    S2 in valid iff {
	// Courses must have teachers

}
    S3 in valid iff {
	// Courses must have teachers
  no teaches.Course

}
    S4 in valid iff {
	// Courses must have teachers
	//all c: Course | some teaches.c
  	one teaches.Course
}
    S5 in valid iff {
	// Courses must have teachers
  all c: Course | one teaches.c

}
    S6 in valid iff {
	// Courses must have teachers
  some Course.teaches 
}
    S7 in valid iff {
	// Courses must have teachers
  all c: Course | c.(instanceGrades[this]) = Professor -> Grade
}
    S8 in valid iff {
	// Courses must have teachers
	all c: Course | c.(instanceGrades[this])[Person] = Professor
}
    S9 in valid iff {
	// Courses must have teachers
  all c: Course | #(c.(instanceGrades[this])[Person]) >= 1
}
    S10 in valid iff {
	// Courses must have teachers
  	all c : Course , p : Professor | c in p 
}
    S11 in valid iff {
	// Courses must have teachers
	all c : Course | (some p : Person | p.teaches = c)
}
    S12 in valid iff {
	// Courses must have teachers
//	all c : Course | (some p : Person | p.teaches = c)
	all c : Course | some c.teaches
}
    S13 in valid iff {
	// Courses must have teachers
	all c : Course | some p : Professor | p.teaches in c
}
    S14 in valid iff {
	// Courses must have teachers
	some p : Professor | p.teaches in Course
}
    S15 in valid iff {
	// Courses must have teachers
	all c:Course , p:Professor |
  		c in p.teaches
}
    S16 in valid iff {
	// Courses must have teachers
	all c: Course | some p: Person | (p.teaches = c) implies (p in Professor)
}
    S17 in valid iff {
	// Courses must have teachers
  all c : Course | some p : Professor | p in teaches.c
  all c : Course | some p : Professor | p.teaches in c
  

}
    S18 in valid iff {
	// Courses must have teachers
  all c:Course | some p:Person | p.teaches in c

}
    S19 in valid iff {
	// Courses must have teachers
	all c : Course | some p : Person | some p.teaches

}
    S20 in valid iff {
	// Courses must have teachers
  	all p: Professor | some p.teaches

}
    S21 in valid iff {
	// Courses must have teachers
  	all c : Course | (all p : Professor | p.teaches in c)

}
    S22 in valid iff {
	// Courses must have teachers
	all c : Course | some t : (Person - Student) | c in t.teaches
}
    S23 in valid iff {
	// Courses must have teachers
	all c : Course | all t : (Person - Student) | c in t.teaches
}
    S24 in valid iff {
	// Courses must have teachers
	all c : Course | all p : Person | c in p.teaches
}
    S25 in valid iff {
	// Courses must have teachers
	some p : Professor  | p in enrolled.Course
}
    S26 in valid iff {
	// Courses must have teachers
  	all c : Course | (one p : Professor | p.teaches in c)

}
    S27 in valid iff {
	// Courses must have teachers
  all p : Person | some p.teaches

}
    S28 in valid iff {
	// Courses must have teachers
  	all p : Person, c : Course | c in Professor

}
    S29 in valid iff {
	// Courses must have teachers
  	some p : Professor | all c : Course | c in p.teaches

}
    S30 in valid iff {
	// Courses must have teachers
	all c: Course | some p: Person | p in Professor => c in p.teaches
}
    S31 in valid iff {
	// Courses must have teachers
	all c: Course | one p: Person | p in Professor => c in p.teaches
}
    S32 in valid iff {
	
	all c : Course | some p : Student | p->c in teaches

}
    S33 in valid iff {
	// Courses must have teachers
  all c : Course | all p : c.courseProjects | p.teaches != none

}
    S34 in valid iff {
	// Courses must have teachers
  	 some p: Professor| all c: Course | c -> p in teaches

}
    S35 in valid iff {
	// Courses must have teachers
	all c : Course | some Professor -> c
  
	//teaches in Person ... -> Course
  
}
    S36 in valid iff {
	// Courses must have teachers
	all x: Course, y: Person-Student | lone(y.teaches)
}
    S37 in valid iff {
	// Courses must have teachers
	Person-Student in Course.teaches
}
    S38 in valid iff {
	// Courses must have teachers
	//all c: Course, p: Person | c in p.teaches 
	all c: Course, p: Person | one c implies p in Professor
	//all c: Course, p: Person | p.teaches implies c 
  
	//all c: Course, p: Person | iff p in c.teaches then p in Professor
  
}
    S39 in valid iff {
	// Courses must have teachers
	all x : Course , y : Person - Professor | some(teaches.x)
}
    S40 in valid iff {
	// Courses must have teachers
	all x: Person-Student, y: Course | no(x.teaches)
}
    S41 in valid iff {
	// Courses must have teachers
	all c : Course | lone teaches.c
  
}
    S42 in valid iff {
	// Courses must have teachers
  all x : Course | all y : Person - Student | some(teaches.x)

}
    S43 in valid iff {
	// Courses must have teachers
  all x : Course | all y : Person - Student | some(x.teaches)

}
    S44 in valid iff {
	// Courses must have teachers
  	lone p : Professor | lone t : p.teaches | t in Course

}
    S45 in valid iff {
	// Courses must have teachers
  	all p : Person | lone t : p.teaches | t in Course

}
    S46 in valid iff {
	//// Courses must have teachers
	 all p : Person, c: Course | one teaches.c implies one p.teaches
}
    S47 in valid iff {
	// Courses must have teachers
	all c: Course | some enrolled.c
}
    S48 in valid iff {
	// Courses must have teachers
  all p : Professor | one c: Course | c in p.teaches

}
    S49 in valid iff {
	// Courses must have teachers
  all p : Person-Student | one c: Course | c in p.teaches

}
    S50 in valid iff {
	// Courses must have teachers
  all p : Person-Student | some c: Course | c in p.teaches

}
    S51 in valid iff {
	// Courses must have teachers
	some p : Person | all c : Course | c in p.teaches
}
    S52 in valid iff {
	// Courses must have teachers
  all c: Course | some p: Person | p in teaches.c
  
  all c: Course, p: Professor | p in teaches.c
}
    S53 in valid iff {
	// Courses must have teachers
	// all t: Professor | some (t.teaches)
	all p: Project | some (p & (Course + Professor))
}
    S54 in valid iff {
	// Courses must have teachers
	// all t: Professor | some (t.teaches)
	all p: Project | some (Course + Professor)
}
    S55 in valid iff {
	// Courses must have teachers
	all c: Course | all p: Professor | c in p.teaches and c not in p.enrolled 
}
    S56 in valid iff {
	// Courses must have teachers
	all c: Course | one p: Professor | p.teaches = c
}
    S57 in valid iff {
	// Courses must have teachers
  	all c: Course | some teaches.c
  	some teaches.Course
}
    S58 in valid iff {
	// Courses must have teachers
  	all p: Person, c: Course | p.teaches in c iff p in Professor
}
    S59 in valid iff {
	// Courses must have teachers
  	//all c: Course | some teaches.c 
  all c: Course| lone p: Person | p.teaches in c
}
    S60 in valid iff {
	// Courses must have teachers
  	//all c: Course | some teaches.c 
  all c: Course| some p: Person | teaches.c in p
}
    S61 in valid iff {
	// Courses must have teachers
	all c: Course | lone p: Person | p in Professor implies c in p.teaches 
}
    S62 in valid iff {
	// Courses must have teachers
	//all p: Person, c: Course | p in teaches.c implies p in Professor  
	all p: Person, c:Course | some teaches.c implies p in Professor
  
}
    S63 in valid iff {
	// Courses must have teachers
	all p: Person, c: Course | (p not in teaches.c) iff (p in Professor)
}
    S64 in valid iff {
	// Courses must have teachers
	all p: Person, c:Course| p in teaches.c implies p in Professor
	some p: Person | p->Course in teaches implies some p.teaches
}
    S65 in valid iff {
	// Courses must have teachers
	some p: Person|all c: Course| c in p.teaches implies p in Professor}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65 extends Formula {}

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
