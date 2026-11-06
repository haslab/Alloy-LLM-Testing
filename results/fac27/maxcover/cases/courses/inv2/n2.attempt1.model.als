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
    Oracle in valid iff {
	// Only professors can teach courses
    all p : Person | some p.teaches implies p in Professor
}
    S1 in valid iff {
	// Only professors can teach courses

}
    S2 in valid iff {
	// Only professors can teach courses
	all s: Student | (no s.teaches)
}
    S3 in valid iff {
	// Only professors can teach courses
	all c: Course | Student not in teaches.c
}
    S4 in valid iff {
	// Only professors can teach courses
	all p : Person | some p.teaches implies p in Student
}
    S5 in valid iff {
	// Only professors can teach courses
	all p : Person | some c : Course | p.teaches in c implies p in Professor
}
    S6 in valid iff {
	// Only professors can teach courses
  all p : Person | some c: Course| c in p.teaches implies p in Professor
}
    S7 in valid iff {
	// Only professors can teach courses
	all p : Person | (some p.enrolled) implies p in Professor
}
    S8 in valid iff {
	// Only professors can teach courses
  all p: Person | p.teaches in Professor
}
    S9 in valid iff {
	// Only professors can teach courses
  	all p: Person| (p in Professor) iff (p.teaches!= none)

}
    S10 in valid iff {
	// Only professors can teach courses
  	all p: Person-Professor | p.teaches not in Course
}
    S11 in valid iff {
	// Only professors can teach courses
  all p:Person |
  	some t:p.teaches |
  		t in Course implies p in Professor

}
    S12 in valid iff {
	// Only professors can teach courses
  	all p: Person-Professor | some c: Course | c not in p.teaches
}
    S13 in valid iff {
	// Only professors can teach courses
	no (Student-Professor).teaches
}
    S14 in valid iff {
	// Only professors can teach courses
	all p :Person|all c:Course|p.teaches in c implies p in Professor
}
    S15 in valid iff {
	// Only professors can teach courses
	all p :Person|(all c:Course|p.teaches in c) implies p in Professor
}
    S16 in valid iff {
	// Only professors can teach courses
  	all p: Person | p in Professor implies (some p.teaches)

}
    S17 in valid iff {
	// Only professors can teach courses
  all p : Person | some c: Course| c not in p.teaches implies p not in Professor
}
    S18 in valid iff {
	// Only professors can teach courses
  all p : Person | some c: Course| p not in Professor implies c not in c.teaches
}
    S19 in valid iff {
	// Only professors can teach courses
  all p : Person | some c: Course| p not in Professor implies (p.teaches = none)
}
    S20 in valid iff {
	// Only professors can teach courses
   no p: Person | p in Student and p in Professor
 

}
    S21 in valid iff {
	// Only professors can teach courses
	
	// all p : Person | (some p.teaches) implies p in Professor

       Professor in Course.teaches
}
    S22 in valid iff {
	// Only professors can teach courses
	all p : Person | no p.enrolled implies p in Professor
}
    S23 in valid iff {
	// Only professors can teach courses
  all teachers : Person.teaches | Student not in teachers

}
    S24 in valid iff {
	// Only professors can teach courses
	all p : Professor | p not in Student implies p.teaches != none
  	all pe: Person | pe not in Student implies pe.teaches != none
}
    S25 in valid iff {
	// Only professors can teach courses
	//teaches in Professor -> Course
  	all p : Person - Professor | some p.teaches
 
}
    S26 in valid iff {
	// Only professors can teach courses
  	all p: Person | one  Professor implies (some p.teaches)

}
    S27 in valid iff {
	// Only professors can teach courses
    all c : Course | c in  Professor.teaches 
   // teaches in Professor -> Course
  	

}
    S28 in valid iff {
	// Only professors can teach courses
	Person -> Person.teaches in Professor -> Course
}
    S29 in valid iff {
	// Only professors can teach courses
  	all disj p, p1: Person| (p in Professor) iff (p.teaches!= none) and (p1 not in Professor) iff (p1.teaches!=none)

}
    S30 in valid iff {
	// Only professors can teach courses
	all p : Professor | p not in Student implies p.teaches != none
  	all pe: Person | pe in Student implies pe.teaches = none
}
    S31 in valid iff {
	// Only professors can teach courses
	all p : Professor | p not in Student implies p.teaches != none
  	all pe: Person | pe.teaches = none
}
    S32 in valid iff {
	// Only professors can teach courses
	all p : Professor | p not in Student implies p.teaches != none
	all s : Student | s not in Person implies s.teaches = none
}
    S33 in valid iff {
	// Only professors can teach courses
  all p : Person | some p.teaches implies Professor in p

}
    S34 in valid iff {
	// Only professors can teach courses
	all p: Person, c: Course | c in p.teaches iff p in Professor
}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34 extends Formula {}

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
