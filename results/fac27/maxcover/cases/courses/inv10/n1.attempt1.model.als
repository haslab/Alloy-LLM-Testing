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
    Oracle in valid iff {
	// Only students have grades
	Course.(instanceGrades[this]).Grade in Student
}
    S1 in valid iff {
	// Only students have grades
	//no grades[Professor]
}
    S2 in valid iff {
	// Only students have grades
	no Professor & Course.(instanceGrades[this]).Grade  
}
    S3 in valid iff {
	// Only students have grades
	all c : Course | all p : Person.(c.(instanceGrades[this])) | p in Student
}
    S4 in valid iff {
	// Only students have grades
	all p: Person | all c: Course | lone c.(instanceGrades[this])[p]
}
    S5 in valid iff {
	// Only students have grades
	all p: Person | all c: Course | all x: c.(instanceGrades[this])[p] | p not in Student
}
    S6 in valid iff {
	// Only students have grades
	//all g: Grade | all c: Course | (c[g]) -> Person not in Student
  	all p: Person | all c: Course | some c.(instanceGrades[this])[p]
}
    S7 in valid iff {
	// Only students have grades
	all g:Grade | all p:Person | some ((instanceGrades[this]).(g->p)) implies p in Student
}
    S8 in valid iff {
	// Only students have grades
	all p : Person - Student | #p.enrolled.(instanceGrades[this]) = 0 and 
  	no #p.enrolled.(instanceGrades[this])[p]
}
    S9 in valid iff {
	// Only students have grades
	all p : Person, c : Course | some g : Grade | (instanceGrades[this])[p,g] in Student and (instanceGrades[this])[p,g] not in Professor
}
    S10 in valid iff {
	// Only students have grades
	all p : Person, c : Course, g : Grade | p.(c.(instanceGrades[this])) in g implies p in Student and p not in Professor
}
    S11 in valid iff {
	// Only students have grades
	all p : Person, c : Course | some g : Grade | p.(c.(instanceGrades[this])) in g implies p in Student and p not in Professor
}
    S12 in valid iff {
	// Only students have grades
	all p : Person, c : Course | some g : Grade | p.(c.(instanceGrades[this])) in g implies p not in Professor
}
    S13 in valid iff {
	// Only students have grades
	all p : Person, c : Course | some g : Grade | p.(c.(instanceGrades[this])) in g implies c in p.enrolled and p not in Professor
}
    S14 in valid iff {
	// Only students have grades
	all c: Course, p: Person | c not in p.enrolled implies no p.(c.(instanceGrades[this]))
}
    S15 in valid iff {
	// Only students have grades
    all c : Course, s : Student | (s.enrolled.(instanceGrades[this]) in c.(instanceGrades[this]))

}
    S16 in valid iff {
	// Only students have grades
  	all p : Person | all g : Grade | p->g in Course.(instanceGrades[this]) => p in Student
  
  	some (instanceGrades[this]).(Person->Grade)
}
    S17 in valid iff {
	// Only students have grades
	all s:Student | all c:Course | all g:Grade | s in c.(instanceGrades[this]).g 
}
    S18 in valid iff {
	// Only students have grades
	all c : Course | some p : Person | some (c.(instanceGrades[this])[p]) => p in Student

}
    S19 in valid iff {
	// Only students have grades
  
  all c : Course, s: Student | some c.(instanceGrades[this]).Person & s 
}
    S20 in valid iff {
	// Only students have grades
    all p: Person | p in Professor or p in Student
    all s: Student | s.(instanceGrades[this]) = Course->Grade
    all p: Professor | no p.(instanceGrades[this])

}
    S21 in valid iff {
	// Only students have grades
	all p: Person |
		(p in Student) => (some c: Course | p in c.(instanceGrades[this]).Person)
}
    S22 in valid iff {
	// Only students have grades
	all p : Person, c : Course | 
		some g : Grade | (p -> g) in c.(instanceGrades[this]) implies p in Student
  		

}
    S23 in valid iff {
	// Only students have grades

  	// all s: Student | all g: Grade | g in s.enrolled.grades

	all c: Course, g: Grade | some p: Person | c.(instanceGrades[this])[p] = g implies p in Student
}
    S24 in valid iff {
	// Only students have grades
	all p : Person | some (p.enrolled.(instanceGrades[this]) + p.teaches.(instanceGrades[this])) => p in Student
}
    S25 in valid iff {
	// Only students have grades
   Professor not in Course.(instanceGrades[this]).Person

}
    S26 in valid iff {
	// Only students have grades
	all c: Course | all p : Person | c.(instanceGrades[this])[p] in Grade => p in Student
}
    S27 in valid iff {
  all s: Student, c: Course | some c.(instanceGrades[this])[s]
	// Only students have grades

}
    S28 in valid iff {
	// Only students have grades
	all pe : Person | (pe.teaches.(instanceGrades[this]).Grade = none) and (pe.enrolled.(instanceGrades[this]).Grade != none)
}
    S29 in valid iff {
	// Only students have grades
	//all p : Person | all c : p.enrolled | p in c.grades implies p in Student
  	all pr : Professor | all class : pr.enrolled+pr.teaches | no g : Grade | pr->g in class.(instanceGrades[this])
  
  	all p : Person  | all c : p.enrolled | some g : Grade | p->g in c.(instanceGrades[this]) implies p in Student
  	
}
    S30 in valid iff {
	// Only students have grades
	//all p : Person | all c : p.enrolled | p in c.grades implies p in Student
  	all pr : Professor | all class : pr.teaches | no g : Grade | pr->g in class.(instanceGrades[this])
  

  	
}
    S31 in valid iff {
	// Only students have grades
	//all p : Person | all c : p.enrolled | p in c.grades implies p in Student
  	all pr : Professor | all class : pr.enrolled | no g : Grade | pr->g in class.(instanceGrades[this])
  

  	
}
    S32 in valid iff {
	// Only students have grades
	all p:Student | some p.enrolled.(instanceGrades[this])
}
    S33 in valid iff {
	// Only students have grades
	all p:Student, c:Course, g:Grade | some c.(instanceGrades[this]).g
}
    S34 in valid iff {
	// Only students have grades
	all p : Person | all c : Course | one c.(instanceGrades[this])[p] => p in Student  

}
    S35 in valid iff {
	// Only students have grades

	all c: Course, g: Grade | some p: Person | g in c.(instanceGrades[this])[p] implies p in Student

}
    S36 in valid iff {
	// Only students have grades

	all c: Course, g: Grade | one p: Person | g in c.(instanceGrades[this])[p] implies p in Student

}
    S37 in valid iff {
	// Only students have grades
	Student & (Course.(instanceGrades[this])).Grade = Student
}
    S38 in valid iff {
	// Only students have grades
  all p: Person |
		(p in Student implies some c: p.enrolled | c.(instanceGrades[this])[p] in Grade) and
		(p in Professor implies no c: p.teaches | some pe: c.enrolled | c.(instanceGrades[this])[pe] in Grade)

  

}
    S39 in valid iff {
	// Only students have grades
  	/* Ternary relationships:
    	if
        x : Course
        y : Student
        z : Grade
        then,
        x.grades.z -> all students with grade z in course y 
        y.(x.grades) -> all grades of student y in course x
        (grades.z).y -> all courses where sutent y got grade z
        
        In all examples above you can use the signature's name instead of a variable (Course/Student/Grade) to get all entries of that type
    all p : Course.grades.Grade | p in Student
    */
  	all s : Student, g : Grade | some  c : Course |
		s in c.(instanceGrades[this]).g  
}
    S40 in valid iff {
	// Only students have grades
	all s : Person | all g : Grade|  s in Student and s->g in Course.(instanceGrades[this])
}
    S41 in valid iff {
	// Only students have grades
	some s : Person | all g : Grade|  s in Student and s->g in Course.(instanceGrades[this])
}
    S42 in valid iff {
	all p: Person | some c: Course | (p -> c) in c.(instanceGrades[this]) implies p in Student
}
    S43 in valid iff {
	// Only students have grades
	all s: Student, c: Course | some s.enrolled.(instanceGrades[this])

}
    S44 in valid iff {
	// Only students have grades
	all s: Student, c: Course | some c.(instanceGrades[this])

}
    S45 in valid iff {
	// Only students have grades
	all c : Course | c.(instanceGrades[this]).(order_first[this]) in Student
}
    S46 in valid iff {
    // Only students have grades
  all p: Professor | all c: Course | not (p->Grade) in c.(instanceGrades[this])

}
    S47 in valid iff {
	// Only students have grades
	all c: Course | all p: Professor-Student |some g:Grade| p->g not in c.(instanceGrades[this])
}
    S48 in valid iff {
	// Only students have grades
	all c: Course | all p: Professor-Student | all g:Grade| p->g not in c.(instanceGrades[this])
}
    S49 in valid iff {
	// Only students have grades
	all c: Course | all p: Professor-Student | lone g:Grade | p->g not in c.(instanceGrades[this])
}
    S50 in valid iff {
	// Only students have grades
	all c: Course | all p: Person-Professor | all g:Grade | p->g not in c.(instanceGrades[this])
}
    S51 in valid iff {
    // Only students have grades
  all s: Student | all c: Course | not (s->Grade) in c.(instanceGrades[this])

}
    S52 in valid iff {
    // Only students have grades
  all s: Person | all c: Course | not (s->Grade) in c.(instanceGrades[this])

}
    S53 in valid iff {
	// Only students have grades
  
 	all s : Student | all c : s.enrolled | some (instanceGrades[this]).c

}
    S54 in valid iff {
	// Only students have grades
all p:Person, g:Grade| (Course<:(instanceGrades[this])).g in enrolled implies p in Student}
    S55 in valid iff {
	// Only students have grades
	// all p: Person, c: Course, g: Grade | p->g in c.grades implies p in Student
  	all p: Person | p->Grade in Course.(instanceGrades[this]) implies p in Student
}
    S56 in valid iff {
	// Only students have grades
  all c: Course | (instanceGrades[this]) in c -> Student -> Grade

}
    S57 in valid iff {
	// Only students have grades
	all p : Person - Student | #p.enrolled.(instanceGrades[this]) = 0 and #p.teaches.(instanceGrades[this]) = 0
}
    S58 in valid iff {
	// Only students have grades
  all x : Person | some (x.enrolled.(instanceGrades[this])) 

}
    S59 in valid iff {
	// Only students have grades
	all c: Course, p: Person| some g:Grade |p->g in c.(instanceGrades[this]) => p in Student - Professor
}
    S60 in valid iff {
	// Only students have grades
	all c: Course, p: Person, g:Grade |p->g in c.(instanceGrades[this]) => p in Student - Professor
}
    S61 in valid iff {
	// Only students have grades
  all p: Person-Student | no c: Course | no g: Grade | g in c.(instanceGrades[this])[p]

}
    S62 in valid iff {
	// Only students have grades
  	all p: Person, g: Grade, pr: Project |
  		p->pr in personProjects implies (p in Student and some enrolled.(instanceGrades[this]))
  		

}
    S63 in valid iff {
	// Only students have grades
	all c : Course | some (c.(instanceGrades[this]).Grade & Student)
}
    S64 in valid iff {
	// Only students have grades
  all s: Student, c: Course , g: Grade | s in enrolled.c implies s->g in c.(instanceGrades[this])

}
    S65 in valid iff {
	// Only students have grades -> ESTA MAL
  all s: Student, c: Course , g: Grade | s in enrolled.c implies s->g in c.(instanceGrades[this])
  
  all c: Course, g: Grade, p: Person | p->g in c.(instanceGrades[this]) implies p in Student

}
    S66 in valid iff {
  // Only students have grades (appear in any course's grades)
  all p : Person | some c : Course, g : Grade | c->p->g in (instanceGrades[this]) implies p in Student
}
    S67 in valid iff {
	// Only students have grades
	all c : Course | all p : Person | p in c.(instanceGrades[this]).Grade implies p = Student
}
    S68 in valid iff {
	// Only students have grades
	all c : Course | all p : Person | (p not in Professor and p in c.(instanceGrades[this]).Grade ) implies p = Student
}
    S69 in valid iff {
	// Only students have grades
	all c : Course | all p : Person | (p in Professor and p in c.(instanceGrades[this]).Grade ) implies p = Student
}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69 extends Formula {}

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
