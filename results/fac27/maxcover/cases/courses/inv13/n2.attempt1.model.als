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
    Oracle in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c : Course, p : Person | (order_last[this]) in p.(c.(instanceGrades[this])) implies some p.personProjects & c.courseProjects
}
    S1 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course

}
    S2 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c : Course | let g = (c.(instanceGrades[this])), g2 = Person.g | g.((order_max[this, g2])) in (Person <: personProjects).(c.courseProjects)
}
    S3 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c : Course, g : (order_max[this, c.(instanceGrades[this])[Student]]), s : c.(instanceGrades[this]).g |some c.courseProjects implies some (s.personProjects & c.courseProjects)
}
    S4 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c: Course | some (order_max[this, Person.(c.(instanceGrades[this]))])
}
    S5 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c : Course | one p : c.(instanceGrades[this]).max | one s : Student | one g : Grade |
  	(c in s.enrolled and s->g in c.(instanceGrades[this]) and g=p) 
  
}
    S6 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
 
  all c:Course | c in Course:> courseProjects.(((c.(instanceGrades[this])).(order_last[this]))    .personProjects)

}
    S7 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
 
  some c:Course | c in Course:> courseProjects.(((c.(instanceGrades[this])).(order_last[this])).personProjects)

}
    S8 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  all s,s1:Student | all c:Course | (s!=s1 and (order_gt[this, c.(instanceGrades[this])[s], c.(instanceGrades[this])[s1]])) implies (some p:s.personProjects | p in c.courseProjects) 
  	

}
    S9 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course

	// all c : Course, p : Person | last in p.(c.grades) implies
	//   some pr :Project | p->pr in projects and c->pr in projects

	// all c : Course, p : Person | last in p.(c.grades) implies some p.projects & c.projects

    all s1: Student,c: Course | 
      (all s2:Student-s1 | (order_gt[this, s1.(c.(instanceGrades[this])), s2.(c.(instanceGrades[this]))]))
      implies some s1.personProjects & c.courseProjects

}
    S10 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  all c:Course | one s:Student | (all s1:Student  | s!=s1 implies (order_gt[this, s.(c.(instanceGrades[this])), s1.(c.(instanceGrades[this]))])) implies (some p:s.personProjects | p in c.courseProjects) 
  	

}
    S11 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  all c:Course | one s:Student | (all s1:Student  | s!=s1 and (order_gt[this, s.(c.(instanceGrades[this])), s1.(c.(instanceGrades[this]))])) implies (some p:s.personProjects | p in c.courseProjects) 
  	

}
    S12 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  all c:Course | some s:Student | (all s1:Student  | s!=s1 and (order_gt[this, s.(c.(instanceGrades[this])), s1.(c.(instanceGrades[this]))])) implies (some p:s.personProjects | p in c.courseProjects) 
  	

}
    S13 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  all c:Course | one s:Person | (all s1:Person  | s!=s1 implies (order_gt[this, s.(c.(instanceGrades[this])), s1.(c.(instanceGrades[this]))])) implies (some p:s.personProjects | p in c.courseProjects) 

}
    S14 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  all c:Course | lone s:Person | (all s1:Person  | s!=s1 implies (order_gt[this, s.(c.(instanceGrades[this])), s1.(c.(instanceGrades[this]))])) implies (some p:s.personProjects | p in c.courseProjects) 

}
    S15 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	all a : Student, c : Course | one b : Student | (order_gte[this, b.(c.(instanceGrades[this])), a.(c.(instanceGrades[this]))]) implies c.courseProjects in b.personProjects 

}
    S16 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	all a : Student, c : Course | one b : Student | (order_gte[this, b.(c.(instanceGrades[this])), a.(c.(instanceGrades[this]))]) implies b.personProjects in c.courseProjects 

}
    S17 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  all s:Person | one c:Course | (all s1:Person  | (order_gte[this, s.(c.(instanceGrades[this])), s1.(c.(instanceGrades[this]))])) implies (some p:s.personProjects | p in c.courseProjects) 

}
    S18 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	all a : Student, c : Course, p: Project | one b : Student | (order_gte[this, b.(c.(instanceGrades[this])), a.(c.(instanceGrades[this]))]) implies p in c.courseProjects&b.personProjects  

}
    S19 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	all a : Student, c : Course | one b : Student | (order_gte[this, b.(c.(instanceGrades[this])), a.(c.(instanceGrades[this]))]) implies some c.courseProjects&b.personProjects  

}
    S20 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	all a : Student, c : Course | one b : Student | (order_gt[this, b.(c.(instanceGrades[this])), a.(c.(instanceGrades[this]))]) implies some c.courseProjects&b.personProjects  

}
    S21 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  all c:Course | one s:Person | (all s1:Person  | (order_larger[this, s.(c.(instanceGrades[this])), s1.(c.(instanceGrades[this]))])=s.(c.(instanceGrades[this]))) implies (some p:s.personProjects | p in c.courseProjects) 
  	//all c : Course, p : Person | last in p.(c.grades) implies some p.projects & c.projects


}
    S22 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
   all  s : Student, c : Course | s.(c.(instanceGrades[this])) in (c.(instanceGrades[this]).(order_last[this])) =>  s.personProjects in c.courseProjects

}
    S23 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	all a : Student, c : Course | some b : Student | (order_gte[this, b.(c.(instanceGrades[this])), a.(c.(instanceGrades[this]))]) implies some c.courseProjects&b.personProjects  

}
    S24 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all s : Student, c : Course | (order_max[this, Grade]) in s.(c.(instanceGrades[this])) implies some p : Project | p in s.personProjects
}
    S25 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c: Course, s: Student | (order_last[this]) in s.(c.(instanceGrades[this])) implies s.personProjects in c.courseProjects
}
    S26 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c: Course, s: Student | (order_last[this]) in s.(c.(instanceGrades[this])) implies no (s.personProjects & c.courseProjects)
}
    S27 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
 
  all c:Course | c in Course:>  courseProjects.( ( (c.(instanceGrades[this])).((order_max[this, Person.(c.(instanceGrades[this]))])) ).personProjects)
  

}
    S28 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
 
  all c:Course | some(c.(instanceGrades[this])) implies some(c.courseProjects & ( ( (c.(instanceGrades[this])).((order_max[this, Person.(c.(instanceGrades[this]))])) ).personProjects))
  

}
    S29 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all s : Student | all c: Course | (s.(c.(instanceGrades[this])) in (order_last[this])) implies c in Person <: s.personProjects 
	

}
    S30 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all s: Student, c: Course | no c.(instanceGrades[this])[s].(order_next[this]) => some (s.personProjects & c.courseProjects)
}
    S31 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	all s : Student, c : Course, pr : c.courseProjects
		| (order_max[this, Grade]) in s.(c.(instanceGrades[this])) implies pr in s.personProjects
}
    S32 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	all s1,s2 : Student | some c : Course | (order_gt[this, s1.(c.(instanceGrades[this])), s2.(c.(instanceGrades[this]))]) implies s1.enrolled.courseProjects in c.courseProjects
	
}
    S33 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	all s1,s2 : Student | some c : Course | (order_gt[this, s1.(c.(instanceGrades[this])), s2.(c.(instanceGrades[this]))]) implies s2.enrolled.courseProjects in c.courseProjects
	
}
    S34 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	all s1,s2 : Student | some c : Course | (order_gt[this, s1.(c.(instanceGrades[this])), s2.(c.(instanceGrades[this]))]) implies one s1.enrolled.courseProjects
	
}
    S35 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	all s1,s2 : Student | some c : Course | (order_gt[this, s1.(c.(instanceGrades[this])), s2.(c.(instanceGrades[this]))]) implies lone s1.enrolled.courseProjects
	
}
    S36 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	all p1,p2 : Student | some c : Course | (order_gt[this, p1.(c.(instanceGrades[this])), p2.(c.(instanceGrades[this]))]) implies one p1.enrolled.courseProjects & c.courseProjects
	
}
    S37 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	all p1,p2 : Student | some c : Course | (order_gt[this, p1.(c.(instanceGrades[this])), p2.(c.(instanceGrades[this]))]) implies one p1.personProjects & c.courseProjects
	
}
    S38 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  //all c:Course | one s:Person | (all s1:Person  | last[s.(c.grades),s1.(c.grades)]=s.(c.grades)) implies (some p:s.projects | p in c.projects)
  all c : Course, p : Person | (order_first[this]) in p.(c.(instanceGrades[this])) implies some p.personProjects & c.courseProjects
  
  	

}
    S39 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	all p1,p2 : Student | some c : Course | (order_gte[this, p1.(c.(instanceGrades[this])), p2.(c.(instanceGrades[this]))]) implies one p1.personProjects & c.courseProjects
	
}
    S40 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c: Course | (order_max[this, Person.(c.(instanceGrades[this]))]).~(c.(instanceGrades[this])).personProjects in c.courseProjects
}
    S41 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	// all c: Course | (c.grades).(max[Person.(c.grades)]).projects in c.projects
	all c: Course | all s: Student | s.(c.(instanceGrades[this])) = (order_max[this, Person.(c.(instanceGrades[this]))]) => s.personProjects in c.courseProjects
}
    S42 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	// all c: Course | (c.grades).(max[Person.(c.grades)]).projects in c.projects
	all c: Course | all s: Student | s.(c.(instanceGrades[this])) = (order_max[this, Person.(c.(instanceGrades[this]))]) => c.courseProjects in s.personProjects
}
    S43 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	// all c: Course | (c.grades).(max[Person.(c.grades)]).projects in c.projects
	all c: Course | all s: Student | s.(c.(instanceGrades[this])) = (order_max[this, Person.(c.(instanceGrades[this]))]) => (c.courseProjects in s.personProjects and some c.courseProjects)
}
    S44 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	// all c: Course | (c.grades).(max[Person.(c.grades)]).projects in c.projects
	all c: Course | all s: Student | (some s.(c.(instanceGrades[this])) and s.(c.(instanceGrades[this])) = (order_max[this, Person.(c.(instanceGrades[this]))])) => (c.courseProjects in s.personProjects and some c.courseProjects)
}
    S45 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	// all c: Course | (c.grades).(max[Person.(c.grades)]).projects in c.projects
	// all c: Course | all s: Student | (some s.(c.grades) and s.(c.grades) = max[Person.(c.grades)]) => (c.projects in s.projects and some c.projects)
	all c: Course | all s: Student | (some s.(c.(instanceGrades[this])) and s.(c.(instanceGrades[this])) = (order_last[this])) => (c.courseProjects in s.personProjects and some c.courseProjects)
}
    S46 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  all c:Course | all s : enrolled.c | no ((s <: c.(instanceGrades[this])).(order_prev[this])) implies some (s.personProjects & c.courseProjects)
}
    S47 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  one a : Person | all b : Person, c : Course | (order_gt[this, a.(c.(instanceGrades[this])), b.(c.(instanceGrades[this]))]) implies a.personProjects in c.courseProjects

}
    S48 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  one a : Person | all b : Person, c : Course | (order_gt[this, a.(c.(instanceGrades[this])), b.(c.(instanceGrades[this]))]) implies one p : Project | p in c.courseProjects and p in a.personProjects

}
    S49 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  all a,b : Person, c : Course | (order_gt[this, a.(c.(instanceGrades[this])), b.(c.(instanceGrades[this]))]) implies c.courseProjects in a.personProjects
}
    S50 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  all a,b : Person, c : Course | (order_gt[this, a.(c.(instanceGrades[this])), b.(c.(instanceGrades[this]))]) implies a.personProjects in c.courseProjects
  
}
    S51 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  all a,b : Student, c : Course | (order_gt[this, a.(c.(instanceGrades[this])), b.(c.(instanceGrades[this]))]) implies some a.personProjects&c.courseProjects
  
}
    S52 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  one a : Student | all b : Student, c : Course | (order_gt[this, a.(c.(instanceGrades[this])), b.(c.(instanceGrades[this]))]) implies one a.personProjects&c.courseProjects
  
}
    S53 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  one a : Student | all b : Student-a, c : Course | (order_gt[this, a.(c.(instanceGrades[this])), b.(c.(instanceGrades[this]))]) implies one a.personProjects&c.courseProjects
  
}
    S54 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  all c:Course | some s : enrolled.c | no ((s <: c.(instanceGrades[this])).(order_prev[this])) implies some (s.personProjects & c.courseProjects)
}
    S55 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  all c:Course | no s : enrolled.c | no ((s <: c.(instanceGrades[this])).(order_prev[this])) and some (s.personProjects & c.courseProjects)
}
    S56 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
		let highest = {c: Course, s: c.~enrolled | no c.(instanceGrades[this])[s].(order_next[this])} |
			all c: Course | all s: c.highest |
				s in c.courseProjects.~personProjects
}
    S57 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all s1, s2: Student, c: Course | no g2: c.(instanceGrades[this])[s2] | g2 in c.(instanceGrades[this])[s1].(order_next[this]) => some (s1.personProjects & c.courseProjects)
}
    S58 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c: Course, s: Student |
  		s.(c.(instanceGrades[this])) = (order_max[this, Student.(c.(instanceGrades[this]))])
}
    S59 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c: Course, s: Student |
  		s.(c.(instanceGrades[this])) = (order_max[this, Student.(c.(instanceGrades[this]))]) => some (c.courseProjects & s.personProjects)
}
    S60 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c: Course |
  		let bestGrade = (order_max[this, (c.(instanceGrades[this]))[Student]]), bestStudent = c.(instanceGrades[this]).bestGrade |
  		c.courseProjects in bestStudent.personProjects
}
    S61 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c: Course |
  		let bestGrade = (order_max[this, (c.(instanceGrades[this]))[Student]]), bestStudent = c.(instanceGrades[this]).bestGrade |
  		lone c.courseProjects & bestStudent.personProjects
}
    S62 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c: Course |
  		let bestGrade = (order_max[this, (c.(instanceGrades[this]))[Student]]), bestStudent = c.(instanceGrades[this]).bestGrade |
  		one c.courseProjects & bestStudent.personProjects
}
    S63 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c: Course |
  		let bestGrade = (order_max[this, (c.(instanceGrades[this]))[Student]]), bestStudent = c.(instanceGrades[this]).bestGrade |
  		one bestStudent and some c.courseProjects & bestStudent.personProjects
}
    S64 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c: Course |
  		let bestGrade = (order_max[this, (c.(instanceGrades[this]))[Student]]), bestStudent = c.(instanceGrades[this]).bestGrade |
  		lone bestStudent => some c.courseProjects & bestStudent.personProjects
}
    S65 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c: Course |
  		let bestGrade = (order_max[this, (c.(instanceGrades[this]))[Student]]), bestStudent = c.(instanceGrades[this]).bestGrade |
  		one bestStudent => some c.courseProjects & bestStudent.personProjects
}
    S66 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c : Course | some student : Student | (order_max[this, student.(c.(instanceGrades[this]))]) = (order_max[this, Person.(c.(instanceGrades[this]))]) => student in (Person<:personProjects).c.(Course<:courseProjects)
}
    S67 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c : Course | some student : Student | (order_max[this, student.(c.(instanceGrades[this]))]) = (order_max[this, Person.(c.(instanceGrades[this]))]) => student in (Person<:personProjects).(c.(Course<:courseProjects))
}
    S68 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c : Course | some student : Student | c in student.enrolled and (order_max[this, student.(c.(instanceGrades[this]))]) = (order_max[this, Person.(c.(instanceGrades[this]))]) => student in (Person<:personProjects).(c.(Course<:courseProjects))
}
    S69 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c : Course | some student : Student | c in student.enrolled and some c.(instanceGrades[this]) and (order_max[this, student.(c.(instanceGrades[this]))]) = (order_max[this, Person.(c.(instanceGrades[this]))]) => student in (Person<:personProjects).(c.(Course<:courseProjects))
}
    S70 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c: Course | no( ((c.(instanceGrades[this])).((order_max[this, Student.(c.(instanceGrades[this]))]))).personProjects & c.courseProjects ) 
}
    S71 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	all s : Student, c : Course | c.(instanceGrades[this])[s] = c.(instanceGrades[this]).(order_last[this]) implies some s.enrolled.courseProjects

}
    S72 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	all s : Student, c : Course | c.(instanceGrades[this])[s] = (order_last[this]) implies some s.enrolled.courseProjects

}
    S73 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c : Course | one p : (order_max[this, Grade])[c.(instanceGrades[this])] | one s : Student | one g : Grade |
  	c in s.enrolled and s->g in c.(instanceGrades[this])
  
}
    S74 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c : Course | one p : (order_max[this, Grade])[c.(instanceGrades[this])] | some proj : p.personProjects | proj in c.courseProjects
  
}
    S75 in valid iff { 
  all p : Student | all c : Course | c in p.enrolled and p.(c.(instanceGrades[this])) = (order_max[this, Person.(c.(instanceGrades[this]))]) implies some (p.personProjects & c.courseProjects) }
    S76 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c:Course|all s:Student | (order_last[this]) in s.(c.(instanceGrades[this])) implies s.enrolled in c
}
    S77 in valid iff { 
  all c : Course | all p : Student | p.enrolled in c and p.(c.(instanceGrades[this])) = (order_max[this, Person.(c.(instanceGrades[this]))]) implies some (p.personProjects & c.courseProjects) }
    S78 in valid iff { 
  all c : Course | all s : enrolled.c | s.(c.(instanceGrades[this])) = (order_max[this, Person.(c.(instanceGrades[this]))]) and some c.courseProjects implies some (s.personProjects & c.courseProjects) }
    S79 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  all c : Course | some s: Person | (s.(c.(instanceGrades[this])) = (order_max[this, Person.(c.(instanceGrades[this]))]) ) implies s in personProjects.(c.courseProjects)

}
    S80 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  all c : Course | some s: enrolled.c | (s.(c.(instanceGrades[this])) = (order_max[this, Person.(c.(instanceGrades[this]))]) ) implies s in personProjects.(c.courseProjects)

}
    S81 in valid iff { 
  all c : Course | all s : enrolled.c - Professor | s.(c.(instanceGrades[this])) = (order_max[this, Student.(c.(instanceGrades[this]))]) implies some (s.personProjects & c.courseProjects) }
    S82 in valid iff { 
  all c : Course | all s : enrolled.c - Professor | (some Student.(c.(instanceGrades[this])) and s.(c.(instanceGrades[this])) = (order_max[this, Student.(c.(instanceGrades[this]))])) implies some (s.personProjects & c.courseProjects) }
    S83 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c: Course, p: Student | some max[(c.(instanceGrades[this]))] 
}
    S84 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  all x: Student | all c:Course | (order_last[this]) in (x.(c.(instanceGrades[this]))) implies x.personProjects in c

}
    S85 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all s : Student, c : Course | some (s.(c.(instanceGrades[this])) & (order_last[this])) implies 
  								  s.enrolled in Course:>c.courseProjects
}
    S86 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all s : Student, c : Course | some (s.(c.(instanceGrades[this])) & (order_last[this])) implies 
  								  s.enrolled in Course:>courseProjects.(c.courseProjects)
}
    S87 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all s : Student, c : Course | some (s.(c.(instanceGrades[this])) & (order_last[this])) implies 
  								  s.enrolled.courseProjects in c.courseProjects
}
    S88 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all s : Student, c : Course | some (s.(c.(instanceGrades[this])) & (order_last[this])) implies 
  								  some (s.enrolled.courseProjects & c.courseProjects)
}
    S89 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course

	all c: Course | some s: Student | c.(instanceGrades[this])[s] = (order_max[this, c.(instanceGrades[this])[Student]]) => (s.enrolled in c)

}
    S90 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course

	all c: Course | some s: Student | c.(instanceGrades[this])[s] = (order_max[this, c.(instanceGrades[this])[Student]]) => (c in s.enrolled)

}
    S91 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course

	all c: Course | some s: Student |
  		(c.(instanceGrades[this])[s] in (order_max[this, c.(instanceGrades[this])[Student]])) implies c.courseProjects in s.personProjects

}
    S92 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course

	all c: Course | some s: Student |
  		(c.(instanceGrades[this])[s] in (order_max[this, c.(instanceGrades[this])[Student]])) implies s.personProjects in c.courseProjects

}
    S93 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course

	all c: Course, s: Student |
  		(c.(instanceGrades[this])[s] in (order_max[this, c.(instanceGrades[this])[Student]])) implies s.personProjects in c.courseProjects

}
    S94 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course

	all c: Course, s: Student |
  		(c.(instanceGrades[this])[s] in (order_max[this, c.(instanceGrades[this])[Student]])) implies c.courseProjects in s.personProjects

}
    S95 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course

	all c: Course, s: Student |
  		(c.(instanceGrades[this])[s] in (order_max[this, c.(instanceGrades[this])[Student]])) implies some p : Project | (p in s.personProjects and p in c.courseProjects)

}
    S96 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all s : Student, c : s.enrolled | ( s.(c.(instanceGrades[this])) 
in max[c.(instanceGrades[this])]) implies some(s.personProjects & c.courseProjects)
}
    S97 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all s : Student, c : s.enrolled | ( max[(instanceGrades[this]).c] in s.(c.(instanceGrades[this]))  ) implies some(s.personProjects & c.courseProjects)
}
    S98 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
    all s : Student, c : Course |
        ((instanceGrades[this])[c][s] = (order_max[this, (instanceGrades[this])[Course][Student]])) implies (some s.personProjects & c.courseProjects)
}
    S99 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
    all c : Course | some ((order_max[this, c.(instanceGrades[this])[Student]])[c.(instanceGrades[this])].personProjects & c.courseProjects)
        or no c.(instanceGrades[this]) or no c.courseProjects
}
    S100 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
    all c : Course | some ((order_max[this, Course.(instanceGrades[this])[Student]])[Course.(instanceGrades[this])].personProjects & c.courseProjects)
        or no c.(instanceGrades[this]) or no c.courseProjects
}
    S101 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
    all c : Course | some ((order_max[this, Course.(instanceGrades[this])[Student]])[c.(instanceGrades[this])].personProjects & c.courseProjects)
        or no c.(instanceGrades[this]) or no c.courseProjects
}
    S102 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
    let highest_mark = (order_max[this, (instanceGrades[this])[Course][Student]]) |
    let s = highest_mark[Course.(instanceGrades[this])] |
    let c = { c : Course | c.(instanceGrades[this])[s] = highest_mark } |
    some (s.personProjects & c.courseProjects)
    or no c.(instanceGrades[this]) or no c.courseProjects
}
    S103 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
    let highest_mark = (order_max[this, (instanceGrades[this])[Course][Student]]) |
    let s = highest_mark[Course.(instanceGrades[this])] |
    let c = { c : Course | c.(instanceGrades[this])[s] = highest_mark } |
    some (s.personProjects & c.courseProjects)
}
    S104 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
    let highest_mark = (order_max[this, Grade]) |
    let s = highest_mark[Course.(instanceGrades[this])] |
    let c = { c : Course | c.(instanceGrades[this])[s] = highest_mark } |
    some (s.personProjects & c.courseProjects)
  	or no c.(instanceGrades[this]) or no c.courseProjects
}
    S105 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
    let highest_mark = (order_max[this, Grade]) |
    let s = highest_mark[Course.(instanceGrades[this])] |
    let c = { c : Course | c.(instanceGrades[this])[s] = highest_mark } |
    some (s.personProjects & c.courseProjects)
}
    S106 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
    let highest_mark = (order_max[this, Grade]) |
    let s = highest_mark[Course.(instanceGrades[this])] |
    let c = { c : Course | c.(instanceGrades[this])[s] = highest_mark } |
    some (s.personProjects & c.courseProjects) or no c.(instanceGrades[this])
}
    S107 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	let highest_mark = (order_max[this, (instanceGrades[this])[Course][Student]]) |
  	let s = highest_mark[Course.(instanceGrades[this])] |
    all c : Course | 
  		c.(instanceGrades[this])[s] = highest_mark
     	implies (
          	some (s.personProjects & c.courseProjects)
        	or no c.(instanceGrades[this]) or no c.courseProjects
  		)
}
    S108 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	let highest_mark = (order_max[this, (instanceGrades[this])[Course][Student]]) |
  	let s = highest_mark[Course.(instanceGrades[this])] |
    all c : Course | 
  		c.(instanceGrades[this])[s] = highest_mark
     	implies some (s.personProjects & c.courseProjects)
}
    S109 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	let highest_mark = (order_max[this, Grade]) |
  	let s = highest_mark[Course.(instanceGrades[this])] |
    all c : Course | c.(instanceGrades[this])[s] = highest_mark
     	implies some (s.personProjects & c.courseProjects)
}
    S110 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	all s : Student, c : Course | (instanceGrades[this])[c][s] = (order_max[this, (instanceGrades[this])[Course][Student]])
        implies some s.personProjects & c.courseProjects or no c.(instanceGrades[this]) or no c.courseProjects
}
    S111 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	all s : Student, c : Course | (instanceGrades[this])[c][s] = (order_max[this, (instanceGrades[this])[Course][Student]])
        implies some s.personProjects & c.courseProjects or no c.(instanceGrades[this])
}
    S112 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all s : Student | ( all c : s.enrolled | (lone g : Grade | s->g in c.(instanceGrades[this]) implies some ( s.personProjects & c.courseProjects)))
}
    S113 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	// max[x] gets the maximum value inside x (in this case the highest value in Grade)
	all s : Student, c : s.enrolled, g : (order_max[this, s.(c.(instanceGrades[this]))]) | some (s.personProjects & c.courseProjects)
}
    S114 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  all c: Course, s: Student, g: Grade | s->g in c.(instanceGrades[this]) => s.personProjects in c.courseProjects

}
    S115 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all s : Student | ( all c : s.enrolled | (one g : Grade | s.personProjects = c.courseProjects implies s->g in c.(instanceGrades[this])  ))
}
    S116 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all disj s1, s2: Student | all c: Course | no g2: c.(instanceGrades[this])[s2] | g2 in c.(instanceGrades[this])[s1].(order_next[this]) => some (s1.personProjects & c.courseProjects)
}
    S117 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all s1, c: Course | c.(instanceGrades[this])[s1] = c.(instanceGrades[this]).max => some (s1.courseProjects & c.courseProjects)
}
    S118 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	all s: Student, c: Course, g: Grade | s->g in c.(instanceGrades[this]) => c.courseProjects in s.personProjects
}
    S119 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	all c: Project.~(Course <: courseProjects) {
      	some (order_max[this, c.(instanceGrades[this])[Student]])
  	}

}
    S120 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	all g: Grade {
        let student = (this.@Person + this.@Course + this.@Project + this.@Grade + Int + String + OrderingAtom).(instanceGrades[this]).g, course = (instanceGrades[this]).g.(this.@Person + this.@Course + this.@Project + this.@Grade + Int + String + OrderingAtom) {
          	g = (order_max[this, course.(instanceGrades[this])[Student]]) implies some student.personProjects & course.courseProjects
        }
    }

}
    S121 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	all g: Grade {
        let student = (this.@Person + this.@Course + this.@Project + this.@Grade + Int + String + OrderingAtom).(instanceGrades[this]).g, course = (instanceGrades[this]).g.(this.@Person + this.@Course + this.@Project + this.@Grade + Int + String + OrderingAtom) {
          	{
              	some course.courseProjects
          		g = (order_max[this, course.(instanceGrades[this])[Student]])
      		} implies some student.personProjects & course.courseProjects
        }
    }

}
    S122 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	all c: Course | some c.courseProjects
}
    S123 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c: Course | let maxGrade = max[c.(instanceGrades[this])] {
        some s: Student | s.(instanceGrades[this]).c = maxGrade and s.personProjects in c.courseProjects
    }
}
    S124 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c : Course | some s : Student | c.(instanceGrades[this])[Student] & (order_first[this]) = c.(instanceGrades[this])[s] => some (s.personProjects & c.courseProjects)
}
    S125 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c : Course | one s : Student | (order_first[this]) = c.(instanceGrades[this])[s] && some (s.personProjects & c.courseProjects)
}
    S126 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c: Course | some c.(instanceGrades[this]).((order_min[this, Student.(c.(instanceGrades[this]))])).personProjects & c.courseProjects
}
    S127 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all s : Student, c : s.enrolled | s.(c.(instanceGrades[this])) in (order_max[this, Person.(c.(instanceGrades[this]))]) implies some (c.courseProjects & s.personProjects)
}
    S128 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all s : Student, c : s.enrolled | some c.(instanceGrades[this]) and s.(c.(instanceGrades[this])) in (order_max[this, Person.(c.(instanceGrades[this]))]) implies some (c.courseProjects & s.personProjects)
}
    S129 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
           all s : Student, c : s.enrolled |
             (all s1 : Student | c in s1.enrolled implies (order_lt[this, c.(instanceGrades[this])[s1], c.(instanceGrades[this])[s]]))
             implies
             some c.courseProjects & s.personProjects
}
    S130 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
           all s : Student, c : s.enrolled |
             (all s1 : Student | s1!=s and c in s1.enrolled implies (order_lte[this, c.(instanceGrades[this])[s1], c.(instanceGrades[this])[s]]))
             implies
             (some c.courseProjects & s.personProjects)
               or
              one enrolled.c
}
    S131 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
           all s : Student, c : s.enrolled |
             (order_lte[this, c.(instanceGrades[this])[Student], c.(instanceGrades[this])[s]])
             implies
             some c.courseProjects & s.personProjects
}
    S132 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
           all s : Student, c : s.enrolled |
             (order_lt[this, c.(instanceGrades[this])[Student-s], c.(instanceGrades[this])[s]])
             implies
             some c.courseProjects & s.personProjects
}
    S133 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
           all s : Student, c : s.enrolled |
             (order_lte[this, c.(instanceGrades[this])[Student], c.(instanceGrades[this])[s]])
             implies
             (some c.courseProjects & s.personProjects
              or one enrolled.c
             )
}
    S134 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  
  all s1: Student,c:Course | not ( some s2:Student | 
      (order_gt[this, s2.(c.(instanceGrades[this])), s1.(c.(instanceGrades[this]))]) )
      implies
      (some s1.personProjects & c.courseProjects) 

}
    S135 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c : Course, s : Student
  		| (order_max[this, Student.(c.(instanceGrades[this]))]) in s implies some pr : s.personProjects | pr in c.courseProjects
}
    S136 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all s : Student, c : s.enrolled, g: Person.(c.(instanceGrades[this])) | (g != s.(c.(instanceGrades[this]))) implies some s.personProjects
}
    S137 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all s : Student, c : Course
		| (order_max[this, Grade]) in Student.(c.(instanceGrades[this])) implies some pr : c.courseProjects | pr in s.personProjects
}
    S138 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course

   all s : Student, c : Course, g : Grade, g2 : Grade-g, p : Project | (c->s->g in (instanceGrades[this]) and (order_gt[this, g, g2])) implies (s->c in enrolled and c->p in courseProjects and s->p in personProjects)
}
    S139 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course

	// all c : Course, p : Person | last in p.(c.grades) implies
	//   some pr :Project | p->pr in projects and c->pr in projects

	// all c : Course, p : Person | last in p.(c.grades) implies some p.projects & c.projects

    all s1: Person,c: Course | (not ( some s2:Student | 
      (order_gt[this, s2.(c.(instanceGrades[this])), s1.(c.(instanceGrades[this]))])))
      implies
      (some s1.personProjects & c.courseProjects) 

}
    S140 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course

	// all c : Course, p : Person | last in p.(c.grades) implies
	//   some pr :Project | p->pr in projects and c->pr in projects

	// all c : Course, p : Person | last in p.(c.grades) implies some p.projects & c.projects

    all s1: Student,c: Course | (not ( some s2:Student-s1 | 
      (order_gt[this, s2.(c.(instanceGrades[this])), s1.(c.(instanceGrades[this]))])))
      implies
      (some s1.personProjects & c.courseProjects) 

}
    S141 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course

	// all c : Course, p : Person | last in p.(c.grades) implies
	//   some pr :Project | p->pr in projects and c->pr in projects

	// all c : Course, p : Person | last in p.(c.grades) implies some p.projects & c.projects

    all s1: Student,c: Course | (not ( some s2:Student | 
      (order_gt[this, s2.(c.(instanceGrades[this])), s1.(c.(instanceGrades[this]))]))
      and
      (some s1.personProjects & c.courseProjects))

}
    S142 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course

	// all c : Course, p : Person | last in p.(c.grades) implies
	//   some pr :Project | p->pr in projects and c->pr in projects

	// all c : Course, p : Person | last in p.(c.grades) implies some p.projects & c.projects

    all s1: Student,c: Course | (not ( some s2:Student-s1 | 
      (order_gt[this, s2.(c.(instanceGrades[this])), s1.(c.(instanceGrades[this]))]))
      and
      (some s1.personProjects & c.courseProjects))

}
    S143 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course

	// all c : Course, p : Person | last in p.(c.grades) implies
	//   some pr :Project | p->pr in projects and c->pr in projects

	// all c : Course, p : Person | last in p.(c.grades) implies some p.projects & c.projects

    all s1: Person,c: Course | 
      (not (some s2:Student-s1 | (order_gt[this, s2.(c.(instanceGrades[this])), s1.(c.(instanceGrades[this]))])))
      implies some s1.personProjects & c.courseProjects

}
    S144 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all s: Student, c: Course | s.(c.(instanceGrades[this])) = max[c.(instanceGrades[this])] implies 
  		s.personProjects & c.courseProjects != none
}
    S145 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	// max[x] max value from x
  
  	all s : Student, c : s.enrolled | some p : s.personProjects | (order_max[this, Grade]) in s.(c.(instanceGrades[this])) implies p in c.courseProjects
}
    S146 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	// max[x] gets the maximum value inside x (in this case the highest value in Grade)
	all s : Student, c : s.enrolled, g : (order_max[this, s.(Course.(instanceGrades[this]))]) | g in s.(c.(instanceGrades[this])) implies some (s.personProjects & c.courseProjects)
}
    S147 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	/* 	one s : Student | one c : s.enrolled | 
  	 	c.grades[s] = max[Grade] implies 
  		
  	*/
  	one s : Student | some c : s.enrolled | 
  		c.(instanceGrades[this])[s] = (order_max[this, Grade]) implies some s.personProjects & c.courseProjects
  	
	
}
    S148 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	/* 	one s : Student | one c : s.enrolled | 
  	 	c.grades[s] = max[Grade] implies 
  		
  	*/
  	one s : Student | some c : s.enrolled | 
  		c.(instanceGrades[this])[s] in (order_max[this, Grade]) implies some s.personProjects & c.courseProjects
  	
	
}
    S149 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	/* 	one s : Student | one c : s.enrolled | 
  	 	c.grades[s] = max[Grade] implies 
  		
  	*/
  	one s : Student | some c : Course | 
  		c.(instanceGrades[this])[s] = (order_max[this, Grade]) implies some s.personProjects & c.courseProjects
  	
	
}
    S150 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	/* 	one s : Student | one c : s.enrolled | 
  	 	c.grades[s] = max[Grade] implies 
  		
  	*/
  	one s : Student | one c : s.enrolled | 
  		c.(instanceGrades[this])[s] in (order_max[this, Grade]) implies some s.personProjects & c.courseProjects
  	
	
}
    S151 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	one s: Student | all c: Course | some p: s.personProjects | s in (order_first[this]).(instanceGrades[this])[c] => p in s.personProjects & c.courseProjects 
}
    S152 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	one s: Student | all c: Course | some p: s.personProjects | s in c.(instanceGrades[this]).(order_first[this]) => p in s.personProjects & c.courseProjects 
}
    S153 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	one s: Student | all c: Course | some p: s.personProjects | s in c.(instanceGrades[this]).(order_last[this]) => p in s.personProjects & c.courseProjects 
}
    S154 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	one s: Student | all c: Course |
  		(order_last[this]) in s.(c.(instanceGrades[this])) implies some c.(Course <: courseProjects) & s.(Person <: personProjects)
  		
}
    S155 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	one s: Student | all c: Course | s in c.(instanceGrades[this]).(order_first[this]) => some s.personProjects & c.courseProjects 
}
    S156 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all s: Student | all c: Course | c.(instanceGrades[this])[s] = c.(instanceGrades[this]).max implies c.courseProjects in s.personProjects
}
    S157 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all s: Student | all c: Course | some p: Project | s in c.(instanceGrades[this]).((order_max[this, Grade])) implies p in s.personProjects and p in c.courseProjects
        
}
    S158 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  all p: Person | all c: Course | c.(instanceGrades[this])[p] = c.(instanceGrades[this]).((order_max[this, Grade])) implies some pr:Project | pr in p.personProjects

}
    S159 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  all c: Course | 
        one s: Student | c.(instanceGrades[this])[s] = (order_last[this])[c.(instanceGrades[this])] implies #(s.personProjects & c.courseProjects) > 0
}
    S160 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	all s1:Student,  c:Course | (all s2:Student | (order_gte[this, s1.(c.(instanceGrades[this])), s2.(c.(instanceGrades[this]))]) )
	implies
	lone (s1.personProjects - c.courseProjects)

}
    S161 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all s1:Student,  c:Course | ((all s2:Student | (order_gte[this, s1.(c.(instanceGrades[this])), s2.(c.(instanceGrades[this]))]) )
						implies
						some (s1.personProjects & c.courseProjects))

}
    S162 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	all g : Grade | some c : Course, u : Person | u->g in c.(instanceGrades[this])
	all c : Course | let g = c.(instanceGrades[this]), g2 = Person.g | some c.courseProjects implies g.((order_max[this, g2])) in (Person <: personProjects).(c.courseProjects)
}
    S163 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	all g : Grade | some c : Course, u : Person | u->g in c.(instanceGrades[this])
	//all c : Course | let g = c.grades, g2 = Person.g | some c.projects implies g.(max[g2]) in (Person <: projects).(c.projects)
}
    S164 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c: Course, s: Student, sg: s.(c.(instanceGrades[this])) | all cg: Person.(c.(instanceGrades[this])) - sg | some p: c.courseProjects | (order_gte[this, sg, cg]) implies p in s.personProjects
}
    S165 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c: Course, s: Student, sg: s.(c.(instanceGrades[this])) | all cg: Person.(c.(instanceGrades[this])) - sg | all p: c.courseProjects | (order_gte[this, sg, cg]) implies p in s.personProjects
}
    S166 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all p:Person | some c:Course | (order_last[this]) in p.(c.(instanceGrades[this])) implies (p.personProjects & c.courseProjects != none)
}
    S167 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  let map1 = Grade -> Int |
  all c: Course |
        // Trova tutti gli studenti con il voto più alto
        all s: Student |
            // Lo studente s ha il voto massimo nel corso c
            (all s2: Student | #c.(instanceGrades[this])[s2] > 0 => c.(instanceGrades[this])[s].map1 >= c.(instanceGrades[this])[s2].map1) =>
            // Deve aver lavorato su almeno un progetto del corso
            some c.courseProjects & s.personProjects
  			
}
    S168 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all s: Student | all c:Course | one p:Project | (order_max[this, Grade]) in s.(c.(instanceGrades[this])) and p in c.courseProjects and c in s.enrolled implies p in s.personProjects 
}
    S169 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all s: Student | all c:Course | some p:Project | (order_max[this, Grade]) in s.(c.(instanceGrades[this])) and p in c.courseProjects and c in s.enrolled implies p in s.personProjects 
}
    S170 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	one s: Student | all c: Course |
  		(order_last[this]) in s.(c.(instanceGrades[this])) implies c in s.(Person <: personProjects)
  		

}
    S171 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	one s: Student | all c: Course |
  		(order_last[this]) in s.(c.(instanceGrades[this])) implies c.(Course <: courseProjects) in s.(Person <: personProjects)
  		

}
    S172 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	one p: Person| all c: Course |
  		(order_last[this]) in p.(c.(instanceGrades[this])) implies some c.courseProjects & p.personProjects
  		
}
    S173 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	one p: Person, c: Course |
  		(order_last[this]) in p.(c.(instanceGrades[this])) implies some (c.courseProjects & p.personProjects)
  		
}
    S174 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c : Course, p : Person |
  	some p.personProjects & c.courseProjects implies (order_last[this]) in p.(c.(instanceGrades[this]))
}
    S175 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	let map = Grade -> Int |
	all c: Course |
        all s: Student |
            // Se lo studente ha il voto massimo
            (all s2: Student | c.(instanceGrades[this])[s].map >= c.(instanceGrades[this])[s2].map) =>
            // Deve aver lavorato su almeno un progetto del corso
            some c.courseProjects & s.personProjects
}
    S176 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	let map = Grade -> Int |
	all c: Course |
        all s: Student |
            // Se lo studente ha il voto massimo
            ((all s2: Student | c.(instanceGrades[this])[s].map >= c.(instanceGrades[this])[s2].map) =>
            // Deve aver lavorato su almeno un progetto del corso
            some c.courseProjects & s.personProjects) or #c.(instanceGrades[this])[] = 1
}
    S177 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  	let map = Grade -> Int |
	all c: Course |
        all s: c.~enrolled |
            // Se lo studente ha il voto massimo
            ((all s2: c.~enrolled | c.(instanceGrades[this])[s].map >= c.(instanceGrades[this])[s2].map) =>
            // Deve aver lavorato su almeno un progetto del corso
            some c.courseProjects & s.personProjects)
}
    S178 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c: Course |
        some s: Student | 
            (s in (c.(instanceGrades[this])).Grade and c.(instanceGrades[this])[s] = (order_last[this])) implies
                (some p: Project | p in s.personProjects and p in c.courseProjects)
}
    S179 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	some s: Student, c: Course | s.(c.(instanceGrades[this])) = (order_max[this, Person.(c.(instanceGrades[this]))]) implies 
  		s.personProjects & c.courseProjects != none
}
    S180 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c : Course | some ((Student->(order_max[this, Student.(c.(instanceGrades[this]))])) & c.(instanceGrades[this])).Grade.personProjects
}
    S181 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c : Course | one (c.(instanceGrades[this])).Grade.personProjects & c.courseProjects
}
    S182 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c : Course | some (c.(instanceGrades[this])).Grade.personProjects & c.courseProjects
}
    S183 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c : Course | (c.(instanceGrades[this])).Grade.personProjects = c.courseProjects
}
    S184 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c : Course | c.courseProjects in (c.(instanceGrades[this])).Grade.personProjects 
}
    S185 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c : Course | some (c.(instanceGrades[this])).Grade.personProjects
}
    S186 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c : Course | some (c.(instanceGrades[this])).Grade.personProjects => some c.courseProjects
}
    S187 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  all s : Student | all c : Course | some c.(instanceGrades[this]) and (order_first[this])[c.(instanceGrades[this])] = c.(instanceGrades[this])[s] implies some p:Project | p in c.courseProjects and p in s.personProjects

}
    S188 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  all s : Student | all c : Course | all p :Project | some c.(instanceGrades[this]) and (order_first[this])[c.(instanceGrades[this])] = c.(instanceGrades[this])[s] implies p in c.courseProjects and p in s.personProjects

}
    S189 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
  all s : Student | all c : Course | all p :Project | some c.(instanceGrades[this]) and c.(instanceGrades[this])[s] in (order_first[this])[c.(instanceGrades[this])] implies p in c.courseProjects and p in s.personProjects

}
    S190 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all s : Student | all c : Course | 
		(some c.(instanceGrades[this]) and c.(instanceGrades[this])[s] in (order_last[this])[c.(instanceGrades[this])]) 
		implies 
		(some p : Project | p in c.courseProjects and p in s.personProjects)
}
    S191 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	let highest = {
		c: Course, s: c.~enrolled |
			no c.(instanceGrades[this])[s].(order_next[this])
	} |
	all c: Course |
		c.courseProjects & highest[c].personProjects != none
}
    S192 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
    let highest = {
        s: Student, c: s.enrolled |
            c.(instanceGrades[this])[s].(order_next[this]) = none
    } | all s: Student |
        s in highest[s].courseProjects.~(Person <: personProjects)
}
    S193 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
    let highest = {
        s: Person, c: s.enrolled |
            no c.(instanceGrades[this])[s].(order_next[this])
    } | all p: Person |
        p in highest[p].courseProjects.~(Person <: personProjects)
}
    S194 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
    // let highest = {
    //     c: Course, p: c.~enrolled | no c.grades[p].next
    // } |
    //     all c: Course, p: highest.c |
    //         p.projects & c.projects
    let highest = {
        c: Course, p: c.~enrolled | no c.(instanceGrades[this])[p].(order_prev[this])
    } | all s: Person |
            s in s.~highest.courseProjects.~(Person <: personProjects)
}
    S195 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
    // let highest = {
    //     c: Course, p: c.~enrolled | no c.grades[p].next
    // } |
    //     all c: Course, p: highest.c |
    //         p.projects & c.projects
    let highest = {
        c: Course, p: c.~enrolled | no c.(instanceGrades[this])[p].(order_next[this])
    } | all p: Person |
        some p[highest] implies p in p[highest].courseProjects.~(Person <: personProjects)
}
    S196 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
    let highest = {
        s: Person, c: s.enrolled |
            no c.(instanceGrades[this])[s].(order_next[this])
   } | all p: Person |
        highest[p].courseProjects in p.personProjects
}
    S197 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	let highest = {
		c: Course, s: c.~enrolled |
			c.(instanceGrades[this])[s].(order_next[this]) not in c.(instanceGrades[this])[Person]
	} |
	all c: Course |
		c.courseProjects & highest[c].personProjects != none
}
    S198 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	let highest = {
		c: Course, s: c.~enrolled |
			c.(instanceGrades[this])[s].(order_next[this]) & c.(instanceGrades[this])[Person] = none
	} |
	all c: Course |
		c.courseProjects & highest[c].personProjects != none
}
    S199 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	let highest = {
		s: Student, c: s.enrolled |
			c.(instanceGrades[this])[s].(order_next[this]) & c.(instanceGrades[this])[Person] = none
	} | all s: Student |
		s in highest[s].courseProjects.~(Student <: personProjects)
}
    S200 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	let highest = {
		s: Student, c: s.enrolled |
			c.(instanceGrades[this])[s].(order_prev[this]) & c.(instanceGrades[this])[Person] = none
	} | all s: Student |
		s in highest[s].courseProjects.~(Student <: personProjects)
}
    S201 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	let highest = {
		s: Person, c: s.enrolled |
			c.(instanceGrades[this])[s].(order_next[this]) & c.(instanceGrades[this])[Person] = none
	} | all s: Student |
		some highest[s] implies one s.personProjects & highest[s].courseProjects
}
    S202 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	let highest = {
		s: Person, c: s.enrolled |
			c.(instanceGrades[this])[s].(order_next[this]) & c.(instanceGrades[this])[Person] = none
	} | all s: Student |
		some highest[s] implies some s.personProjects & highest[s].courseProjects
}
    S203 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c: Course, s: c.~enrolled |
		c.(instanceGrades[this])[s].(order_next[this]) not in c.(instanceGrades[this])[Person]
			implies s.personProjects & c.courseProjects != none
}
    S204 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	all c: Course, s: c.~enrolled |
		no c.(instanceGrades[this])[s].(order_next[this]) & c.(instanceGrades[this])[Person]
			implies s.personProjects & c.courseProjects != none
}
    S205 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
	let highest = {s: Student, c: s.enrolled |
		c.(instanceGrades[this])[s] = (order_last[this])
	} |
	all s: Student |
		s.personProjects & (highest[s].courseProjects) != none
}
    S206 in valid iff {
	// A student with the highest mark in a course must have worked on a project on that course
    all s: Student, c: Course | 
        (s.(c.(instanceGrades[this])) = (order_max[this, c.(instanceGrades[this])[Student]]) and some c.courseProjects)
        implies
        some s.personProjects & c.courseProjects

}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, S74, S75, S76, S77, S78, S79, S80, S81, S82, S83, S84, S85, S86, S87, S88, S89, S90, S91, S92, S93, S94, S95, S96, S97, S98, S99, S100, S101, S102, S103, S104, S105, S106, S107, S108, S109, S110, S111, S112, S113, S114, S115, S116, S117, S118, S119, S120, S121, S122, S123, S124, S125, S126, S127, S128, S129, S130, S131, S132, S133, S134, S135, S136, S137, S138, S139, S140, S141, S142, S143, S144, S145, S146, S147, S148, S149, S150, S151, S152, S153, S154, S155, S156, S157, S158, S159, S160, S161, S162, S163, S164, S165, S166, S167, S168, S169, S170, S171, S172, S173, S174, S175, S176, S177, S178, S179, S180, S181, S182, S183, S184, S185, S186, S187, S188, S189, S190, S191, S192, S193, S194, S195, S196, S197, S198, S199, S200, S201, S202, S203, S204, S205, S206 extends Formula {}

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
