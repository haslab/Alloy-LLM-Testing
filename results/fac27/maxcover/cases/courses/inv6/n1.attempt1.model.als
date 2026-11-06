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
    Oracle in valid iff {
	// Students only work on projects of courses they are enrolled in
    all s: Student | s.personProjects in s.enrolled.courseProjects
    //all p: Student.projects | p in projects.p.enrolled.projects
    //Course.projects in Student.projects
}
    S1 in valid iff {
	// Students only work on projects of courses they are enrolled in
    Course.courseProjects in Student.personProjects
}
    S2 in valid iff {
	// Students only work on projects of courses they are enrolled in
    all p: Student.personProjects | p in personProjects.p.enrolled.courseProjects
    //Course.projects in Student.projects
}
    S3 in valid iff {
	// Students only work on projects of courses they are enrolled in

        // all s : Student | all pr : Project | all c : Course |
	//  c->pr in projects implies s->c in enrolled

        all s : Student | all c : Course | some c.courseProjects implies s->c in enrolled
}
    S4 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s : Student, p : Project, c : Course | 
  		p in s.personProjects implies c.courseProjects in s.enrolled
}
    S5 in valid iff {
	// Students only work on projects of courses they are enrolled in
  	all s : Student | some c : Course, p : Project | p in c.courseProjects and c in s.enrolled implies p in s.personProjects

}
    S6 in valid iff {
	// Students only work on projects of courses they are enrolled in
  	all s : Person-Professor | some c : Course, p : Project | p in c.courseProjects and c in s.enrolled implies p in s.personProjects

}
    S7 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all p : Person - Professor |
  		all proj : p.personProjects |
  			some c : p.enrolled | proj in c.courseProjects
}
    S8 in valid iff {
	// Students only work on projects of courses they are enrolled in
  all s:Student | courseProjects.(s.personProjects) = s.enrolled

}
    S9 in valid iff {
	// Students only work on projects of courses they are enrolled in
  	all s: Student| all c:Course | all pr:Project | pr in s.personProjects implies pr in c.courseProjects and c in 		  s.enrolled

}
    S10 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s : Person & Student, p : s.personProjects, c : s.enrolled | p in c.courseProjects
}
    S11 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s : Student | some c : Course | s.personProjects in c.courseProjects => s.enrolled in c  
}
    S12 in valid iff {
	// Students only work on projects of courses they are enrolled in
  
  all p: Person | all c: Course | all pr : Project | p in personProjects.pr implies p in Student and p in enrolled.c

}
    S13 in valid iff {
	// Students only work on projects of courses they are enrolled in
  	all s:Student | some s.personProjects implies some c:Course | some c.courseProjects and s->c in enrolled

}
    S14 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s : Student | some c : Course | 
  	 	s.personProjects in c.courseProjects and s.enrolled in c
}
    S15 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s : Student | some c : Course | 
  	 	s.personProjects in s.enrolled.courseProjects
}
    S16 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s : Student | s.personProjects = s.enrolled.courseProjects
}
    S17 in valid iff {
	// Students only work on projects of courses they are enrolled in
  	all pr: Project, c:Course | (some p:Student | p in (Person <: personProjects).pr and c in (Course <: courseProjects).pr implies p in enrolled.c)
}
    S18 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s:Student | some p:Project,c:Course | p in c.courseProjects and p in s.personProjects implies c in s.enrolled  
}
    S19 in valid iff {
	// Students only work on projects of courses they are enrolled in
      all s: Student |  s.enrolled.courseProjects in s.personProjects 

}
    S20 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s: Student | some p: Project | p in s.personProjects implies s in enrolled.(Course <: courseProjects.p)
}
    S21 in valid iff {
	// Students only work on projects of courses they are enrolled in
  	all p : Student | (some c : Course, p : Project | p in enrolled.c and c in courseProjects.p )  

}
    S22 in valid iff {
	// Students only work on projects of courses they are enrolled in
  	all s : Student | all c : Course | some pr : Project | s in personProjects.pr implies s in enrolled.c and c in courseProjects.pr
}
    S23 in valid iff {
	// Students only work on projects of courses they are enrolled in
  	all p : Person | all c : Course | some pr : Project | p in personProjects.pr and p in Student implies p in enrolled.c and c in courseProjects.pr
}
    S24 in valid iff {
	// Students only work on projects of courses they are enrolled in
  	all s: Student | all c: Course| s.personProjects in c.courseProjects implies c in s.enrolled  

}
    S25 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s : Student | some(s.personProjects)
}
    S26 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s : Student, p : s.personProjects | one c : Course | p in c.courseProjects implies c in s.enrolled
}
    S27 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all p : Person | some c : p.enrolled | c.courseProjects in p.personProjects
}
    S28 in valid iff {
	// Students only work on projects of courses they are enrolled in
	// all s : Student, p : s.projects | some s.enrolled & (Course <: projects).p
  	all s : Student | s.enrolled in courseProjects.(s.personProjects)
}
    S29 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all p : Person | (some p.enrolled and some p.enrolled.courseProjects) implies Person<:personProjects.Project in p 
}
    S30 in valid iff { Student.personProjects in Student.enrolled.courseProjects  
}
    S31 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s : Student | all c : s.enrolled | s.personProjects in c
}
    S32 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s:Student, p:s.enrolled.courseProjects | s.personProjects in p
}
    S33 in valid iff {
	// Students only work on projects of courses they are enrolled in
    all pr : Project, s : Person-Professor | all c : (Course <: courseProjects).pr | pr in s.personProjects and c in s.enrolled

}
    S34 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s : Person - Professor | all p : Project | s.enrolled in courseProjects.p
}
    S35 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s : Person-Professor | all p : s.personProjects | s.enrolled in courseProjects.p
}
    S36 in valid iff {
	// Students only work on projects of courses they are enrolled in
  all s : Student | s.personProjects = s.enrolled 

}
    S37 in valid iff {
	// Students only work on projects of courses they are enrolled in

	all s: Student, p: Project | s.enrolled.courseProjects in p

}
    S38 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all st : Student | all c : Course | c.courseProjects in st.personProjects implies c in st.enrolled
}
    S39 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all st : Student | all p : Project | one c : Course | p in st.personProjects implies c in st.enrolled and p in c.courseProjects
}
    S40 in valid iff {
	// Students only work on projects of courses they are enrolled in
  	(Student <: personProjects).Project in enrolled.Course

}
    S41 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all p : Person, c : Course | p.personProjects in c.enrolled => p in Student
}
    S42 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s:Student | some c:Course | c in s.enrolled
}
    S43 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s:Student | some c:Course | some p:Project | p in s.personProjects implies c in s.enrolled
}
    S44 in valid iff {
	// Students only work on projects of courses they are enrolled in
	//all s1 : Person | all p1 : Project | 
  	//s1->p1 in projects implies (some c1 : Course | c1->p1 in projects and s1->c1 in enrolled)
  	all s: Person - Professor, prj: Project | 
        prj in s.enrolled.courseProjects
}
    S45 in valid iff { 
	// Students only work on projects of courses they are enrolled in
	all p: Project, s: Student | some c: Course | p in s.personProjects and p in c.courseProjects => c in s.enrolled 
}
    S46 in valid iff { 
	// Students only work on projects of courses they are enrolled in
	all c: Course, s: Student | some p: Project | c in s.enrolled and p in s.personProjects => p in c.courseProjects 
}
    S47 in valid iff {
	// Students only work on projects of courses they are enrolled in
	// all s : Student, p : s.projects | some s.enrolled & (Course <: projects).p
  	all s : Student | s.enrolled in none
}
    S48 in valid iff {
	// Students only work on projects of courses they are enrolled in
  Student->Course in enrolled 
}
    S49 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all x : Student, p : Project | one c : Course | p in x.personProjects and p in c.courseProjects implies c in x.enrolled
}
    S50 in valid iff {
	// Students only work on projects of courses they are enrolled in
  all s : Student, c : Course | (some c->Project) implies s->c in enrolled

}
    S51 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all p : Student, c : Course | (p in enrolled.c implies some c.courseProjects)
}
    S52 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s:Student | all p:Project | all c:Course | s->p in personProjects implies c->p in courseProjects
}
    S53 in valid iff {
  	// Students only work on projects of courses they are enrolled in
  	some s : Student | all pr : Project | some c : Course |
  		pr in s.personProjects implies (pr in c.courseProjects and c in s.enrolled)
  
  	
}
    S54 in valid iff {
	// Students only work on projects of courses they are enrolled in
	// all s : Student, c : Course | (some s.projects & c.projects) implies s -> c in enrolled
	all s : Student, c : Course, p : Project | s.personProjects in p and c.courseProjects in p implies s -> c in enrolled
}
    S55 in valid iff {
	// Students only work on projects of courses they are enrolled in
  	(Person <: personProjects).Project = enrolled.Course

}
    S56 in valid iff {
	// Students only work on projects of courses they are enrolled in
  	enrolled.Course in (Student <: personProjects).Project 

}
    S57 in valid iff {
	// Students only work on projects of courses they are enrolled in
  	all s: Student, pr: Project, c: Course | s -> c in enrolled implies pr in c.courseProjects
}
    S58 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s : Student, p : Project, c : Course | c in s.enrolled implies p in s.personProjects
  
}
    S59 in valid iff {
    // Students only work on projects of courses they are enrolled in
    all s:Student-Professor | all p:Project | all c:Course | (s->c in enrolled and c->p in courseProjects) implies s->p in personProjects
}
    S60 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s : Student | all p : s.personProjects | p = s.enrolled.courseProjects
}
    S61 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s:Student | some p:Project | some c:Course |
  		p in s.personProjects implies (p in c.courseProjects and c in p.enrolled)
  	
}
    S62 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s:Student | some p:Project | one c:Course |
  		p in s.personProjects implies (p in c.courseProjects and c in s.enrolled)
  	
}
    S63 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s:Student | one p:Project | one c:Course |
  		p in s.personProjects implies (p in c.courseProjects and c in s.enrolled)
  	
}
    S64 in valid iff {
	// Students only work on projects of courses they are enrolled in

  all s : Student |  some s.(Person <: personProjects)  & (s.enrolled).(Course <: courseProjects)  
  
}
    S65 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s : Student | all p : s.personProjects | one c : Course | p in c.courseProjects implies s in c.(instanceGrades[this]).Person
}
    S66 in valid iff {
	// Students only work on projects of courses they are enrolled in
  	all s:Student | all p:Project| (some c:Course | c in courseProjects.p and c in courseProjects.p implies p in s.personProjects)
}
    S67 in valid iff {
	// Students only work on projects of courses they are enrolled in
  	all s:Student | all p:Project| (some c:Course | s not in Professor and c in courseProjects.p and c in courseProjects.p implies p in s.personProjects)
}
    S68 in valid iff {
	// Students only work on projects of courses they are enrolled in
  	all p: Person | (p in Student) implies (p not in Professor)
  	all s:Student | all p:Project| (some c:Course | c in courseProjects.p and c in courseProjects.p implies p in s.personProjects)
}
    S69 in valid iff {
	// Students only work on projects of courses they are enrolled in
  	all s:Person | all p:Project| (some c:Course | s in Student and c in courseProjects.p and c in courseProjects.p implies p in s.personProjects and (s in Professor implies s not in personProjects.p))
}
    S70 in valid iff {
	// Students only work on projects of courses they are enrolled in
  	 all s: Student | all p: Project | 
        (some c: Course | c in s.enrolled and p in c.courseProjects) implies p in s.personProjects and
        (s in Professor implies p not in s.personProjects)
}
    S71 in valid iff {
	// Students only work on projects of courses they are enrolled in
  	 all s: Student | all p: Project | some c: Course |
        (c in s.enrolled and p in c.courseProjects) implies p in s.personProjects and (c in s.enrolled and p in c.courseProjects implies s not in c.teaches)
}
    S72 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s : Student, p : Project | p in s.personProjects implies some c : s.enrolled | p in c.enrolled or p in s.teaches.courseProjects
}
    S73 in valid iff {
	// Students only work on projects of courses they are enrolled in
  
  all s : Student, c : Course | some (s.personProjects & c.courseProjects)  

}
    S74 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s: Student, c: Course | Project in s.(Person<:personProjects) implies s in enrolled.c
}
    S75 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s: Student, c: Course, pr: Project | pr in s.(Person<:personProjects) iff c in s.enrolled
}
    S76 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all pr : Project, p : Person | one c : Course |
  		p -> pr in personProjects implies		
  			c -> pr in courseProjects and c in p.enrolled
}
    S77 in valid iff {
	// Students only work on projects of courses they are enrolled in
  all s:Student | some c:Course, p:c.courseProjects | c in s.enrolled implies p in s.personProjects

}
    S78 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s: Student | some p: Project | p in s.personProjects iff p in s.enrolled.courseProjects
}
    S79 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s: Student | one p: Project | p in s.personProjects iff p in s.enrolled.courseProjects
}
    S80 in valid iff {
	// Students only work on projects of courses they are enrolled in
  all p : Person, pr : Project | p in Student and p in personProjects.pr
  

}
    S81 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all p:Person,c:Course | p.(Person <: personProjects) in c.(Course <: courseProjects) implies p in Student and p in enrolled.c
  
 
  
  // Para todas as pessoas estudantes, so podem trabalhar em projetos que fazem parte dos cursos
}
    S82 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s : Student | some c: Course | some ( s.personProjects & c.courseProjects ) implies ( c in s.enrolled )
}
    S83 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s : Student, c:Course, pr:Project | pr in s.personProjects and pr in c.courseProjects
}
    S84 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all p: Person | all c: Course | c in p.enrolled <=> p.personProjects in c.courseProjects 
}
    S85 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s: Student | all c: s.enrolled | all p1, p2: s.personProjects | p1 in c.courseProjects and p2 in c.courseProjects implies p1 = p2
}
    S86 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s : Student | some c : s.enrolled | lone p : s.personProjects | p in c.courseProjects  
}
    S87 in valid iff {
	// Students only work on projects of courses they are enrolled in
  all s : Student | all pro : Project | all c : Course | s.personProjects in c.courseProjects => c in s.enrolled  

}
    S88 in valid iff {
	// Students only work on projects of courses they are enrolled in

  all s : Student |  lone  s.(Person <: personProjects)  & (s.enrolled).(Course <: courseProjects) 
  
  
}
    S89 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all p : Person, c : Course, pr: c.courseProjects |
  		(p.personProjects in pr) implies (c in p.enrolled)
}
    S90 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s : Student, p : Project| some c : Course | c in s.enrolled implies p in s.personProjects
  
}
    S91 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s: Student, c: Course | s.personProjects in c.courseProjects iff c in s.enrolled
}
    S92 in valid iff {
	// Students only work on projects of courses they are enrolled in
  	//all s: Student, p: Project | p in s.projects implies one (s.enrolled & (Course<:projects.p))
  	all s: Student, p: Project | p in s.personProjects implies one s.enrolled.(Course<:courseProjects)
}
    S93 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s : Student | some c : s.enrolled | some s.personProjects implies s.personProjects in c.courseProjects
}
    S94 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s: Student | some c: Course | c in s.enrolled implies c.courseProjects in s.personProjects
}
    S95 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s: Student | some c: Course, p: Project | c in s.enrolled implies p in s.personProjects
}
    S96 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s: Student | some c: Course | c in s.enrolled implies s.personProjects in c.courseProjects
}
    S97 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s: Student, c: Course | c in s.enrolled implies s.enrolled.courseProjects in c.courseProjects
}
    S98 in valid iff {
	// Students only work on projects of courses they are enrolled in
  	all s : Student, c: Course | some p : Project | s.enrolled in c implies p in s.personProjects
}
    S99 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s : Student, c : Course, pr : Project | (pr in s.personProjects) and (pr in c.courseProjects) and (s in enrolled.c)
}
    S100 in valid iff {
	// Students only work on projects of courses they are enrolled in
	//all s: Student, x: Project, c: Course | s in projects.x implies (s in enrolled.c and c in projects.x)
  
  all p:Person, x: Project, c: Course |( p in personProjects.x) iff (p in enrolled.c and c in courseProjects.x)  
}
    S101 in valid iff {
	// Students only work on projects of courses they are enrolled in
	//all s: Student, x: Project, c: Course | s in projects.x implies (s in enrolled.c and c in projects.x)
  
  some p:Student, x: Project, c: Course |( p in personProjects.x) iff (p in enrolled.c and c in courseProjects.x)  
}
    S102 in valid iff {
	// Students only work on projects of courses they are enrolled in
	//all s: Student, x: Project, c: Course | s in projects.x implies (s in enrolled.c and c in projects.x)
  
  some p:Student, x: Project, c: Course |( p in personProjects.x) iff (p in enrolled.c and c in courseProjects.x)  
  
  all p: Student | some x: Project, c:Course | p in personProjects.x iff (p in enrolled.c and c in courseProjects.x)
}
    S103 in valid iff {
	// Students only work on projects of courses they are enrolled in
	//all s: Student, x: Project, c: Course | s in projects.x implies (s in enrolled.c and c in projects.x)
  
  //some p:Student, x: Project, c: Course |( p in projects.x) iff (p in enrolled.c and c in projects.x)  
  
  all p: Student | some x: Project, c:Course | p in personProjects.x iff (p in enrolled.c and c in courseProjects.x)
}
    S104 in valid iff {
	// Students only work on projects of courses they are enrolled in
	//all s: Student, x: Project, c: Course | s in projects.x implies (s in enrolled.c and c in projects.x)
  
  //some p:Student, x: Project, c: Course |( p in projects.x) iff (p in enrolled.c and c in projects.x)  
  
  all p: Student | some x: Project, c:Course | p in personProjects.x implies (p in enrolled.c and c in courseProjects.x) and p not in teaches.c
}
    S105 in valid iff {
	// Students only work on projects of courses they are enrolled in
	//all p: Project, c: Course, s: Student | c in s.enrolled implies s in projects.p 
	all p: Project, c: Course, y: Person | y in enrolled.c implies ( y in Student and y in personProjects.p and (y not in teaches.c ))
}
    S106 in valid iff {
	// Students only work on projects of courses they are enrolled in
	//all p: Project, c: Course, s: Student | c in s.enrolled implies s in projects.p 
	all p: Project, c: Course, y: Person | y in enrolled.c implies ( y in Student and y in personProjects.p and (y not in personProjects.p ))
}
    S107 in valid iff {
	// Students only work on projects of courses they are enrolled in
	//all p: Project, c: Course, s: Student | c in s.enrolled implies s in projects.p 
	all p: Project, c: Course|some y: Person | y in enrolled.c implies ( y in Student and y in personProjects.p and (y not in personProjects.p ))
}
    S108 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all p: Student, c: Course, y: Project | (c in courseProjects.y) and (p in enrolled.c) and (p not in teaches.c) implies (p in personProjects.y)
}
    S109 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all p: Student,c: Course, x: Project| lone (enrolled.c & personProjects.x)
}
    S110 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all pj: Project | all c: Course | some p: Person | pj in p.personProjects implies c in p.enrolled

}
    S111 in valid iff {
	// Students only work on projects of courses they are enrolled in
	all s: Student | some c: Course | some s.personProjects implies s.personProjects in c.courseProjects and c in s.enrolled
}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, S74, S75, S76, S77, S78, S79, S80, S81, S82, S83, S84, S85, S86, S87, S88, S89, S90, S91, S92, S93, S94, S95, S96, S97, S98, S99, S100, S101, S102, S103, S104, S105, S106, S107, S108, S109, S110, S111 extends Formula {}

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
