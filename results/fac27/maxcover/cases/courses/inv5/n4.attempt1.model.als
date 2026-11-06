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
    Oracle in valid iff {
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
    S1 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p: Person | (some p.personProjects) implies p in Student
}
    S2 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
    Person<:personProjects.Project in Student
    some Project
}
    S3 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
    Person<:personProjects.Project in Student
    some Person<:personProjects.Project
}
    S4 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	Person <: personProjects in (Student some -> some Project)

}
    S5 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them

}
    S6 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all p : Project | all per : Person | per in (Person <: personProjects).p implies per in 	  (Person-Professor)  
  
	all p : Project | some per : Person | per in (Person <: personProjects).p 
}
    S7 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all y : Project | some p : Person | y in p.personProjects

}
    S8 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	// all p : Person, ps : Project | ps in p.projects
  	all ps : Project | some p : Person | p in none
}
    S9 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  all s: Student | all p: s.personProjects | some none

}
    S10 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
    Person != Student
	all person: Person | some person.personProjects implies person in Student 
}
    S11 in valid iff {
  all p : Project | (some s : Student | p in s.personProjects)
	// Only students work on projects and 
	// projects must have someone working on them

}
    S12 in valid iff {
  all p : Project, s : Person | (p in s.personProjects implies p in Student)
 // all p : Project | (some s : Student | p in s.projects)
	// Only students work on projects and 
	// projects must have someone working on them

}
    S13 in valid iff {
  all p : Professor | no p.personProjects
 // all p : Project | (some s : Student | p in s.projects)
	// Only students work on projects and 
	// projects must have someone working on them

}
    S14 in valid iff {
  all p : Professor | no p.personProjects
  all p : Person | some p.personProjects implies p in Student
 // all p : Project | (some s : Student | p in s.projects)
	// Only students work on projects and 
	// projects must have someone working on them

}
    S15 in valid iff {
  all p : Professor | no p.personProjects
  all p : Person | some p.personProjects implies p in Student
  all p : Project | (some s : Student | p in s.personProjects)
	// Only students work on projects and 
	// projects must have someone working on them

}
    S16 in valid iff {
  all p : Person | some p.personProjects implies p in Student
  all p : Project | (some s : Student | p in s.personProjects)
  all p : Project, s : Student | some s.personProjects	
  
	// Only students work on projects and 
	// projects must have someone working on them

}
    S17 in valid iff {
	// Only students work on projects and 
  	all p : Person-Professor, x : Project | x in p.personProjects
	// projects must have someone working on them

}
    S18 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Person-Professor, ps : Project | ps in p.personProjects
  	all ps : Project | some p : Person-Professor | ps in p.personProjects 
}
    S19 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all y : Project | some p : Person-Professor | y in  p.personProjects

}
    S20 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Person, ps : Project | ps in p.personProjects
  	all ps : Project | some p : Person | ps in p.personProjects 
}
    S21 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Person-Student | no p.personProjects
  	all p : Project | some s : Person-Professor | p in s.personProjects
}
    S22 in valid iff {
	// Only students work on projects and 
  	all p : Person | some p.enrolled implies p in Student
	// projects must have someone working on them
  all c : Course | some c.courseProjects implies some s : Student | c.courseProjects in s.personProjects 

}
    S23 in valid iff {
	// Only students work on projects and 
  	all p : Person | some p.enrolled implies p in Student
	// projects must have someone working on them
  all c : Course | some c.courseProjects implies some p : Person-Professor | p.personProjects in c.courseProjects 

}
    S24 in valid iff {
	// Only students work on projects and 
  	all p : Person | some p.enrolled implies p in Student
	// projects must have someone working on them
  all c : Course | some c.courseProjects implies some p : Person-Professor | c.courseProjects in p.personProjects 

}
    S25 in valid iff {
	// Only students work on projects and 
  	all p : Person | some p.enrolled implies p in Student
	// projects must have someone working on them
  all c : Course | some c.courseProjects implies some p : Person | c.courseProjects in p.personProjects 

}
    S26 in valid iff {
	// Only students work on projects and 
  	all p : Person | some p.personProjects implies p in Student
	// projects must have someone working on them
  all c : Course | some c.courseProjects implies some p : Person | c.courseProjects in p.personProjects 

}
    S27 in valid iff {
	// Only students work on projects and 
  	all p : Person | some p.personProjects implies p in Student
	// projects must have someone working on them
  	all x : Course | some s : Student | some x.courseProjects implies x.courseProjects in s.personProjects

}
    S28 in valid iff {
	// Only students work on projects and 
  	//all p : Person | some p.projects implies p in Student
	// projects must have someone working on them
  	all x : Course | some s : Student | some x.courseProjects implies x.courseProjects in s.personProjects

}
    S29 in valid iff {
	// Only students work on projects and 
  	all p : Person-Professor | some p.personProjects implies p in Student
	// projects must have someone working on them


}
    S30 in valid iff {
	// Only students work on projects and 
  	all p : Person, c : Course | c in p.enrolled implies c not in p.teaches 
  	all p : Person | some p.personProjects implies p in Student
	// projects must have someone working on them


}
    S31 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  (all p : Project | some s : Student | p in s.personProjects) and no Professor.personProjects

}
    S32 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all p : Project | some c : Course, s : Student | p in c.courseProjects implies p in s.personProjects
}
    S33 in valid iff {
	// Only students work on projects and 
  all p : Professor | no p.personProjects
	// projects must have someone working on them
  	all p : Project | some c : Course, s : Student | p in c.courseProjects implies p in s.personProjects
}
    S34 in valid iff {
	// Only students work on projects and 
  	all p : Person-Student | no p.personProjects
	// projects must have someone working on them
  	all p : Project | some c : Course, s : Student | p in c.courseProjects implies p in s.personProjects
}
    S35 in valid iff {
	// Only students work on projects and 
  	all p : Person-Student | no p.personProjects
	// projects must have someone working on them
  	all p : Project, s : Student | p in s.personProjects
}
    S36 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p:Person | some pj:Project| pj in p.personProjects implies p in Student 
  
  
	
}
    S37 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p:Person | some pj:Project| some(p.personProjects) implies (p in Student)
  
  
	
}
    S38 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Project | all pp : Student | p in pp.personProjects
}
    S39 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all pers:Person | (some pers.personProjects) implies pers in Student
	and
	all p:Project | some pers:Person | p in pers.personProjects

}
    S40 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all p : Project | all s : Person | p in s.personProjects and s in Student

}
    S41 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	
  	// all p.projects implies p in student
  	some p : Person | 
  		all pr : Project |
  			pr in p.personProjects implies p in Student
  	// all project some p.projects

}
    S42 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Person | (all pr : Project | p->pr in personProjects) implies p in Student 
}
    S43 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Project | some pp : Person | p in pp.personProjects implies pp in Student 
}
    S44 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Project | some per : Person | per in personProjects.p and per in Student and per not in Professor
}
    S45 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all x: Person-Student, y: Student | no(x.personProjects) && some y
}
    S46 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Project | some per : Person | per in personProjects.p implies p in Student
}
    S47 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all s: Student, p: Project | one (Person<:personProjects).p //in Student 
}
    S48 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Project | some per : Person | p in per.personProjects implies per in Student and per not in Professor
}
    S49 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all s: Student, p: Project | one (Person<:personProjects).p and (Person<:personProjects).p in Student
}
    S50 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all s: Student, p: Project | one (Person<:personProjects).s
}
    S51 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all s: Student, p: Project | lone s.(Person<:personProjects)
}
    S52 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all s: Student, p: Project | some s.personProjects 
}
    S53 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all p : Project | some per : Person | per in personProjects.p and per not in Professor
	all p : Project | some per : Person | per in personProjects.p and per in Student  
}
    S54 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all per : Person | per in Student implies per not in Professor
	all p : Project | some per : Person | per in personProjects.p and per in (Person-			Professor)  
}
    S55 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all pro:Project | ( some p:Person | p in personProjects.pro implies p in Student) 
	and (some p1:Person | p1 in personProjects.pro)
}
    S56 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all x : Person | some p : Project | x in Student and some none
}
    S57 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  
  	all p:Person | some pro:Project | pro in p.personProjects implies p in Student
  	all proj:Project | some p:Person| proj in p.personProjects

}
    S58 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  all p:Project, person:Person | one Person<:personProjects.p

}
    S59 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  (all p : Project | some s : Student | p in s.personProjects) and no (Professor - Student).personProjects

}
    S60 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Project,  s : Student | p in s.personProjects
  	all p : Project | some p1 : Person | p in p1.personProjects
}
    S61 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
 	some Person:>Project
}
    S62 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	Person :> personProjects.Project in Student and Person :> personProjects.Project not in Professor
  	some(Person :> personProjects.Project)
  
}
    S63 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  all s: Student | some s.(Person <: personProjects)

}
    S64 in valid iff {
	// Only students work on projects and >>>>>>>>>> DONE
	// projects must have someone working on them
	all p : Person | (some pr : Project | p->pr in personProjects) implies p in Student 
	and all pr1 : Project | one p1 : Person | p1 in personProjects.pr1
}
    S65 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  some s : Person - Professor | all p : Project | p in s.personProjects

}
    S66 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  some s : Student | all p : Project | p in s.personProjects

}
    S67 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them

	all p: Project | some s: Student | s.personProjects in p
}
    S68 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them

	some p: Project | some s: Student | s.personProjects in p
}
    S69 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them

	some p: Project | some s: Student | p in s.personProjects
}
    S70 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all s : (Person - Professor) | some s.personProjects
}
    S71 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all p : Person - Student | all pj : Project | p not in personProjects.pj and 
  	all s : Student| some s.personProjects
  	
	
}
    S72 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all p : Person - Student | all pj : Project | p not in personProjects.pj and 
  	some s : Student| s in personProjects.pj
  	
	
}
    S73 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all s : Student, p : Project | p in s.personProjects
  	all p : Project | some s : Student | p in s.personProjects
}
    S74 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all p : Project | (Professor not in Person :> personProjects.p) and some (Person :> personProjects.p)
  	

}
    S75 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all p : Project | (Professor not in Person :> personProjects.p) and some (Student :> personProjects.p)
  	

}
    S76 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all p : Project | (all s:Person | some s.enrolled implies s in Student and  p in s.personProjects)

}
    S77 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	(all p : Project | some s : Student | some s.enrolled implies p in s.personProjects)
	(all p : Project | all t : Professor | p not in t.personProjects)
}
    S78 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	(all p : Project | some s : Person | some s.enrolled implies p in s.personProjects)
	(all p : Project | all t : Professor | p not in t.personProjects)
}
    S79 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	(all p : Project | all s : Person | some s.enrolled implies p in s.personProjects)
	(all p : Project | all t : Professor | p not in t.personProjects)
}
    S80 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all p : Project | some pe : Person | (p in pe.personProjects) implies pe in Student
	all p : Project | some pe : Person | pe.personProjects in p
}
    S81 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all p : Project | some pe : Person | (p in pe.personProjects) implies pe in Student
	all p : Project | some pe : Person | pe.personProjects = p
}
    S82 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Project | some s: Student |s.personProjects=p
}
    S83 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all p: Person | some p.personProjects implies p in Student
  	all p: Project | one person: Person | p in person.personProjects
}
    S84 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all pe : Person, p : Project | p in pe.personProjects implies pe in Student
  	 some pe : Person | all p : Project | p in pe.personProjects 

}
    S85 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them

	some s: Student | all p: Project | p in s.personProjects
	all p: Person | some p.personProjects implies p in Student

}
    S86 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	(all p: Person| some p.personProjects iff p in Student)
}
    S87 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  all p: Project | some pe: Person | p in pe.personProjects
  no  p: Professor | p.personProjects in Project
  
  // CONTINUAR

}
    S88 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all p : Project | all ps : Person| one c : Course | ps in Student and p in ps.personProjects and p in c.courseProjects implies c in ps.enrolled

}
    S89 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all p : Project | some ps : Person| one c : Course | ps in Student and p in ps.personProjects and p in c.courseProjects implies c in ps.enrolled

}
    S90 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all p:Person |
  		some proj:Project|
  			proj in p.personProjects implies p in Student
	
  	all proj:Project|
  		some s:Student |  proj in s.personProjects

}
    S91 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all s: Student | some s.personProjects
  	all p:Project | some ss: Student | p in ss.personProjects
}
    S92 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all pr:Project ,p:Person | p in Student 
}
    S93 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all p : Person, pr : Project | some pr => p in Student
  	all p : Project | some s : Person | p in s.personProjects

}
    S94 in valid iff {
	// Only students work on projects and
	// Projects must have someone working on them
	all x : Person | 
		( // Se uma pessoa está em um projeto, então ela é um estudante
			all p : Project | (p in x.personProjects implies x in Student)
		) and 
		( // Para cada pessoa, deve haver pelo menos um projeto em que ela está trabalhando
			some p : Project | p in x.personProjects
		)
}
    S95 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	
  	// Only students work on projects
    //all prj: Project | prj.projects.enrolled in Student
  	all p : Person - Professor | p.personProjects = none 

    // Projects must have someone working on them
    all p: Person | some p.personProjects
}
    S96 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  all s: Student | lone s.personProjects and some s.personProjects

}
    S97 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  one s: Student | lone s.personProjects and some s.personProjects

}
    S98 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  all s: Person | all p: s.personProjects | p in s.enrolled.courseProjects and some s.personProjects

}
    S99 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  all s: Student | all p: s.personProjects | p in s.enrolled.courseProjects and some s.personProjects

}
    S100 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  all s: Student | all p: s.enrolled | some s.personProjects

}
    S101 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  all s: Student | all p: s.enrolled.courseProjects | some s.personProjects

}
    S102 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  all s: Student | all p: s.enrolled.courseProjects | some none

}
    S103 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
   
    all s: Person | s in Student <=> s.personProjects != none
    all p: Project | some s: Student | s.personProjects = p
	
}
    S104 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
   
    all s: Person | (s in Student <=> s.personProjects != none) and 
     (all p:Project | s.personProjects = p)
	
}
    S105 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
   
    all s: Person | (s not in Student => s.personProjects = none) and 
     (all p:Project | s.personProjects = p)
	
}
    S106 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
   all p: Project |
		(some s: Student | s.personProjects = p) and
		(all s: Person | s in Student <=> s.personProjects != none)
	
}
    S107 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
   all p: Project |
		(some s: Student | s.personProjects = p) and
		(all s: Person | s not in Student => s.personProjects = none)
	
}
    S108 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	// Assuming working is a student being enrolled in a course and that course has 	projects
  
  	(all p : Project, x : Person, c : Course | p in c.courseProjects and c in x.enrolled 			implies x in Student) 
	and
	(all p : Project | some c : Course, x : Student | p in c.courseProjects and c in x.enrolled)
}
    S109 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Project | some x : Student | p in x.personProjects implies x in Student

}
    S110 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Project | some x : Student | p in x.personProjects implies not x in Student

}
    S111 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Project | some x : Student | p in x.personProjects implies not x in Professor

}
    S112 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  
  all s : Person, pr : Project | (some s.(Person<:personProjects)) implies s in Student
	& (Person<:personProjects).pr
}
    S113 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them

  all x: Project | some (Person - Student).personProjects &  Project
}
    S114 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all p: Project | some s: Student | some pr: s.personProjects |
  	(p in pr) implies
  		(some u: Person | pr in u.personProjects) 
  
  		
	
}
    S115 in valid iff {
	// Only students work on projects and
  	all p : Project | (Person <: personProjects).p in Student
	// projects must have someone working on them
	all p : Project | some (Person <: personProjects)
}
    S116 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all pr : Project | one pe : Person | pe not in Professor implies pr in pe.personProjects
}
    S117 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all pr : Project | one pe : Person | pe not in Professor and pr in pe.personProjects
}
    S118 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all pr : Project | one pe : Person | pe in Student implies pr in pe.personProjects
}
    S119 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all x: Person-Student, y: Course | no(x.personProjects) && no(y.courseProjects) && some Student
}
    S120 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all x: Professor, y: Course | no(x.personProjects) && no(y.courseProjects) && some Student
}
    S121 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all p: Project | one person: Person | person in Student and p in person.personProjects
}
    S122 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all p : Project | some pe : Person | pe in Student implies p in pe.personProjects
}
    S123 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  all x : Person - Student | no(x.personProjects)
  all x : Project | some personProjects.x & Professor
  

}
    S124 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p: Person | some pr: Project | p in Student
}
    S125 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all p: Project | one person: Person | some person.personProjects implies person in Student 
}
    S126 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all s: Student | all p: Project | p in s.personProjects and p not in Professor
  	all p: Project | some s:Student | p in s.personProjects
  	all pe: Person - Student | all p: Project | p not in pe.personProjects
	all pro: Project| some p: Person | pro in p.personProjects
}
    S127 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p: Project | one person: Person | p in person.personProjects implies person in Student
}
    S128 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
      // Only students work on projects and 
	 all p : Person | (some pr : Project | p->pr in personProjects) implies p in Professor
    // projects must have someone working on them
	all proj: Project | some s : Student | proj in s.personProjects

}
    S129 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Person - Student | all pr: Project | pr in p.personProjects
}
    S130 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all s: Student | some p : Project | s in personProjects.p and all x:Person | x
 in personProjects.p implies x in Student

}
    S131 in valid iff {
	// Only students work on projects and 
	// projects must have someone 
  all s: Person, p:Project | s->p in (Person <: personProjects) implies s in Student and one (Person <: personProjects).p

}
    S132 in valid iff {
	// Only students work on projects and 
	// projects must have someone 
  all s: Person, p:Project | s in Student and one (Person <: personProjects).p

}
    S133 in valid iff {
	// Only students work on projects and 
	// projects must have someone 
  all s: Person, p:Project | !( s in Professor and one (Person <: personProjects).p)

}
    S134 in valid iff {
	// Only students work on projects and 
  
  
  all p : Project | lone ( Person <: personProjects).p 
  
	// projects must have someone working on them
  
  
  

}
    S135 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all x: Student | some p: Project | (Person <: personProjects).p in x.(Person <: personProjects)
}
    S136 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all p: Person | (all pr: Project | (p->pr) in (Person<:personProjects)) implies p in Student
  	
    //(Person<:projects) in Student -> Project
  	all p: Project | some (Person<:personProjects).p
  	
  	
}
    S137 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all p: Person | (all pr: Project | (p->pr) in (Person<:personProjects)) implies p in Student
	all p: Person | all pr: Project | (p->pr) in (Person<:personProjects) implies p in Student
  	
    //(Person<:projects) in Student -> Project
  	all p: Project | some (Person<:personProjects).p
  	
  	
}
    S138 in valid iff {
	// Only students work on projects and 
	all c: Course, P: Person | Project in P.personProjects implies P in Student	
  // projects must have someone working on them
	
}
    S139 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	some s : Person | all p : Project | (s in none) implies (s in Student)

}
    S140 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  
  all p : Person | p.(Person <:personProjects) in Student  iff some p.(Person <: personProjects) & Student
  

}
    S141 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  all p: Project | (Person <: personProjects) in Student -> p

}
    S142 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  
  all p : Person , pro : Project | (Person <:personProjects).pro in Student  iff some p.(Person <: personProjects) & Student
  

}
    S143 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  
  all p : Person , pro : Project | (Person <:personProjects).pro in Student  iff some (Person <: personProjects).pro & Student
  

}
    S144 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  
  all  pro : Project | (Person <:personProjects).pro in Student  iff no (Person <: personProjects).pro & Professor
  

}
    S145 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p:Project | some pe:Person | p in pe.personProjects
  all pe:Person | some p:Project | p in pe.personProjects implies pe in Person
}
    S146 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p:Project | some pe:Student | p in pe.personProjects
  all pe:Person | some p:Project | p in pe.personProjects implies pe in Person
}
    S147 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  all p : Project | some Person-Professor <: personProjects.p

}
    S148 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all pe: Person - Student | some p: Project | p not in pe.personProjects
	all p: Person | all pro: Project | pro in p.personProjects
}
    S149 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p: Project | lone (Student <: personProjects).p
}
    S150 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p: Person | p.personProjects in Project implies p in Student
  	all p: Project | one s: Student | p in s.personProjects
}
    S151 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p: Person | p.personProjects in Project implies p in Student
  	all p: Project | lone s: Student | p in s.personProjects
}
    S152 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
 	//all p : Project | some (Student <: projects)
  	all p : Person  | p.personProjects in Project implies p in Student
  	all p : Project | some 	(Student <: personProjects).p
  	

}
    S153 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  
	all proj : Project | some per : Person | proj in per.personProjects implies per in Student 
  	all proj : Project | some per : Person | some per.personProjects implies per in Student
}
    S154 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  
	all proj : Project | some per : Person | proj in per.personProjects implies per in Student 
    all proj : Project | proj in Person.personProjects implies Person in Student
}
    S155 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  
	all proj : Project | some per : Person | some proj implies per in Student 
    all proj : Project | proj in Person.personProjects implies Person in Student
}
    S156 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
      Student.personProjects = Person.(personProjects & (Person->Project))


}
    S157 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
      lone (Student.personProjects) and Student.personProjects = Person.(personProjects & (Person->Project))


}
    S158 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
      lone (Person.personProjects) and (Student - Professor).personProjects = Person.(personProjects & (Person->Project))


}
    S159 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
      lone (Person.personProjects) and (personProjects.Project & Person) in Student


}
    S160 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Project | Person.personProjects in p implies Person in Student
}
    S161 in valid iff {
	// Only students work on projects and 
  all x:Person, p:Project | x in Student implies p in x.personProjects
  all p : Project | lone (Person <: personProjects).p

	// projects must have someone working on them

}
    S162 in valid iff {
	// Only students work on projects and 
  all x:Person, p:Project | x in Student implies p in x.personProjects
  all p : Project | lone (Student <: personProjects).p

	// projects must have someone working on them

}
    S163 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  all x:Person | x in Student implies some x.personProjects
  all x:Professor, c:Course, p:Project | c in x.teaches implies p not in x.personProjects}
    S164 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  all p : Person | (some p.enrolled) implies p in Student and one none 

}
    S165 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Project | no (p & (Person-Professor).personProjects)
}
    S166 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them

  all pr : Project | some (Person <: personProjects).pr implies some Person & Student 
  all pr : Project | some (Person <: personProjects).pr
}
    S167 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
 	//all p : Project | some (Student <: projects)
  	all p : Person  | p.personProjects in Project implies p in Student
  	

}
    S168 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
 	//all p : Project | some (Student <: projects)
  	all p : Person  | p.personProjects in Project implies p in Student
  	all p : Project | some 	Student.personProjects 
  	

}
    S169 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p: Project | all ps: Person | (p in ps.personProjects) implies no (ps & Professor)
	all p: Project | one s: Student | p in s.personProjects

}
    S170 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all p: Person, p1: Project | p1 in p.personProjects implies p not in Professor 
  	some (Person <: personProjects).Project

}
    S171 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all p: Person, p1: Project | p1 in p.personProjects implies p not in Student 
  	some (Person <: personProjects).Project

}
    S172 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  	all p: Person, p1: Project | p1 in p.personProjects implies p not in Student 
  	all p: Project | some (Person <: personProjects).p

}
    S173 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Person | Student not in p implies no p.personProjects
  	all p : Project | some pe : Person & Student | p in pe.personProjects 
}
    S174 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Person | #(p.personProjects) > 0 implies p = Student 
  	//all pr : Project | some s : Student | pr in s.projects
}
    S175 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Person | #(p.personProjects) > 0 implies p = Student and p not in Professor
  	all pr : Project | some s : Student | pr in s.personProjects
}
    S176 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Person | #(p.personProjects) > 0 and p not in Professor implies p = Student 
  	all pr : Project | some s : Student | pr in s.personProjects
}
    S177 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Person | #(p.personProjects) > 0 and p not in Professor iff p = Student 
  	all pr : Project | some s : Student | pr in s.personProjects
}
    S178 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Person | #(p.personProjects) > 0 and p not in Professor implies p = Student 
  	//all pr : Project | some s : Student | pr in s.projects
}
    S179 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Person | #(p.personProjects) > 0 and p not in Professor implies p = Student 
  	all pr : Project | some s : Person | pr in s.personProjects
}
    S180 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Person | #(p.personProjects) > 0 and p not in Professor implies p = Student 
  	all pr : Project | some s : Person | pr in s.personProjects and s not in Professor
}
    S181 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	some s : Student | all p : Project | s.personProjects in p
}
    S182 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	some t : Professor | some s : Student | all p : Project | s.personProjects in p and t + s in p
}
    S183 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	some t : Professor | some s : Student | all p : Project | s.personProjects in p and (t + s).personProjects in p
}
    S184 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	some p : Person | some s : Student | all p : Project | s.personProjects in p and p in none  
}
    S185 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	some p : Person | some s : Student | all pj : Project | s.personProjects in pj and pj in p.personProjects  
}
    S186 in valid iff {
	// Only students work on projects and 
  all p: Project, s: Person | s in personProjects.p implies s in Student
	// projects must have someone working on them
	all p: Project | some pe: Person | pe.enrolled in courseProjects.p
}
    S187 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Person | Student not in p implies no p.personProjects
  	all p : Project | some Course.courseProjects:>p
}
    S188 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Person | Student not in p implies no p.personProjects
  	all p : Project | some pe : Person | p in pe.personProjects 
}
    S189 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p : Person | Student not in p implies no p.personProjects
  	all p : Project | some pe : Person | Student in pe implies p in pe.personProjects 
}
    S190 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p: Project | some personProjects[Person]
}
    S191 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	some p : Person | all pr : Project | pr in p.personProjects
}
    S192 in valid iff {
	// Only students work on projects and 
  	all p: Project, y: Person | y->p in personProjects implies y in Student
	// projects must have someone working on them
	//all p: Project| some y: Person | some projects.p 
  	some y: Person | some Project implies y in Project
}
    S193 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p: Project, s: Student | some s.enrolled implies p in Student
}
    S194 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  all p: Project | some s : Person | p in s.personProjects iff s in Student

}
    S195 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
  all p: Project | some s : Person | p in s.personProjects iff s in Student
  
  all p: Project | some per : Person | p in per.personProjects

}
    S196 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p: Person | some p.personProjects implies p in Student
    and
    all p: Project | some per: Person - Professor | p in per.personProjects
}
    S197 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p: Person | some p.personProjects implies p in Student
    and
    all p: Person | some p.personProjects
}
    S198 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p: Person | some p.personProjects implies p in Student
    and
    all p: Project | some per: Person | some per.personProjects implies p in per.personProjects
}
    S199 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p: Person | some p.personProjects implies p in Student
    and
    all p: Project | some s: Student | some s.personProjects implies p in s.personProjects

}
    S200 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p: Person | some p.personProjects implies p in Student
    and
    all p: Project | some s: Student | p in s.personProjects and some c: Course | p in c.courseProjects and c in s.enrolled
}
    S201 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p: Person | some p.personProjects implies p in Student
    and
    all p: Project | some s: Student | some c: Course | p in c.courseProjects implies p in s.personProjects 
}
    S202 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	all p: Person | some p.personProjects implies p not in Professor
    and
    all p: Project | some s: Student | p in s.personProjects
}
    S203 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	Student <: personProjects in Student some -> one Project
}
    S204 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	Student <: personProjects in Student -> one Project
	Person  <: personProjects in Person some -> Project
}
    S205 in valid iff {
	// Only students work on projects and 
	// projects must have someone working on them
	// Only students work on projects and 
	// projects must have someone working on them
	Student <: personProjects in Student -> one Project
	Professor  <: personProjects in Professor some -> Project
}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, S74, S75, S76, S77, S78, S79, S80, S81, S82, S83, S84, S85, S86, S87, S88, S89, S90, S91, S92, S93, S94, S95, S96, S97, S98, S99, S100, S101, S102, S103, S104, S105, S106, S107, S108, S109, S110, S111, S112, S113, S114, S115, S116, S117, S118, S119, S120, S121, S122, S123, S124, S125, S126, S127, S128, S129, S130, S131, S132, S133, S134, S135, S136, S137, S138, S139, S140, S141, S142, S143, S144, S145, S146, S147, S148, S149, S150, S151, S152, S153, S154, S155, S156, S157, S158, S159, S160, S161, S162, S163, S164, S165, S166, S167, S168, S169, S170, S171, S172, S173, S174, S175, S176, S177, S178, S179, S180, S181, S182, S183, S184, S185, S186, S187, S188, S189, S190, S191, S192, S193, S194, S195, S196, S197, S198, S199, S200, S201, S202, S203, S204, S205 extends Formula {}

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
    #valid.Oracle = 4
    #(Instance - valid.Oracle) = 4
    detected = { f : Formula - Oracle | valid.f != valid.Oracle }
    maxsome detected
} for exactly 16 Atom, exactly 4 PersonAtom, exactly 4 CourseAtom, exactly 4 ProjectAtom, exactly 4 GradeAtom,
       exactly 8 Instance, 8 Int
