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
    // Earlier requirement 13, required in every Instance.
{
	// A student cannot work with the same student in different projects
	all disj a, b : Student | lone a.personProjects & b.personProjects
}
    Oracle in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	all c : Course, p : c.courseProjects | no disj a, b : (Person <: personProjects).p, ga : c.(instanceGrades[this])[a], gb : c.(instanceGrades[this])[b] | (order_gt[this, ga, gb.(order_next[this])])
}
    S1 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit

}
    S2 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  all c: Course, disj s1,s2: Student , g1: s1.(c.(instanceGrades[this])) , g2 : s2.(c.(instanceGrades[this])) | some (s1.personProjects & s2.personProjects & c.courseProjects) 
  implies g1 in g2.(order_next[this]) + g2.(order_prev[this])

}
    S3 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	all s,s2: Student , p : s.personProjects & s2.personProjects, c : Course | p in c.courseProjects implies (order_next[this])[s.(c.(instanceGrades[this]))]  = s2.(c.(instanceGrades[this])) or (order_next[this])[s2.(c.(instanceGrades[this]))] = s.(c.(instanceGrades[this])) or s.(c.(instanceGrades[this])) = s2.(c.(instanceGrades[this]))
}
    S4 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  	all disj s1,s2 : Student | all p :s1.personProjects & s2.personProjects | s1.((Course <: courseProjects.p).(instanceGrades[this])) = s2.((Course <: courseProjects.p).(instanceGrades[this]))

/*
sig Person {
	teaches : set Course,
	enrolled : set Course,
	projects : set Project
}

sig Professor,Student in Person {}

sig Course {
	projects : set Project,
	grades : Person -> Grade
}

sig Project {}

sig Grade {}
*/
  }
    S5 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  	all disj s1,s2 : Student | all p :s1.personProjects & s2.personProjects | s1.((Course <: courseProjects.p).(instanceGrades[this])) = s2.((Course <: courseProjects.p).(instanceGrades[this])) or s1.((Course <: courseProjects.p).(instanceGrades[this])).(order_next[this]) = s2.((Course <: courseProjects.p).(instanceGrades[this])) or s1.((Course <: courseProjects.p).(instanceGrades[this])) = s2.((Course <: courseProjects.p).(instanceGrades[this])).(order_next[this]) and one(s2.((Course <: courseProjects.p).(instanceGrades[this]))) and one(s1.((Course <: courseProjects.p).(instanceGrades[this])))

/*
sig Person {
	teaches : set Course,
	enrolled : set Course,
	projects : set Project
}

sig Professor,Student in Person {}

sig Course {
	projects : set Project,
	grades : Person -> Grade
}

sig Project {}

sig Grade {}
*/
  }
    S6 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	// all p1 : Student, p2 : Student, project : p1.projects & p2.projects => project.grades.p1  
  all p : Student, p1 : Student & personProjects.(p.personProjects) | no p
}
    S7 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  all s1, s2 : Student, p : Project, c: Course | s1 != s2 and p in s1.personProjects and p in s2.personProjects and p in c.courseProjects implies (all g1, g2 : Grade | g1 in s1.(c.(instanceGrades[this])) and g2 in s2.(c.(instanceGrades[this])) implies (g1 = g2 or g1 = g2 + 1 or g1 + 1 = g2))

}
    S8 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit  
	all disj s, s1 : Student | some c : Course | some p : c.courseProjects | p in (s.personProjects & s1.personProjects) and (s.(c.(instanceGrades[this]))).(order_next[this]) = s1.(c.(instanceGrades[this]))
}
    S9 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit  
	all disj s, s1 : Student | some c : Course | some p : c.courseProjects | p in (s.personProjects & s1.personProjects) and ((s.(c.(instanceGrades[this]))).(order_next[this]) = s1.(c.(instanceGrades[this])) || (s1.(c.(instanceGrades[this]))).(order_next[this]) = s.(c.(instanceGrades[this])) || s1.(c.(instanceGrades[this])) = s.(c.(instanceGrades[this])))
}
    S10 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit  
	all disj s, s1 : Student | some c : Course | some p : c.courseProjects | p in (s.personProjects & s1.personProjects) => ((s.(c.(instanceGrades[this]))).(order_next[this]) = s1.(c.(instanceGrades[this])) || (s1.(c.(instanceGrades[this]))).(order_next[this]) = s.(c.(instanceGrades[this])) || s1.(c.(instanceGrades[this])) = s.(c.(instanceGrades[this])))
}
    S11 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	all c: Course | all p: c.courseProjects |
		 all disj x, y: (Person <: personProjects).p | not (order_lt[this, x.(c.(instanceGrades[this])), y.(c.(instanceGrades[this])).(order_next[this])]) and not (order_lt[this, x.(c.(instanceGrades[this])), y.(c.(instanceGrades[this])).(order_prev[this])])
}
    S12 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	all c: Course | all p: c.courseProjects |
		 all disj x, y: (Person <: personProjects).p | 
		 	some x.(c.(instanceGrades[this])) and some y.(c.(instanceGrades[this])) => 
		 	not (order_lt[this, x.(c.(instanceGrades[this])), y.(c.(instanceGrades[this])).(order_next[this])]) and not (order_lt[this, x.(c.(instanceGrades[this])), y.(c.(instanceGrades[this])).(order_prev[this])])
}
    S13 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	all c: Course | all p: c.courseProjects |
		 all disj x, y: (Person <: personProjects).p | 
		 	some x.(c.(instanceGrades[this])) and some y.(c.(instanceGrades[this])) => 
		 	not (order_lt[this, x.(c.(instanceGrades[this])), y.(c.(instanceGrades[this])).(order_prev[this])]) and not (order_lt[this, x.(c.(instanceGrades[this])).(order_prev[this]), y.(c.(instanceGrades[this]))])
}
    S14 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  all disj s1,s2 : Student | 
  	lone p : Project |
  		all c:Course | 
  			p in c.courseProjects implies(
  				(p in s1.personProjects and p in s2.personProjects) implies (c.(instanceGrades[this])[s1].(order_prev[this]) = c.(instanceGrades[this])[s2] or c.(instanceGrades[this])[s2].(order_prev[this]) = c.(instanceGrades[this])[s1] or c.(instanceGrades[this])[s2]=c.(instanceGrades[this])[s1])
  
  
  	)
}
    S15 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  all c: Course |
  all p : c.courseProjects |
  all disj s1,s2: (personProjects.p & Student) | 
  	c.(instanceGrades[this])[s1].(order_prev[this]) = c.(instanceGrades[this])[s2] or c.(instanceGrades[this])[s2].(order_prev[this]) = c.(instanceGrades[this])[s1] or c.(instanceGrades[this])[s1] = c.(instanceGrades[this])[s2] 
  
}
    S16 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  	all disj s1, s2 : Student, c : Course, p : Project | some s1.personProjects & s2.personProjects & c.courseProjects implies one (s1.(c.(instanceGrades[this])) - s2.(c.(instanceGrades[this])))

}
    S17 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  all p: Project | all s1, s2: (Person<:personProjects).p | 
  		let g1 = s1.(Course.(instanceGrades[this])) |
  		let g2 = s2.(Course.(instanceGrades[this])) |
  		all g11: g1, g22: g2 | g11.(order_prev[this]) in g22 or g11.(order_next[this]) in g22

}
    S18 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  all p: Project | all s1, s2: (Person<:personProjects).p | 
  		let g1 = s1.(Course.(instanceGrades[this])) |
  		let g2 = s2.(Course.(instanceGrades[this])) |
  		all g11: g1, g22: g2 | g11.(order_prev[this]) = g22 or g11.(order_next[this]) = g22

}
    S19 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  all p: Project | all s1, s2: (Person<:personProjects).p | 
  		s1 != s2 implies
  		let g1 = s1.(Course.(instanceGrades[this])) |
  		let g2 = s2.(Course.(instanceGrades[this])) |
  		all g11: g1, g22: g2 | g11.(order_prev[this]) = g22 or g11.(order_next[this]) = g22

}
    S20 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  all p: Project | all s1, s2: (Person<:personProjects).p | 
  		s1 != s2 implies
  		let g1 = s1.(Course.(instanceGrades[this])) |
  		let g2 = s2.(Course.(instanceGrades[this])) |
  		all g11: g1, g22: g2 | g11.(order_prev[this]) = g22 or g11.(order_next[this]) = g22 or g11 = g22

}
    S21 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  	all disj s1,s2 : Student | some c : Course | 
  		(c in s1.enrolled&s2.enrolled and some c.courseProjects) implies 
		(c.(instanceGrades[this])[s1].(order_next[this]) = c.(instanceGrades[this])[s2] or c.(instanceGrades[this])[s1].(order_prev[this]) = c.(instanceGrades[this])[s2] )

}
    S22 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  	all disj s1,s2 : Student | some c : Course | 
  		(c in s1.enrolled&s2.enrolled) implies 
		(c.(instanceGrades[this])[s1].(order_next[this]) = c.(instanceGrades[this])[s2] or c.(instanceGrades[this])[s1].(order_prev[this]) = c.(instanceGrades[this])[s2] )

}
    S23 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  	all disj s1,s2 : Student | all c : Course | 
  		(c in s1.enrolled&s2.enrolled) implies 
		(c.(instanceGrades[this])[s1].(order_next[this]) = c.(instanceGrades[this])[s2] or c.(instanceGrades[this])[s1].(order_prev[this]) = c.(instanceGrades[this])[s2] )

}
    S24 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  	all disj s1,s2 : Student | one c : Course | 
  		(c in s1.enrolled&s2.enrolled) implies 
		(c.(instanceGrades[this])[s1].(order_next[this]) = c.(instanceGrades[this])[s2] or c.(instanceGrades[this])[s1].(order_prev[this]) = c.(instanceGrades[this])[s2] )

}
    S25 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  	all s1,s2 : Student | all c : Course | 
  		(c in s1.enrolled&s2.enrolled) implies 
		(c.(instanceGrades[this])[s1].(order_next[this]) = c.(instanceGrades[this])[s2] or c.(instanceGrades[this])[s1].(order_prev[this]) = c.(instanceGrades[this])[s2] )

}
    S26 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  	all disj s1,s2 : Student | all c : Course, p : c.courseProjects | 
  		(c in s1.enrolled&s2.enrolled 
          and (some p&(s1.personProjects&s2.personProjects))) implies 
		(c.(instanceGrades[this])[s1].(order_next[this]) = c.(instanceGrades[this])[s2] or c.(instanceGrades[this])[s1].(order_prev[this]) = c.(instanceGrades[this])[s2] )

}
    S27 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  	all disj s1,s2 : Student | all c : Course, p : Project | 
  		(c in s1.enrolled&s2.enrolled 
          and ( p in (s1.personProjects&s2.personProjects))) implies 
		(c.(instanceGrades[this])[s1].(order_next[this]) = c.(instanceGrades[this])[s2] or c.(instanceGrades[this])[s1].(order_prev[this]) = c.(instanceGrades[this])[s2] )

}
    S28 in valid iff {
  	all c : Course | all project : c.courseProjects | all disj p1, p2 : Person <: personProjects.project | (order_gte[this, p1.(c.(instanceGrades[this])), -1 + p2.(c.(instanceGrades[this]))]) or (order_lte[this, p1.(c.(instanceGrades[this])), 1 + p2.(c.(instanceGrades[this]))])
}
    S29 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  all p:Project, disj s1,s2: Person<:personProjects.p | 
  (s1.((courseProjects.p).(instanceGrades[this]))) in (s2.((courseProjects.p).(instanceGrades[this]))).(order_prev[this])
	
}
    S30 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	all s1,s2 :Student | all p1:s1.personProjects | all p2:s2.personProjects | all c:Course |
  		 p1 = p2 and s1 != s2 and p1 in c.courseProjects implies c.(instanceGrades[this])[s1] - c.(instanceGrades[this])[s2] = 1 or c.(instanceGrades[this])[s2] - c.(instanceGrades[this])[s1] = 1 or c.(instanceGrades[this])[s1] - c.(instanceGrades[this])[s2] = 0
}
    S31 in valid iff {
  	//all c : Course | all project : c.projects | all disj p1, p2 : Person <: projects.project | gte[p1.(c.grades), -1 + p2.(c.grades)] or lte[p1.(c.grades), 1 + p2.(c.grades)]
  all c: Course | all p: c.courseProjects | all disj p1,p2: Person<:personProjects.p | all g1:p1.(c.(instanceGrades[this])), g2:p2.(c.(instanceGrades[this])) | (order_lte[this, g1, g2+1]) or (order_lte[this, g2, g1+1])
}
    S32 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  	all disj s1,s2 : Student | some c : Course | some p : Project | p in s1.personProjects & s2.personProjects and p in c.courseProjects implies c.(instanceGrades[this])[s1] = c.(instanceGrades[this])[s2] - 1

}
    S33 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	all c : Course, p : c.courseProjects, s1, s2 : Student | (p in (s1.personProjects & s2.personProjects)) implies lone (order_prevs[this, s1.(c.(instanceGrades[this]))]) - (order_prevs[this, s2.(c.(instanceGrades[this]))])
}
    S34 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  	//next[x] function finds the next item (in this case Grade) in the set (in line 1 Grade is defined as having the Ordering property, which means each item has an order so you can find the next one)
	all disj s,s2: Student |
  		all c : s.enrolled & s2.enrolled | 
  
  				some s.(c.(instanceGrades[this])) and some s2.(c.(instanceGrades[this])) implies
  					((order_next[this])[s.(c.(instanceGrades[this])) ] = s2.(c.(instanceGrades[this])) or
                     (order_next[this])[s2.(c.(instanceGrades[this]))] = s.(c.(instanceGrades[this])) or
                      s.(c.(instanceGrades[this])) = s2.(c.(instanceGrades[this])))
}
    S35 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	all s1, s2: Student, c: Course | (s1.personProjects & s2.personProjects) in c.courseProjects implies s1.(c.(instanceGrades[this])) = s2.(c.(instanceGrades[this])) or (order_next[this])[s1.(c.(instanceGrades[this]))] = s2.(c.(instanceGrades[this])) or s1.(c.(instanceGrades[this])) = (order_next[this])[s2.(c.(instanceGrades[this]))]
}
    S36 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
		all s1, s2: Student, c: (s1.enrolled & s2.enrolled) | (s1.personProjects & s2.personProjects) in c.courseProjects implies s1.(c.(instanceGrades[this])) = s2.(c.(instanceGrades[this])) or (order_next[this])[s1.(c.(instanceGrades[this]))] = s2.(c.(instanceGrades[this])) or s1.(c.(instanceGrades[this])) = (order_next[this])[s2.(c.(instanceGrades[this]))]

}
    S37 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
		all s1, s2: Student, c: (s1.enrolled & s2.enrolled) | (s1.personProjects & s2.personProjects) in c.courseProjects and some s1.(c.(instanceGrades[this])) and some s2.(c.(instanceGrades[this])) implies s1.(c.(instanceGrades[this])) = s2.(c.(instanceGrades[this])) or (order_next[this])[s1.(c.(instanceGrades[this]))] = s2.(c.(instanceGrades[this])) or s1.(c.(instanceGrades[this])) = (order_next[this])[s2.(c.(instanceGrades[this]))]

}
    S38 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	all s1, s2: Student, c: Course | 
  		s1.personProjects & s2.personProjects in c.courseProjects
  		implies (
  		s1.(c.(instanceGrades[this])) = s2.(c.(instanceGrades[this]))+1 or
  		s1.(c.(instanceGrades[this])) = s2.(c.(instanceGrades[this])) or
  		s1.(c.(instanceGrades[this])) = s2.(c.(instanceGrades[this]))-1)
}
    S39 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  	all c : Course, disj x,y : Student |
	  (lone c.courseProjects & x.personProjects & y.personProjects) implies c.(instanceGrades[this])[x] in c.(instanceGrades[this])[y].((order_prev[this])+((this.@Person + this.@Course + this.@Project + this.@Grade + Int + String + OrderingAtom) <: iden)+(order_next[this]))

}
    S40 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	all s1, s2: Student | all c: Course |
        (c in s1.enrolled and c in s2.enrolled and some (s1.personProjects & s2.personProjects)) implies
        let g1 = c.(instanceGrades[this])[s1], g2 = c.(instanceGrades[this])[s2] |
        g1 = g2 or g1 = (order_next[this])[g2] or g2 = (order_next[this])[g1]
}
    S41 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	all s1, s2 : Student |
		some c : Course |
			some (c.courseProjects & s1.personProjects & s2.personProjects) implies
				c.(instanceGrades[this])[s1] = c.(instanceGrades[this])[s2]	
}
    S42 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	all s1, s2 : Student |
		some c : Course |
			some (c.courseProjects & s1.personProjects & s2.personProjects) implies
				c.(instanceGrades[this])[s1] = c.(instanceGrades[this])[s2] or c.(instanceGrades[this])[s1] = (order_next[this])[c.(instanceGrades[this])[s2]] or c.(instanceGrades[this])[s2] = (order_next[this])[c.(instanceGrades[this])[s1]]
}
    S43 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	all disj s1, s2 : Student |
		some c : Course |
			some (c.courseProjects & s1.personProjects & s2.personProjects) implies
				c.(instanceGrades[this])[s1] = c.(instanceGrades[this])[s2] or c.(instanceGrades[this])[s1] = (order_next[this])[c.(instanceGrades[this])[s2]] or c.(instanceGrades[this])[s2] = (order_next[this])[c.(instanceGrades[this])[s1]]
}
    S44 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	all s1, s2 : Student |
		some c : Course |
			some (c.courseProjects & s1.personProjects & s2.personProjects) implies
				c.(instanceGrades[this])[s1] = c.(instanceGrades[this])[s2] or c.(instanceGrades[this])[s1] = (order_next[this])[c.(instanceGrades[this])[s2]] or c.(instanceGrades[this])[s1] = (order_prev[this])[c.(instanceGrades[this])[s2]]
}
    S45 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	all c: Course | all p: Project | all disj s1, s2: Student | 
  		p in s1.personProjects and
  		p in s2.personProjects and
  		p in c.courseProjects implies
  		(
          c.(instanceGrades[this])[s1] = c.(instanceGrades[this])[s2].(order_next[this]) or
          c.(instanceGrades[this])[s2] = c.(instanceGrades[this])[s1].(order_next[this])
        )
  
  
//    all c: Course | all p: Project | 
//            p in c.projects implies all disj s1, s2: Student | 
//                (s1 in p.projects and s2 in p.projects) implies (
//                c.grades[s1] = c.grades[s2].next or c.grades[s2] = c.grades[s1].next)
}
    S46 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	all disj s1, s2 : Student, c : Course | one p : Project | p in s1.personProjects & s2.personProjects and p in c.courseProjects implies s1.(c.(instanceGrades[this])) in s2.(c.(instanceGrades[this])).((order_prev[this]) + ((this.@Person + this.@Course + this.@Project + this.@Grade + Int + String + OrderingAtom) <: iden) + (order_next[this]))
}
    S47 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	all disj s1, s2 : Student | one c : Course, p : Project | p in s1.personProjects & s2.personProjects and p in c.courseProjects implies s1.(c.(instanceGrades[this])) in s2.(c.(instanceGrades[this])).((order_prev[this]) + ((this.@Person + this.@Course + this.@Project + this.@Grade + Int + String + OrderingAtom) <: iden) + (order_next[this]))
}
    S48 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	all disj s1, s2 : Student | one c : Course | one s1.personProjects & s2.personProjects & c.courseProjects implies s1.(c.(instanceGrades[this])) in s2.(c.(instanceGrades[this])).((order_prev[this]) + ((this.@Person + this.@Course + this.@Project + this.@Grade + Int + String + OrderingAtom) <: iden) + (order_next[this]))
}
    S49 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	all s, s1: Student | all p: Project | all c: Course | s != s1 and  p in s.personProjects and p in s1.personProjects and p in c.courseProjects and some s.(c.(instanceGrades[this])) and some s.(c.(instanceGrades[this])) implies ( (order_next[this])[s1.(c.(instanceGrades[this]))] = s.(c.(instanceGrades[this])) or not (order_next[this])[s.(c.(instanceGrades[this]))] = s1.(c.(instanceGrades[this])) or  s.(c.(instanceGrades[this])) = s1.(c.(instanceGrades[this])) )

}
    S50 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  all s,s2: Student | all p : Project | p in s.personProjects and p in s2.personProjects and  all c : Course |   p in c.courseProjects and some s.(c.(instanceGrades[this])) and some s2.(c.(instanceGrades[this])) implies 
  	((order_next[this])[s.(c.(instanceGrades[this]))]  = s2.(c.(instanceGrades[this])) or (order_next[this])[s2.(c.(instanceGrades[this]))] = s.(c.(instanceGrades[this])) 
   	or s.(c.(instanceGrades[this])) = s2.(c.(instanceGrades[this])))
}
    S51 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	all p : Project | all m : (enrolled.((Course <: courseProjects).p)).(((Course <: courseProjects).p).(instanceGrades[this])) | some m2 : (enrolled.((Course <: courseProjects).p)).(((Course <: courseProjects).p).(instanceGrades[this])) | (order_next[this])[m] = m2 or (order_prev[this])[m] = m2
}
    S52 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  some p:Project | all s1,s2:Student | s1+s2 in personProjects.p => 
  (s1.((courseProjects.p).(instanceGrades[this]))) in (s2.((courseProjects.p).(instanceGrades[this]))).(order_prev[this])
	
}
    S53 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  all p:Project, s1,s2:Student | s1+s2 in personProjects.p => 
  (s1.((courseProjects.p).(instanceGrades[this]))) in (s2.((courseProjects.p).(instanceGrades[this]))).(order_prev[this])
	
}
    S54 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  all p:Project, disj s1,s2: Person <: personProjects.p | 
  (s1.(Course.(instanceGrades[this]))) + (s2.(Course.(instanceGrades[this]))) in (s2.(Course.(instanceGrades[this]))).(order_prev[this]) + (s1.(Course.(instanceGrades[this]))).(order_prev[this])
}
    S55 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  all p:Project, disj s1,s2: Person <: personProjects.p | 
  (s1.(Course.(instanceGrades[this]))) in (s2.(Course.(instanceGrades[this]))).(order_prev[this]) or (s2.(Course.(instanceGrades[this]))) in (s1.(Course.(instanceGrades[this]))).(order_prev[this])
}
    S56 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  all p:Project, disj s1,s2: Person <: personProjects.p | 
  (s1.(Course.(instanceGrades[this]))) in ((s2.(Course.(instanceGrades[this]))).(order_prev[this]) + (s2.(Course.(instanceGrades[this]))))
}
    S57 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  all p:Project, disj s1,s2: Person <: personProjects.p | 
  (s1.(Course.(instanceGrades[this]))) in 
  ( (s2.(Course.(instanceGrades[this])).(order_prev[this])) + s2.(Course.(instanceGrades[this])) + (s2.(Course.(instanceGrades[this])).(order_next[this])) )
}
    S58 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  all p:Project, disj s1,s2: Person <: personProjects.p | some s2.(Course.(instanceGrades[this])) =>
  (s1.(Course.(instanceGrades[this]))) in s2.(Course.(instanceGrades[this])).((order_prev[this]) + ((this.@Person + this.@Course + this.@Project + this.@Grade + Int + String + OrderingAtom) <: iden) + (order_next[this])) 
}
    S59 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  some p:Project, disj s1,s2: Person <: personProjects.p | some s2.(Course.(instanceGrades[this])) =>
  (s1.(Course.(instanceGrades[this]))) in s2.(Course.(instanceGrades[this])).((order_prev[this]) + ((this.@Person + this.@Course + this.@Project + this.@Grade + Int + String + OrderingAtom) <: iden) + (order_next[this])) 
}
    S60 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  all p:Project, disj s1,s2: Student <: personProjects.p |
  	some s2.((courseProjects.p).(instanceGrades[this])) =>
  		(s1.(Course.(instanceGrades[this]))) in s2.(Course.(instanceGrades[this])).((order_prev[this]) + ((this.@Person + this.@Course + this.@Project + this.@Grade + Int + String + OrderingAtom) <: iden) + (order_next[this])) 
}
    S61 in valid iff {
    // Students working on the same project in a course cannot have marks differing by more than one unit
    all disj s1, s2: Student | 
        some p: s1.personProjects & s2.personProjects | 
            all c: Course | 
                p in c.courseProjects => 
                    s1.(instanceGrades[this])[c] = s2.(instanceGrades[this])[c] or 
                    s1.(instanceGrades[this])[c] in none or 
                    s2.(instanceGrades[this])[c] in none
}
    S62 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	all disj s1, s2 : Student, c : Course, p : Project | 
  		p in (s1.personProjects & s2.personProjects & c.courseProjects) implies
  			some s1.(c.(instanceGrades[this])) and 
  			some s2.(c.(instanceGrades[this])) and
  			s1.(c.(instanceGrades[this])) in (s2.(c.(instanceGrades[this])).((order_prev[this]) + ((this.@Person + this.@Course + this.@Project + this.@Grade + Int + String + OrderingAtom) <: iden) + (order_next[this])))
}
    S63 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
  
  all disj x,y:Student, c:Course | one p : x.personProjects & y.personProjects| x->c in enrolled and y->c in enrolled and c->p in courseProjects implies x.(c.(instanceGrades[this])) = y.(c.(instanceGrades[this]))
}
    S64 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit

  all disj x,y:Student, c:Course, g1: x.(c.(instanceGrades[this])), g2:y.(c.(instanceGrades[this])) | (lone c.courseProjects & x.personProjects & y.personProjects) implies g1=g2
}
    S65 in valid iff {
	    all c: Course |
        all p: Project |
            (p in c.courseProjects and 
             some disj s1, s2: Student | 
                (p in s1.personProjects and p in s2.personProjects and 
                 ((c.(instanceGrades[this])[s1] = (order_next[this])[c.(instanceGrades[this])[s2]]) or 
                  (c.(instanceGrades[this])[s2] = (order_next[this])[c.(instanceGrades[this])[s1]]) or 
                  (c.(instanceGrades[this])[s1] = c.(instanceGrades[this])[s2]))))
}
    S66 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	all disj s1, s2: Student, c: Course | 
  		(s1.personProjects & s2.personProjects) != none and s1.personProjects & s2.personProjects in c.courseProjects
  		implies (s1.(c.(instanceGrades[this]))!=none and s2.(c.(instanceGrades[this]))!=none and (
  		s1.(c.(instanceGrades[this])) = s2.(c.(instanceGrades[this]))+1 or
  		s1.(c.(instanceGrades[this])) = s2.(c.(instanceGrades[this])) or
  		s1.(c.(instanceGrades[this])) = (order_prev[this])[s2.(c.(instanceGrades[this]))]))
}
    S67 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	all disj s1, s2: Student | 
  		s1.personProjects & s2.personProjects != none implies
  		all g1: s1.(Course.(instanceGrades[this])), g2: s2.(Course.(instanceGrades[this])) |
  			g1 = g2 or
  			g1 = g2 + 1 or
  			g1 = (order_prev[this])[g2]
}
    S68 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	all disj s1, s2 : Student, c : Course | some (s1.personProjects & s2.personProjects).~courseProjects :> c => (order_gte[this, s2.(c.(instanceGrades[this])), (order_prev[this])[s1.(c.(instanceGrades[this]))]])
}
    S69 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	all disj s1, s2 : Student, c : Course | some (s1.personProjects & s2.personProjects).~courseProjects :> c => (order_gt[this, s2.(c.(instanceGrades[this])), s1.(c.(instanceGrades[this])).(order_prev[this])])
}
    S70 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
	all disj s1, s2 : Student, c : Course | (some (s1.personProjects & s2.personProjects).~courseProjects :> c) => (order_gte[this, s2.(c.(instanceGrades[this])), s1.(c.(instanceGrades[this])).(order_prev[this])]) && s2.(c.(instanceGrades[this])) not = none
}
    S71 in valid iff {
	// Students working on the same project in a course cannot have marks differing by more than one unit
    all disj s1, s2: Student, c: Course | s1.(c.(instanceGrades[this])) = s2.(c.(instanceGrades[this])) or s1.(c.(instanceGrades[this])) = s2.(c.(instanceGrades[this])).(order_next[this]) or s1.(c.(instanceGrades[this])).(order_next[this]) = s2.(c.(instanceGrades[this]))
}
    S72 in valid iff {
	// Students working on the same project in a course 
		// cannot have marks differing by more than one unit
	all c: Course, p: c.courseProjects |
		all disj s1, s2: p.~(Person <: personProjects) |
			c.(instanceGrades[this])[s1] not in (Grade - (c.(instanceGrades[this])[s1] + c.(instanceGrades[this])[s1].(order_prev[this]) + c.(instanceGrades[this])[s1].(order_next[this])))
}
    S73 in valid iff {
	// Students working on the same project in a course 
		// cannot have marks differing by more than one unit
	all c: Course, p: c.courseProjects | all disj s1, s2: p.~(Person <: personProjects) |
		c.(instanceGrades[this])[s2] in (Grade - c.(instanceGrades[this])[s1] - (order_next[this])[c.(instanceGrades[this])[s1]] - (order_prev[this])[c.(instanceGrades[this])[s1]])
}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73 extends Formula {}

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
