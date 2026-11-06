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
    Oracle in valid iff {
	// Only students can be enrolled in courses
	all p : Person | some p.enrolled implies p in Student
}
    S1 in valid iff {
	// Only students can be enrolled in courses
  	all c: Course | c.(instanceGrades[this]) in (Student -> Grade)
	
}
    S2 in valid iff {
	// Only students can be enrolled in courses
  	all c: Course | c.(instanceGrades[this]) in (Student some -> Grade)
	
}
    S3 in valid iff {
	// Only students can be enrolled in courses
	all p : Person | some c : Course | some c.(instanceGrades[this]).p implies p in Student	
}
    S4 in valid iff {
	// Only students can be enrolled in courses
	
}
    S5 in valid iff {
	// Only students can be enrolled in courses
	all p : Person | (some c : Course | some c.(instanceGrades[this])[p]) iff (p in Student)	
}
    S6 in valid iff {
	// Only students can be enrolled in courses
	all p: Professor | no p.enrolled
}
    S7 in valid iff {
	// Only students can be enrolled in courses
  	all p: Person | some enrolled implies p in Student
}
    S8 in valid iff {
	// Only students can be enrolled in courses
  all p:Person | p.enrolled in Student
	
}
    S9 in valid iff {
	// Only students can be enrolled in courses
	all p : Person - Professor | p in enrolled.Course
  
  	no(enrolled.Course-Student)
}
    S10 in valid iff {
    all p : Person | (p in Student) iff (some p.enrolled)
}
    S11 in valid iff {
	// Only students can be enrolled in courses
	all c: Course | enrolled.c not in Professor
}
    S12 in valid iff {
	// Only students can be enrolled in courses
	all c: Course | Professor not in enrolled.c
}
    S13 in valid iff {
	// Only students can be enrolled in courses
  all p : Person | p in Student implies some p.enrolled
	
}
    S14 in valid iff {
	all s : Student , c: Course | s in enrolled.c 
}
    S15 in valid iff {
	// Only students can be enrolled in courses
	all c: Course | Student in enrolled.c and Person not in enrolled.c
}
    S16 in valid iff {
	// Only students can be enrolled in courses
	all c: Course | enrolled.c = Student
 
}
    S17 in valid iff {
	// Only students can be enrolled in courses 
  all s: Student, c: Course | s.enrolled = c
	
}
    S18 in valid iff {
	// Only students can be enrolled in courses 
  all s: Student, c: Course | s.enrolled = c and s.teaches != Course
	
}
    S19 in valid iff {
	// Only students can be enrolled in courses 
  all s: Student, c: Course | s.enrolled = c and no teaches
	
}
    S20 in valid iff {
	// Only students can be enrolled in courses 
  all s: Person - Professor, c: Course | s.enrolled = c
	
}
    S21 in valid iff {
	// Only students can be enrolled in courses
  	//all p : Person , c : Course | p.enrolled in c implies p not in Professor
	all p : Person , c : Course | p.teaches in c implies p not in Student
}
    S22 in valid iff {
	// Only students can be enrolled in courses 
  all p: Professor, c: Course | p.enrolled not in c
	
}
    S23 in valid iff {
	// Only students can be enrolled in courses 
 all p: Person - Student, s: Person - Professor, c: Course | 
	#(p.enrolled) = 0 and
	#(s.teaches) = 0 and
	no (p & s) and
	s.enrolled in c
	
}
    S24 in valid iff {
	// Only students can be enrolled in courses 
all p: Person  | 
	p in Student and
	#(p.enrolled) != 0 and
	#(p.teaches) = 0 
	
}
    S25 in valid iff {
	// Only students can be enrolled in courses 
 all p: Professor , s: Student, c: Course | 
	#(p.enrolled) = 0 and
	#(s.teaches) = 0 and
	no (p & s) and
	s.enrolled in c
	
}
    S26 in valid iff {
	// Only students can be enrolled in courses
	all p: Person | p.enrolled in Course iff p in Student and p.teaches not in Course
}
    S27 in valid iff {
	// Only students can be enrolled in courses 
all disj p,s : Person |
	p!=s and
	p in Professor and
	s in Student and
	#(p.enrolled) = 0 and
	#(s.teaches) = 0 
	
}
    S28 in valid iff {
	// Only students can be enrolled in courses
	all p: Professor, s: Student, c: Course | 
  		p != s and
  		p + s = Person and
  		no p.enrolled
}
    S29 in valid iff {
	// Only students can be enrolled in courses
	all p: Person - Professor, s: Person - Student, c: Course | 
  		no p.enrolled
}
    S30 in valid iff {
	// Only students can be enrolled in courses
	all p: Person - Professor | 
  		no p.enrolled
}
    S31 in valid iff {
	// Only students can be enrolled in courses
	all p: Person | 
  		no p.enrolled and
  		p in Professor
}
    S32 in valid iff {
	// Only students can be enrolled in courses 
  	all	p : Professor | (no p.teaches)
}
    S33 in valid iff {
	// Only students can be enrolled in courses
  	all p: Person | some c:Course | c in p.enrolled implies p in Student
}
    S34 in valid iff {
	// Only students can be enrolled in courses
  	all p: Person-Professor, c : Course | p.enrolled in c
	
}
    S35 in valid iff {
	// Only students can be enrolled in courses
  	all p: Person, c : Course | p.enrolled in c implies p in Student
	
}
    S36 in valid iff {
	// Only students can be enrolled in courses
  	all p: Person, c : Course | p.enrolled in c implies p in Student and p.teaches not in c
	
}
    S37 in valid iff {
	// Only students can be enrolled in courses
  	all p : Person-Professor, c : Course | p.enrolled in c and p.teaches not in c
}
    S38 in valid iff {
	// Only students can be enrolled in courses
  all p:Person |
  	p.enrolled in Course implies p in Student
	
}
    S39 in valid iff {
	// Only students can be enrolled in courses
	all p : Person | some c : Course | p.enrolled in c implies p in Student
}
    S40 in valid iff {
	// Only students can be enrolled in courses
	all p : Person | some c : Course | p.enrolled in c implies (p in Student and not p in Professor)
}
    S41 in valid iff {
	// Only students can be enrolled in courses
  	//all p : Professor, s : Student | s in enrolled.Course and p not in enrolled.Course
  all s : Student | some s.enrolled
  all p : Professor | no p.enrolled
	
}
    S42 in valid iff {
	// Only students can be enrolled in courses
    all c : Course | Student in c.enrolled
	
}
    S43 in valid iff {
	// Only students can be enrolled in courses
  all p : Person | p.enrolled in Student.enrolled
	
}
    S44 in valid iff {
	// Only students can be enrolled in courses
	all p:Person|Student in p.enrolled
}
    S45 in valid iff {
	// Only students can be enrolled in courses
	all c : Course | c.enrolled = Person - Professor
}
    S46 in valid iff {
	// Only students can be enrolled in courses
	all s:Person, c:Course | s in Professor and s not in enrolled.c
}
    S47 in valid iff {
	// Only students can be enrolled in courses
	all c : Course | all p : Person | c in p.enrolled implies p in Student and p not in Professor
}
    S48 in valid iff {
	// Only students can be enrolled in courses
	all p : Person | some p.enrolled => p = Student
}
    S49 in valid iff {
	// Only students can be enrolled in courses
	all s:Person, c:Course | s in Professor implies s not in enrolled.c and s in Student implies s in enrolled.c 
}
    S50 in valid iff {
	// Only students can be enrolled in courses
  all s : Student, c : Course | s.enrolled in c  
	
}
    S51 in valid iff {
	// Only students can be enrolled in courses
	
  	all p: Person, c: Course | p = Student implies p.enrolled in c
  
}
    S52 in valid iff {
	// Only students can be enrolled in courses
  	all x : Person | (all c : Course | x in c.enrolled )implies x in Student
	
}
    S53 in valid iff {
	// Only students can be enrolled in courses
  	all p : Person , c : Course | p.enrolled in c implies p in Student and p not in Professor
	
}
    S54 in valid iff {
	// Only students can be enrolled in courses
  Person-Professor in enrolled.Course
}
    S55 in valid iff {
	// Only students can be enrolled in courses
   all p : Person | p in enrolled.Course 
	
}
    S56 in valid iff {
	// Only students can be enrolled in courses
	all p: Person | (p in Student) => (p.enrolled = p.teaches)
}
    S57 in valid iff {
	// Only students can be enrolled in courses
	
  	all p: Person, c: Course | p in Student and p.enrolled in c
  
}
    S58 in valid iff {
	// Only students can be enrolled in courses
	
  	all p: Person, c: Course | p in Student and p.enrolled in c implies p not in Professor
  
}
    S59 in valid iff {
	// Only students can be enrolled in courses
	
  	all p: Person, c: Course | p in Student and p.enrolled in c and p not in Professor
  
}
    S60 in valid iff {
	// Only students can be enrolled in courses
	all s: Student | s.enrolled = s.teaches
    all p: Professor | p.enrolled = none
}
    S61 in valid iff {
	// Only students can be enrolled in courses
  	all p : Person , c : Course | some p : Person | p.enrolled in c implies p in Student
  	all p : Person | (some c : Course | p->c in enrolled) implies p in Student
	all p : Person , c : Course | p in enrolled.c implies p in Student
}
    S62 in valid iff {
	// Only students can be enrolled in courses
  	all p : Person , c : Course | some p : Person | p.enrolled in c implies p in Student
  	//all p : Person | (some c : Course | p->c in enrolled) implies p in Student
	//all p : Person , c : Course | p in enrolled.c implies p in Student
}
    S63 in valid iff {
	// Only students can be enrolled in courses
  	all p : Professor, s : Student | s in enrolled.Course and not p in enrolled.Course
	
}
    S64 in valid iff {
	// Only students can be enrolled in courses
  	//all p : Professor, s : Student | s in enrolled.Course and p not in enrolled.Course
  all p : Professor, s : Student | s in p.enrolled and not p in s.enrolled
  //all p : Professor | not p in enrolled.Course
	
}
    S65 in valid iff {
	// Only students can be enrolled in courses
  	//all p : Professor, s : Student | s in enrolled.Course and p not in enrolled.Course
  all s : Student, c : Course | s in enrolled.c
  all p : Professor, c : Course | p not in enrolled.c
	
}
    S66 in valid iff {
	// Only students can be enrolled in courses
  	//all p : Professor, s : Student | s in enrolled.Course and p not in enrolled.Course
  all s : Student, c : Course | some s.enrolled
  all p : Professor, c : Course | p not in enrolled.c
	
}
    S67 in valid iff {
	// Only students can be enrolled in courses
	all t : Person & Professor, p : Person | no t.enrolled and no p.enrolled 
}
    S68 in valid iff {
    // Only students can be enrolled in courses
    all p: Person |
        some c: p.enrolled |
            c in Course implies p in Student
}
    S69 in valid iff {
	// Only students can be enrolled in courses

	// all p : Person | (some c : Course | p->c in enrolled) implies p in Student

	// all p : Person | (some p.enrolled) implies p in Student

        teaches in Student -> Course
}
    S70 in valid iff {
	// Only students can be enrolled in courses
  	all s: Student | some c: Course | c in s.enrolled and c not in s.teaches
}
    S71 in valid iff {
	// Only students can be enrolled in courses
  	all s: Student | all c: Course | c in s.enrolled and c not in s.teaches
}
    S72 in valid iff {
	// Only students can be enrolled in courses
  	all s: Student | all c: Course | c in s.enrolled and c in s.teaches
}
    S73 in valid iff {
	// Only students can be enrolled in courses
  	all s: Student |some c: Course | c in s.enrolled and c in s.teaches
}
    S74 in valid iff {
	// Only students can be enrolled in courses
	Person - Professor in Course.enrolled  
}
    S75 in valid iff {
	// Only students can be enrolled in courses
	all p:Person-Professor | some enrolled
}
    S76 in valid iff {
	// Only students can be enrolled in courses
	some Student
	
}
    S77 in valid iff {
	// Only students can be enrolled in courses
  all p: Person | (p in Student) implies (no p.enrolled)
	
}
    S78 in valid iff {
	// Only students can be enrolled in courses
	all s : Student | Person.enrolled != Professor
}
    S79 in valid iff {
	// Only students can be enrolled in courses
	all s : Student | Person.enrolled = Course
}
    S80 in valid iff {
	// Only students can be enrolled in courses
	Person.enrolled = Student
}
    S81 in valid iff {
	// Only students can be enrolled in courses
	Student in Person
  	all s:Student| Student.enrolled = Course
}
    S82 in valid iff {
	// Only students can be enrolled in courses
	Student in Person
  	all s:Student | s.teaches = none
}
    S83 in valid iff {
	// Only students can be enrolled in courses
  	all s:Student | Person.enrolled = Course && Person.teaches = none
}
    S84 in valid iff {
	// Only students can be enrolled in courses
  	all p: Professor | p.enrolled not in Course 
}
    S85 in valid iff {
	// Only students can be enrolled in courses
  	no enrolled.Course & Professor and Student = enrolled.Course
	
}
    S86 in valid iff {
	// Only students can be enrolled in courses
  	all p: Professor | some c:Course | c in p.enrolled iff c not in p.teaches 
}
    S87 in valid iff {
	// Only students can be enrolled in courses
  	all p: Person | some c:Course | c in p.enrolled iff c not in p.teaches 
}
    S88 in valid iff {
	// Only students can be enrolled in courses
  	all p: Person | some c:Course | c in p.enrolled and c not in p.teaches implies p in Student
}
    S89 in valid iff {
	// Only students can be enrolled in courses
	all p:Person |
  		some course:p.enrolled|
  			course in Course implies Student in p	
}
    S90 in valid iff {
	// Only students can be enrolled in courses
  	all p: Person | p.teaches not in p.enrolled and p.enrolled in Course implies p in Student
}
    S91 in valid iff {
	// Only students can be enrolled in courses
	all p:Person |
  		one course:p.enrolled|
  			course in Course implies Student in p	
}
    S92 in valid iff {
	// Only students can be enrolled in courses
	all p:Person |
  		one course:p.enrolled|
        	course in Course implies Professor not in p	
}
    S93 in valid iff {
	// Only students can be enrolled in courses
	all p:Person |
  		some c:p.enrolled|
        	c in Course implies Professor not in p	
}
    S94 in valid iff {
    // Only students can be enrolled in courses
    all p: Person |
        some c: p.enrolled |
            c in Course implies Student in p and Professor not in p
}
    S95 in valid iff {
    // Only students can be enrolled in courses
    all p: Person |
        some c: p.enrolled |
            c in Course implies p in Student and p not in Professor
}
    S96 in valid iff {
    // Only students can be enrolled in courses
    all p: Person |
        one c: p.enrolled |
            c in Course implies p in Student 
}
    S97 in valid iff {
	// Only students can be enrolled in courses
  all p:Person |
  	p.enrolled in Course implies p in Student and p not in Professor
	
}
    S98 in valid iff {
	// Only students can be enrolled in courses
	no (Professor-Student).enrolled
}
    S99 in valid iff {
	// Only students can be enrolled in courses
  	all p:Person | all c:Course | p.enrolled in c iff p in Student
}
    S100 in valid iff {
	// Only students can be enrolled in courses
	all c : Course | enrolled.c not in Person - Student
}
    S101 in valid iff {
	// Only students can be enrolled in courses
  Course in Student.enrolled
  Course not in Professor.enrolled
	
}
    S102 in valid iff {
	// Only students can be enrolled in courses
	all c : Course | all s : Student | enrolled.c in s
}
    S103 in valid iff {
	// Only students can be enrolled in courses
	all c : Course, p: Person | (p - Professor) not in c.enrolled
}
    S104 in valid iff {
	// Only students can be enrolled in courses
	no (Professor-Student).enrolled
  
	no (Student-Professor).teaches
}
    S105 in valid iff {
	// Only students can be enrolled in courses
  all p : Person | (Course in p.enrolled) implies (p in Student) 
	
}
    S106 in valid iff {
	// Only students can be enrolled in courses
	all p : Person | all c : Course | c in p.enrolled & Student
}
    S107 in valid iff {
	// Only students can be enrolled in courses
  	//all c : Course, s : Student | one s in enrolled.c
    all p : Person, c : Course | p in Student and p in enrolled.c
	
}
    S108 in valid iff {
	// Only students can be enrolled in courses
  	//all c : Course, s : Student | one s in enrolled.c
    all p : Person, c : Course | p in Student and p.enrolled in Course
	
}
    S109 in valid iff {
	// Only students can be enrolled in courses

	// all p : Person | (some c : Course | p->c in enrolled) implies p in Student

	// all p : Person | (some p.enrolled) implies p in Student

        //enrolled in Student -> Course
   //all p : Person, c : Course | p->c in enrolled implies p in Student
  all p : Person | p in Professor implies p not in Student
  no Professor.enrolled
}
    S110 in valid iff {
	// Only students can be enrolled in courses
  	no p: Professor | all c: Course | p in c.enrolled
  
  	
	
}
    S111 in valid iff {
	// Only students can be enrolled in courses
  	no p: Professor | all c: Course | c in p.enrolled
  
  	
	
}
    S112 in valid iff {
	// Only students can be enrolled in courses
  	all p: Professor | no p.enrolled
  all s: Student | s in s.enrolled
}
    S113 in valid iff {
	// Only students can be enrolled in courses
	all p: Person | some c: Course | c in p.enrolled => p = Student
}
    S114 in valid iff {
	// Only students can be enrolled in courses
	all p: Person | some c: Course | c in p.enrolled => p in Student and p not in Professor
}
    S115 in valid iff {
	// Only students can be enrolled in courses
	all p: Person | some c: Course | c in p.enrolled => p in Student and c not in p.teaches
}
    S116 in valid iff {
	// Only students can be enrolled in courses
  	all p : Student, c : Course | c in p.enrolled implies c not in p.teaches
	
}
    S117 in valid iff {
	// Only students can be enrolled in courses
	some (Person-Professor).enrolled
}
    S118 in valid iff {
	// Only students can be enrolled in courses
	//all p1 : Person | all c1 : Course | p1->c1 in enrolled implies p1 in Student
  	no p : Professor | all c : Course | some p.enrolled
}
    S119 in valid iff {
	// Only students can be enrolled in courses
  all p : Person | lone p.enrolled
	
}
    S120 in valid iff {
	// Only students can be enrolled in courses
	some s : Student |  some s.enrolled
}
    S121 in valid iff {
	// Only students can be enrolled in courses
	all p : Professor | not one p.enrolled
}
    S122 in valid iff {
	// Only students can be enrolled in courses
	all p : Person | no p.teaches implies p in Student
}
    S123 in valid iff {
	// Only students can be enrolled in courses
	all p: Person | no p.enrolled implies p in Student
}
    S124 in valid iff {
	// Only students can be enrolled in courses
  	Person-Student not in Person
	
}
    S125 in valid iff {
	// Only students can be enrolled in courses
  	all s : Student, p : Professor, c : Course | s -> c in enrolled and not(p -> c in enrolled)
	
}
    S126 in valid iff {
	// Only students can be enrolled in courses
	all p : Person - Professor | no p.teaches
	
}
    S127 in valid iff {
	// Only students can be enrolled in courses
  Person-Professor not in Person.enrolled 
}
    S128 in valid iff {
	// Only students can be enrolled in courses
  Person-Student not in Person.enrolled
}
    S129 in valid iff {
	// Only students can be enrolled in courses
  Person-Professor not in enrolled.Course
}
    S130 in valid iff {
	// Only students can be enrolled in courses
  Person-Student not in enrolled.Course
}
    S131 in valid iff {
	// Only students can be enrolled in courses
	no Professor . enrolled - Student . enrolled
}
    S132 in valid iff {
	// Only students can be enrolled in courses
  all e : Person.enrolled | Professor not in e
}
    S133 in valid iff {
	// Only students can be enrolled in courses
  all e : Person.personProjects | Professor not in e
}
    S134 in valid iff {
	// Only students can be enrolled in courses
	all c : Course | all p : Person | enrolled.c in p && p in Student 
}
    S135 in valid iff {
    // Only students can be enrolled in courses, except professors teaching the course
    all p : Person | 
        (p in Professor implies all c : p.enrolled | c in p.teaches)
}
    S136 in valid iff {
  all s : Student | some s.enrolled and no s.teaches
	// Only students can be enrolled in courses
	
}
    S137 in valid iff {
	// Only students can be enrolled in courses
  	all s : Student |  Person in s implies (some s.enrolled)
	
}
    S138 in valid iff {
	// Only students can be enrolled in courses
  	all  p: Person | Student in p implies (some p.enrolled)
	
}
    S139 in valid iff {
	// Only students can be enrolled in courses

	//all p : Person | (some p.enrolled) implies p in Student

  
   all p : Person | 
        (p in Student) => some p.enrolled and
        (p in Professor) => no p.enrolled
}
    S140 in valid iff {
	// Only students can be enrolled in courses
	all p : Professor | p.enrolled = p.teaches
}
    S141 in valid iff {
	// Only students can be enrolled in courses
	all p : Person |
  		one p.enrolled implies p in Student
}
    S142 in valid iff {
	// Only students can be enrolled in courses
	all c : Course | enrolled.c = Person
}
    S143 in valid iff {
	// Only students can be enrolled in courses
	all s: Student | one c: Course | s in enrolled.c 
}
    S144 in valid iff {
	// Only students can be enrolled in courses
	all s: Student | one c: Course | enrolled.c in s 
}
    S145 in valid iff {
	// Only students can be enrolled in courses
	all p : Person | #p.enrolled > 1 implies p in Student
}
    S146 in valid iff {
	// Only students can be enrolled in courses
	all x: Person | x.enrolled in Course and x = Student
	
}
    S147 in valid iff {
	// Only students can be enrolled in courses
	all c: Course | c.(instanceGrades[this]).Grade = Student
}
    S148 in valid iff {
	// Only students can be enrolled in courses
	all c: Course | all p: c.(instanceGrades[this]).Grade | p = Student
}
    S149 in valid iff {
	// Only students can be enrolled in courses
	lone s : Student | s.enrolled = Person.enrolled
}
    S150 in valid iff {
    // Professors cannot be enrolled in courses
    all p: Person | (p in Professor implies no p.enrolled)
    
    // Students cannot teach courses
    all p: Person | (p in Student implies no p.teaches)
}
    S151 in valid iff {
	// Only students can be enrolled in courses
  	all p: Person | (p in Student <=> some p.enrolled and no p.teaches)
	
}
    S152 in valid iff {
	// Only students can be enrolled in courses
  	//all p: Person | p in Student or no p.enrolled
  	some s : Student | some s.enrolled
  	all p: Professor | no p.enrolled
}
    S153 in valid iff {
	// Only students can be enrolled in courses
  all s: Student | some s.enrolled
  all p: Professor | no p.enrolled and some p.teaches
}
    S154 in valid iff {
	// Only students can be enrolled in courses
  all s: Student | some s.enrolled and no s.teaches
  all p: Professor | no p.enrolled and some p.teaches
}
    S155 in valid iff {
	// Only students can be enrolled in courses
	all p: Person | #p.enrolled > 0 iff p in Student and p not in Professor  
}
    S156 in valid iff {
	// Only students can be enrolled in courses
  all p : Person - Professor, c : Course | c in p.enrolled 
	
}
    S157 in valid iff {
	// Only students can be enrolled in courses
	all c : Course | enrolled.c = Person-Professor
}
    S158 in valid iff {
	// Only students can be enrolled in courses
	all c : Course | Person-Student not in enrolled.c
 
}
    S159 in valid iff {
	// Only students can be enrolled in courses
	all p : Person | some c : p.enrolled | not p in Professor
}
    S160 in valid iff {
	// Only students can be enrolled in courses
	all pe: Person| pe.teaches&pe.enrolled=none
}
    S161 in valid iff {
	// Only students can be enrolled in courses
  	all p: Person | (p in Student) iff (p.enrolled != none) and (not some p1: Professor| p1.enrolled!=none)
}
    S162 in valid iff {
	// Only students can be enrolled in courses
	all p: Professor, s: Student, c: Course| p !=s and c not in p.enrolled
}
    S163 in valid iff {
	// Only students can be enrolled in courses
  all p: Professor, s: Student, c: Course | p != s implies  enrolled.c not in p
  all p: Professor, c:Course | enrolled.c not in p
	
}
    S164 in valid iff {
	// Only students can be enrolled in courses
  all p: Professor, s: Student, c: Course | p != s implies  enrolled.c not in p
	
}
    S165 in valid iff {
	// Only students can be enrolled in courses
  all p: Professor, c: Course | teaches.c in p implies enrolled.c not in p
	
}
    S166 in valid iff {
	// Only students can be enrolled in courses
  all p: Person, c: Course | enrolled.c in p implies p in Student
	
}
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72, S73, S74, S75, S76, S77, S78, S79, S80, S81, S82, S83, S84, S85, S86, S87, S88, S89, S90, S91, S92, S93, S94, S95, S96, S97, S98, S99, S100, S101, S102, S103, S104, S105, S106, S107, S108, S109, S110, S111, S112, S113, S114, S115, S116, S117, S118, S119, S120, S121, S122, S123, S124, S125, S126, S127, S128, S129, S130, S131, S132, S133, S134, S135, S136, S137, S138, S139, S140, S141, S142, S143, S144, S145, S146, S147, S148, S149, S150, S151, S152, S153, S154, S155, S156, S157, S158, S159, S160, S161, S162, S163, S164, S165, S166 extends Formula {}

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
