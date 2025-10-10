open util/ordering[Grade]

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

// Req 2: Only professors can teach courses

// Failed to parse Alloy model
run Pos1_run3_2 {
    some disj Course1 : Course | some disj Grade1, Grade2 : Grade {
        Person = none
        Professor = none
        Student = none
        Course = Course1
        Project = none
        Grade = Grade1 + Grade2

        Person <: teaches = none->none
        Person <: enrolled = none->none
        Person <: projects = none->none
        // Course <: projects = none
        Course <: grades = none->none->none
        Grade <: next = Grade1->Grade2
    }
} for 0 Person, 1 Course, 0 Project, 2 Grade expect 1

// Failed to parse Alloy model
run Pos2_run3_2 {
    some disj Person1 : Person | some disj Course1 : Course | some disj Grade1, Grade2 : Grade {
        Person = Person1
        Professor = Person1
        Student = none
        Course = Course1
        Project = none
        Grade = Grade1 + Grade2

        Person <: teaches = Person1->Course1
        Person <: enrolled = none->none
        Person <: projects = none->none
        // Course <: projects = none
        Course <: grades = none->none->none
        Grade <: next = Grade1->Grade2
    }
} for 1 Person, 1 Course, 0 Project, 2 Grade expect 1

// Failed to parse Alloy model
run Neg1_run3_2 {
    some disj Person1 : Person | some disj Course1 : Course | some disj Grade1, Grade2 : Grade {
        Person = Person1
        Professor = none
        Student = none
        Course = Course1
        Project = none
        Grade = Grade1 + Grade2

        Person <: teaches = Person1->Course1
        Person <: enrolled = none->none
        Person <: projects = none->none
        // Course <: projects = none
        Course <: grades = none->none->none
        Grade <: next = Grade1->Grade2
    }
} for 1 Person, 1 Course, 0 Project, 2 Grade expect 0

// Failed to parse Alloy model
run Neg2_run3_2 {
    some disj Person1 : Person | some disj Course1 : Course | some disj Grade1, Grade2 : Grade {
        Person = Person1
        Professor = none
        Student = Person1
        Course = Course1
        Project = none
        Grade = Grade1 + Grade2

        Person <: teaches = Person1->Course1
        Person <: enrolled = Person1->Course1
        Person <: projects = none->none
        // Course <: projects = none
        Course <: grades = none->none->none
        Grade <: next = Grade1->Grade2
    }
} for 1 Person, 1 Course, 0 Project, 2 Grade expect 0

// Failed to parse Alloy model
run Neg3_run3_2 {
    some disj Person1, Person2 : Person | some disj Course1 : Course | some disj Grade1, Grade2 : Grade {
        Person = Person1 + Person2
        Professor = Person2
        Student = Person1
        Course = Course1
        Project = none
        Grade = Grade1 + Grade2

        Person <: teaches = Person1->Course1 + Person2->Course1
        Person <: enrolled = Person1->Course1
        Person <: projects = none->none
        // Course <: projects = none
        Course <: grades = none->none->none
        Grade <: next = Grade1->Grade2
    }
} for 2 Person, 1 Course, 0 Project, 2 Grade expect 0


// Req 5: Only students work on projects and projects must have someone working on them

// Unexpectedly generated instance for negative instance
run Neg3_run1_5 {
    some disj P : Person | some disj S : Person | some disj C : Course | some disj PR : Project | some disj G1, G2 : Grade {
        Person = P + S
        Professor = P
        Student = S
        Course = C
        Project = PR
        Grade = G1 + G2

        Person <: teaches = P->C
        Person <: enrolled = S->C
        Person <: projects = P->PR + S->PR

        Course <: projects = C->PR
        Course <: grades = C->P->G1 + C->S->G2

        Grade <: next = G1->G2
    }
} for 2 Person, 1 Course, 1 Project, 2 Grade expect 0

// Req 6: Students only work on projects of courses they are enrolled in

// Failed to parse Alloy model
run Neg2_run1_6 {
  some disj P1,P2 : Person | some disj C1 : Course | some disj PR1 : Project | some disj G1,G2 : Grade {
    Person = P1 + P2
    Professor = P1
    Student = P2

    Course = C1
    Project = PR1
    Grade = G1 + G2

    Person <: teaches = P1->C1
    // Person <: enrolled = none
    Person <: projects = P2->PR1

    Course <: projects = C1->PR1
    Course <: grades = none->none->none

    Grade <: next = G1->G2
  }
} for 2 Person, 1 Course, 1 Project, 2 Grade expect 0

// Failed to parse Alloy model
run Neg1_run3_6 {
    some disj P1 : Person | some disj C1 : Course | some disj PR1 : Project | some disj G1, G2 : Grade {
        Person = P1
        Professor = P1
        Student = P1
        Course = C1
        Project = PR1
        Grade = G1 + G2

        teaches = P1->C1
        // enrolled = none
        Person <: projects = P1->PR1
        Course <: projects = C1->PR1
        grades = none->none->none

        Grade <: next = G1->G2
    }
} for 1 Person, 1 Course, 1 Project, 2 Grade expect 0

// Req 7: Students work on at most one project per course

// Instance failed to satisfy previous requirements
// Fails req 5: Only students work on projects and projects must have someone working on them
run Neg2_run3_7 {
  some disj Pprof,Pstud : Person | some disj C1,C2 : Course | some disj Pr1,Pr2,Pr3 : Project | some disj G1,G2,G3 : Grade {
    Person = Pprof + Pstud
    Professor = Pprof
    Student = Pstud

    Course = C1 + C2
    Project = Pr1 + Pr2 + Pr3
    Grade = G1 + G2 + G3

    teaches = Pprof->C1 + Pprof->C2
    enrolled = Pstud->C1

    Course <: projects = C1->Pr1 + C1->Pr2 + C2->Pr3
    Person <: projects = Pstud->Pr1 + Pstud->Pr2

    grades = none->none->none
    Grade <: next = G1->G2 + G2->G3
  }
} for 2 Person, 2 Course, 3 Project, 3 Grade expect 0

// Req 9: A professor cannot teach colleagues

// Unexpectedly generated instance for negative instance
run Neg1_run1_9 {
    some disj P, Q : Person | some disj C : Course | some disj PR : Project | some disj G1, G2 : Grade {
        Person = P + Q
        Professor = P + Q
        Student = Q

        Course = C
        Project = PR
        Grade = G1 + G2

        teaches = P->C
        enrolled = Q->C

        Person <: projects = Q->PR
        Course <: projects = C->PR

        Course <: grades = C->Q->G1

        Grade <: next = G1->G2
    }
} for 2 Person, 1 Course, 1 Project, 2 Grade expect 0

// Unexpectedly generated instance for negative instance
run Neg2_run1_9 {
    some disj P, Q, S : Person | some disj C : Course | some disj PR : Project | some disj G1, G2 : Grade {
        Person = P + Q + S
        Professor = P + Q
        Student = Q + S

        Course = C
        Project = PR
        Grade = G1 + G2

        teaches = P->C
        enrolled = Q->C + S->C

        Person <: projects = S->PR
        Course <: projects = C->PR

        Course <: grades = C->S->G1 + C->Q->G2

        Grade <: next = G1->G2
    }
} for 3 Person, 1 Course, 1 Project, 2 Grade expect 0

// Unexpectedly generated instance for negative instance
run Neg3_run1_9 {
    some disj P, Q, S : Person | some disj C1, C2 : Course | some disj PR1, PR2 : Project | some disj G1, G2 : Grade {
        Person = P + Q + S
        Professor = P + Q
        Student = Q + S

        Course = C1 + C2
        Project = PR1 + PR2
        Grade = G1 + G2

        teaches = P->C1 + P->C2
        enrolled = S->C1 + Q->C2

        Person <: projects = S->PR1 + Q->PR2
        Course <: projects = C1->PR1 + C2->PR2

        Course <: grades = C1->S->G1 + C2->Q->G2

        Grade <: next = G1->G2
    }
} for 3 Person, 2 Course, 2 Project, 2 Grade expect 0

// Unexpectedly generated instance for negative instance
run Neg1_run2_9 {
    some disj P1,P2 : Person | some disj C1 : Course | some disj PR1 : Project | some disj G1,G2 : Grade {
        Person = P1 + P2
        Professor = P1 + P2
        Student = P2
        Course = C1
        Project = PR1
        Grade = G1 + G2

        teaches = P1->C1
        enrolled = P2->C1
        Person <: projects = P2->PR1
        Course <: projects = C1->PR1
        grades = none->none->none
        Grade <: next = G1->G2

        // Negative: P1 (professor) teaches C1 while P2 (also a professor, and a student) is enrolled in C1, so a professor teaches a colleague; all other listed requirements still hold and no professor teaches herself.
    }
} for 2 Person, 1 Course, 1 Project, 2 Grade expect 0

// Unexpectedly generated instance for negative instance
run Neg2_run2_9 {
    some disj P1,P2,P3 : Person | some disj C1,C2 : Course | some disj PR1,PR2 : Project | some disj G1,G2 : Grade {
        Person = P1 + P2 + P3
        Professor = P1 + P2
        Student = P2 + P3
        Course = C1 + C2
        Project = PR1 + PR2
        Grade = G1 + G2

        teaches = P1->C1 + P2->C2
        enrolled = P2->C1 + P3->C2
        Person <: projects = P2->PR1 + P3->PR2
        Course <: projects = C1->PR1 + C2->PR2
        grades = none->none->none
        Grade <: next = G1->G2

        // Negative: P1 (professor) teaches C1 while colleague P2 (also a professor, and a student) is enrolled in C1, so a professor teaches a colleague; all other constraints are satisfied and no professor teaches herself.
    }
} for 3 Person, 2 Course, 2 Project, 2 Grade expect 0

// Unexpectedly generated instance for negative instance
run Neg3_run2_9 {
    some disj P1,P2,P3 : Person | some disj C1 : Course | some disj PR1,PR2 : Project | some disj G1,G2,G3 : Grade {
        Person = P1 + P2 + P3
        Professor = P1 + P2
        Student = P2 + P3
        Course = C1
        Project = PR1 + PR2
        Grade = G1 + G2 + G3

        teaches = P1->C1
        enrolled = P2->C1 + P3->C1
        Person <: projects = P2->PR1 + P3->PR2
        Course <: projects = C1->PR1 + C1->PR2
        grades = none->none->none
        Grade <: next = G1->G2 + G2->G3

        // Negative: P1 (professor) teaches C1 while colleague P2 (also a professor, and a student) is enrolled in C1, so a professor teaches a colleague; all other requirements hold and no professor teaches herself.
    }
} for 3 Person, 1 Course, 2 Project, 3 Grade expect 0

// Unexpectedly generated instance for negative instance
run Neg1_run3_9 {
    some disj Prof1, Prof2 : Person | some disj C1 : Course | some disj Pj1 : Project | some disj G1, G2 : Grade {
        Person = Prof1 + Prof2
        Professor = Prof1 + Prof2
        Student = Prof2

        Course = C1
        Project = Pj1
        Grade = G1 + G2

        Person <: teaches = Prof1->C1
        Person <: enrolled = Prof2->C1
        Person <: projects = Prof2->Pj1

        Course <: projects = C1->Pj1
        Course <: grades = C1->Prof2->G1

        Grade <: next = G1->G2
    }
} for 2 Person, 1 Course, 1 Project, 2 Grade expect 0

// Unexpectedly generated instance for negative instance
run Neg2_run3_9 {
    some disj Prof1, Prof2, Stud1 : Person | some disj C1, C2 : Course | some disj Pj1, Pj2 : Project | some disj G1, G2 : Grade {
        Person = Prof1 + Prof2 + Stud1
        Professor = Prof1 + Prof2
        Student = Prof2 + Stud1

        Course = C1 + C2
        Project = Pj1 + Pj2
        Grade = G1 + G2

        Person <: teaches = Prof1->C1 + Prof1->C2
        Person <: enrolled = Stud1->C1 + Prof2->C2
        Person <: projects = Stud1->Pj1 + Prof2->Pj2

        Course <: projects = C1->Pj1 + C2->Pj2
        Course <: grades = C1->Stud1->G1 + C2->Prof2->G2

        Grade <: next = G1->G2
    }
} for 3 Person, 2 Course, 2 Project, 2 Grade expect 0

// Unexpectedly generated instance for negative instance
run Neg3_run3_9 {
    some disj Prof1, Prof2, Stud1 : Person | some disj C1 : Course | some disj Pj1 : Project | some disj G1, G2 : Grade {
        Person = Prof1 + Prof2 + Stud1
        Professor = Prof1 + Prof2
        Student = Prof2 + Stud1

        Course = C1
        Project = Pj1
        Grade = G1 + G2

        Person <: teaches = Prof1->C1
        Person <: enrolled = Prof2->C1 + Stud1->C1
        Person <: projects = Prof2->Pj1

        Course <: projects = C1->Pj1
        Course <: grades = C1->Prof2->G1

        Grade <: next = G1->G2
    }
} for 3 Person, 1 Course, 1 Project, 2 Grade expect 0
