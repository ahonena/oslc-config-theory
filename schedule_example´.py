from z3 import EnumSort, Function, Solver, And, Bool, sat, Context

def print_consistency_analysis_result(s, case):
    print("Case being checked: " + case)
    if(s.check() == sat):
        print(case + " is consistent")
    else:
        print("Unsatisfiable theory: " + case)
        print("Unsat core: ", s.unsat_core())
        
'''
Scenario: Course Scheduling

Imagine you are trying to schedule courses in a university. You have constraints on room availability, professors' availability, and some other restrictions. You model these constraints using Z3, and Z3 tells you the model is unsatisfiable (i.e., there's no valid schedule given the constraints). But which constraints are causing the issue? That's where unsat_core comes in.
Constraints:

    Room1 is available on Monday.
    Room2 is available on Tuesday.
    Professor A can teach on Monday.
    Professor B can teach on Tuesday.
    Course X is taught by Professor A in Room1.
    Course Y is taught by Professor B in Room2.
    Course Z is taught by Professor A in Room2.

Now, there's a hypothetical additional constraint that introduces inconsistency:
8. Course Z must also be taught on Monday (but we know from constraint 7 that Professor A teaches in Room2 on a different day).
'''

# Create a fresh context
ctx = Context()

# Declare the types using the new context
Day, (Monday, Tuesday) = EnumSort('Day', ['Monday', 'Tuesday'], ctx)
Room, (Room1, Room2) = EnumSort('Room', ['Room1', 'Room2'], ctx)
Professor, (ProfessorA, ProfessorB) = EnumSort('Professor', ['ProfessorA', 'ProfessorB'], ctx)
Course, (CourseX, CourseY, CourseZ) = EnumSort('Course', ['CourseX', 'CourseY', 'CourseZ'], ctx)

# Define the schedule as separate functions
# DaySchedule maps Courses to Days, i.e. tells what day the course is
DaySchedule = Function('DaySchedule', Course, Day)
# RoomSchedule tells what room the course is
RoomSchedule = Function('RoomSchedule', Course, Room)
# ProfessorSchedule tells which professor teaches the course
ProfessorSchedule = Function('ProfessorSchedule', Course, Professor)

# Create the solver in the new context
s = Solver(ctx=ctx)

# Adding constraints with tracking
constraint1 = And(DaySchedule(CourseX) == Monday, RoomSchedule(CourseX) == Room1, ProfessorSchedule(CourseX) == ProfessorA)
s.assert_and_track(constraint1, Bool('Constraint1',  ctx=ctx))
constraint2 = And(DaySchedule(CourseY) == Tuesday, RoomSchedule(CourseY) == Room2, ProfessorSchedule(CourseY) == ProfessorB)
s.assert_and_track(constraint2, Bool('Constraint2',  ctx = ctx))
constraint3 = And(DaySchedule(CourseZ) == Tuesday, RoomSchedule(CourseZ) == Room2, ProfessorSchedule(CourseZ) == ProfessorA)
s.assert_and_track(constraint3, Bool('Constraint3',  ctx = ctx))


# This constraint introduces inconsistency:
constraint4 = DaySchedule(CourseZ) == Monday
s.assert_and_track(constraint4, Bool('Constraint4', ctx=ctx))


print_consistency_analysis_result(s, "scheduling")