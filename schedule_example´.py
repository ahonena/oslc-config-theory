from z3 import EnumSort, Function, Solver, And, Bool, sat, Context

def print_consistency_analysis_result(s, case):
    print("Case being checked: " + case)
    if(s.check() == sat):
        print(case + " is consistent")
    else:
        print("Unsatisfiable theory: " + case)
        print("Unsat core: ", s.unsat_core())
        

# Create a fresh context
ctx = Context()

# Declare the types using the new context
Day, (Monday, Tuesday) = EnumSort('Day', ['Monday', 'Tuesday'], ctx)
Room, (Room1, Room2) = EnumSort('Room', ['Room1', 'Room2'], ctx)
Professor, (ProfessorA, ProfessorB) = EnumSort('Professor', ['ProfessorA', 'ProfessorB'], ctx)
Course, (CourseX, CourseY, CourseZ) = EnumSort('Course', ['CourseX', 'CourseY', 'CourseZ'], ctx)

# Define the schedule as separate functions
DaySchedule = Function('DaySchedule', Course, Day)
RoomSchedule = Function('RoomSchedule', Course, Room)
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