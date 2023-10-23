from z3 import *

def print_consistency_analysis_result(s, case):
    print("Case being checked: " + case)
    if(s.check() == sat):
        print(case + " is consistent")
    else:
        print("Unsatisfiable theory: " + case)

# Define Configuration datatype
Configuration = Datatype('Configuration')
Configuration.declare('config', ('resource_set', SetSort(IntSort())))
Configuration = Configuration.create()


# Define Contribution datatype
Contribution = Datatype('Contribution')
Contribution.declare('contribute', ('resource_version', IntSort()))
Contribution = Contribution.create()

# ... Continue for other datatypes like Baseline, etc.


ContributionsInConfig = Function('ContributionsInConfig', Configuration, SetSort(Contribution))



def is_non_empty(s, set_var):
    elem = FreshConst(Contribution)  # Create a fresh Contribution variable
    return Exists([elem], IsMember(elem, set_var))


c = Configuration.config(EmptySet(IntSort()))
s = Solver()
s.add(is_non_empty(s, ContributionsInConfig(c)))

print_consistency_analysis_result(s, "First example")

# %% Examples of finding inconsistencies

A = Const('A', SetSort(IntSort()))
e = Int('e')

s = Solver()
s.add(IsMember(e, A), Not(IsMember(e, A)))

print_consistency_analysis_result(s, "self-exclusion")

B = Const('B', SetSort(IntSort()))
C = Const('C', SetSort(IntSort()))

s = Solver()
s.add(IsSubset(A, B), IsSubset(B, C), Not(IsSubset(A, C)))


print_consistency_analysis_result(s, "transitivity violation")

C = Const('C', SetSort(IntSort()))

s = Solver()
s.add(Or(IsMember(e, A), IsMember(e, B)), IsMember(e, C), Not(IsMember(e, C)))

print_consistency_analysis_result(s, "impossible union")
