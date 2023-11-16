from z3 import *

def print_consistency_analysis_result(s, case):
    print("Case being checked: " + case)
    if(s.check() == sat):
        print(case + " is consistent")
    else:
        print("Unsatisfiable theory: " + case)
        print("Unsat core: ", s.unsat_core())

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
s.set(unsat_core=True)

# Adding assertions with tracking predicates
p1 = Bool('p1')
p2 = Bool('p2')
s.assert_and_track(IsMember(e, A), p1)
s.assert_and_track(Not(IsMember(e, A)), p2)

result = s.check()
print_consistency_analysis_result(s, "self-exclusion")

