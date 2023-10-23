from z3 import *


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

if s.check() == sat:
    print("Model is consistent")
    m = s.model()

else:
    print("Unsatisfiable")
