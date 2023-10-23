from z3 import *

# Create a solver
s = Solver()

# Declare two sets of integers
A = Const('A', SetSort(IntSort()))
B = Const('B', SetSort(IntSort()))

# Declare an integer variable
x = Int('x')

# 1. Set Creation
# Let's assume A = {1, 2, 3} and B = {2, 3, 4}
s.add(A == SetAdd(SetAdd(SetAdd(EmptySet(IntSort()), 1), 2), 3))
s.add(B == SetAdd(SetAdd(SetAdd(EmptySet(IntSort()), 2), 3), 4))

# 2. Basic Set Operations

# Union: A ∪ B
union_A_B = SetUnion(A, B)

# Intersection: A ∩ B
intersection_A_B = SetIntersect(A, B)

# Set Difference: A - B
difference_A_B = SetDifference(A, B)

# Membership: Check if 2 belongs to A
membership = IsMember(2, A)

# Subset: Check if A is a subset of B
subset = IsSubset(A, B)

# Add Boolean assertions to the solver

# Assert that 3 is in the union of A and B
s.add(IsMember(3, union_A_B))

# Assert that 2 belongs to A
s.add(membership)

# Assert if A is a subset of B
s.add(subset)

# Print results
if s.check() == sat:
    m = s.model()
    print("Union:", m.eval(union_A_B))
    print("Intersection:", m.eval(intersection_A_B))
    print("Difference:", m.eval(difference_A_B))
    print("Is 2 in A?", m.eval(membership))
    print("Is A a subset of B?", m.eval(subset))
else:
    print("Unsatisfiable")

# 3. Set Comprehensions: 
# Let's create a set C such that C = {x | x ∈ A and x^2 < 5}. 
# This will include elements from A whose squares are less than 5.
C = Const('C', SetSort(IntSort()))
s.add(ForAll(x, Implies(IsMember(x, C), And(IsMember(x, A), x*x < 5))))
