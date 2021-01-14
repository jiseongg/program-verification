'''Application of propositional logic

Assign three seats in a row to three persons A, B, C with constraints
- A won't sit next to C
- A won't sit in the leftmost chair
- B won't sit to the right of C

encoding with boolean variable
sit_ij: person i seats in chair j
'''

from z3 import *

sit = [[Bool('sit_%s%s' % (i, j)) for j in range(3)] for i in range(3)]

####### three invariants exist #######
# everyone is seated
I1 = And([Or([sit[i][j] for j in range(3)]) for i in range(3)]) 

# no seat is empty
I2 = And([Or([sit[i][j] for i in range(3)]) for j in range(3)])

# one person cannot sit on multiple seat
I3 = And([Implies(sit[i][j], And([Not(sit[i][k]) for k in range(3) if k != j]))
        for i in range(3) for j in range(3)])


C1 = And(Implies(sit[0][0], Not(sit[2][1])),
         Implies(sit[0][1], And(Not(sit[2][0]), Not(sit[2][2]))),
         Implies(sit[0][2], Not(sit[2][1])))
C2 = Not(sit[0][0])
C3 = And(Implies(sit[2][0], Not(sit[1][1])),
         Implies(sit[2][1], Not(sit[1][2])))

s = Solver()
s.add(And(I1, I2, I3, C1, C2, C3))
r = s.check()
if r == sat:
    print('Solution exsits')
    print(s.model())
else:
    print('Impossible!')
