'''Encoding if-then-else construct to propositional logic

if x then y else z == (x && y) || (~x && z)

Application: program equivalence
    1) input code on compiler optimizer
        if (!a && !b) then h
        else if (!a) then g else f

    2) optimized code
        if (a) then f
        else if (b) then g else h

    3) encoded PL
        F: F1 <-> F2, where
        F1: ((~a && ~b) && h) || (~(~a && ~b) && ((~a && g) || (a && f)))
        F2: (a && f) || (~a && ((b && g) || (~b && h)))
'''

from z3 import *

a = Bool('a')
b = Bool('b')
f = Bool('f')
g = Bool('g')
h = Bool('h')

F1 = Or(And(Not(a), Not(b), h),
        And(Not(And(Not(a), Not(b))), Or(And(Not(a), g), And(a, f))))
F2 = Or(And(a, f),
        And(Not(a), Or(And(b, g), And(Not(b), h))))
F = F1 == F2

s = Solver()
s.add(Not(F))
r = s.check()

if r == unsat:
    print('proved')
else:
    print('counterexample exists!')
    print(s.model())



