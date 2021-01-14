from z3 import *

x = Int('x')
y = Int('y')
solve(x > 2, y < 10, x + 2*y == 7)

x = Real('x')
y = Real('y')
solve(x**2 + y**2 > 3, x**3 + y < 5)
