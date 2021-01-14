from z3 import *

x = BitVec('x', 32)
y = BitVec('y', 32)

solve(x & y == ~y)
solve(x >> 2 == 3)
solve(x << 2 == 3)
solve(x << 2 == 24)
