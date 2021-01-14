from z3 import *

X = [Int('x%s' % i) for i in range(5)]
Y = [Int('y%s' % i) for i in range(5)]
print(X, Y)

X_plus_Y = [X[i] + Y[i] for i in range(5)]
X_gt_Y = [X[i] > Y[i] for i in range(5)]
print(X_plus_Y)
print(X_gt_Y)

a = And(X_gt_Y)
print(a)

solve(a)

