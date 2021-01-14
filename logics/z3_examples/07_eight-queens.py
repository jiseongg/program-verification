'''Application of FOL on integer theory

Placing eight chess queens on an 8x8 chessboard
so that no two queens share the same row, column,
or diagonal

encoding with integer variable
Q_i: the column position of the queen in row i
'''

from z3 import *

Q = [Int('Q_%s' % i) for i in range(8)]

##### three constraints #####
# column range
col_range = [And(0 <= Q[i], Q[i] <= 7) for i in range(8)]

# no columns are shared
col_no_share = [
        Implies(i != j, Q[i] != Q[j])
        for i in range(8) for j in range(8)]

# no diagonals are shared
diag_no_share = [
        Implies(i != j, And(Q[i] - Q[j] != i - j, Q[i] - Q[j] != j - i))
        for i in range(8) for j in range(8)]

s = Solver()
s.add(col_range + col_no_share + diag_no_share)
r = s.check()

if r == sat:
    m = s.model()
    cols = [m.evaluate(Q[i]) for i in range(8)]

    # print answer
    for i in range(8):
        for j in range(8):
            if cols[i] == j:
                print(1, end=' ')
            else:
                print(0, end=' ')
        print('')
else:
    print('Impossible')
