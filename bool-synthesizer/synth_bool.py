import sys
import re

from z3 import *


def encode_logics(P, Q, Z, pos_inputs, neg_inputs):
    raise NotImplementedError


def decode_logics(P_sols, Q_sols, Z_sols):
    raise NotImplementedError


def main():

    if len(sys.argv) != 2:
        print('Usage: %s <program spec>' % __file__)
        sys.exit()
    else:
        spec_file = sys.argv[1]
    
    with open(spec_file, 'r') as f:
        lines = [s.strip() for s in f.readlines()]
        num_args, num_pos, num_neg = list(map(int, lines[:3]))
        pos_inputs = lines[4:4+num_pos]
        neg_inputs = lines[-num_neg:]

    term_cnt_max = 20
    s = Solver()
    for term_cnt in range(1, term_cnt_max + 1):
        P = [Bool('p_%d%d' % (i, j)) for i in range(term_cnt)
                for j in range(num_args)]
        Q = [Bool('q_%d%d' % (i, j)) for i in range(term_cnt)
                for j in range(num_args)]
        Z = [Bool('z_%d%d' % (i, j)) for i in range(term_cnt)
                for j in range(num_pos)]
        F = encode_logics(P, Q, Z, pos_inputs, neg_inputs)

        s = Solver()
        s.add(F)
        r = s.check()
        if r == sat:
            m = s.model()
            P_sols = [m.evaluate(P[i][j]) for i in range(term_cnt)
                for j in range(num_args)]
            Q_sols = [m.evaluate(Q[i][j]) for i in range(term_cnt)
                for j in range(num_args)]
            Z_sols = [m.evaluate(Z[i][j]) for i in range(term_cnt)
                for j in range(num_pos)]
            answer = decode_logics(P_sols, Q_sols, Z_sols)
            print('Learned function with size = %d' % term_cnt)
            print('f(X) = %s' % answer)
            break
        else:
            continue

    print('no solution exist')


if __name__ == '__main__':
    main()
