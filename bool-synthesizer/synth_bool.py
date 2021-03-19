import sys
import re

from z3 import *


def encode_logics(P, Q, Z, pos_inputs, neg_inputs):
    term_cnt = len(P)

    # one of z_ik for kth positive input must be true
    # if z_ik is true
    # 1) ith term cannot contain !x_j, if x_j is True
    # 1) ith term cannot contain x_j, if x_j is False
    positive_constraints = []
    for k, pos_input in enumerate(pos_inputs):
        positive_constraints.append(Or([Z[i][k] for i in range(term_cnt)]))
        for i in range(term_cnt):
            for j, x_j in enumerate(pos_input):
                if x_j == '1':
                    positive_constraints.append(
                            Or(Not(Z[i][k]), Not(Q[i][j])))
                else:
                    positive_constraints.append(
                            Or(Not(Z[i][k]), Not(P[i][j])))

    # for negative input, one of follows are True
    # 1) ith term contain !x_j where x_j is True
    # 2) ith term doesn't contain x_j where x_j is False
    negative_constraints = []
    for k, neg_input in enumerate(neg_inputs):
        for i in range(term_cnt):
            negative_constraints.append(
                    Or([Q[i][j] if x_j == '1'
                        else P[i][j]
                        for j, x_j in enumerate(neg_input)]))

    return positive_constraints + negative_constraints


def decode_logics(P_sols, Q_sols):
    terms = []
    for i, (p_i, q_i) in enumerate(zip(P_sols, Q_sols)):
        term_i_elements = []
        for j, (p_ij, q_ij) in enumerate(zip(p_i, q_i)):
            if p_ij:
                term_i_elements.append('x%d' % (j + 1))
            if q_ij:
                term_i_elements.append('!x%d' % (j + 1))
        term_i_str = ' /\\ '.join(term_i_elements)
        terms.append('(' + term_i_str + ')')

    formula_str = ' \\/ '.join(terms)

    return formula_str


def main():

    if len(sys.argv) < 2:
        print('Usage: %s <program spec> [maximum term count]' % __file__)
        sys.exit(1)
    
    spec_file = sys.argv[1]
    
    with open(spec_file, 'r') as f:
        lines = [s.strip() for s in f.readlines()]
        num_args, num_pos, num_neg = list(map(int, lines[:3]))
        pos_inputs = lines[4:4+num_pos]
        neg_inputs = lines[-num_neg:]

    max_term_cnt = 2 ** (num_args - 1)

    s = Solver()
    for term_cnt in range(1, max_term_cnt + 1):
        P = [[Bool('p_%d%d' % (i, j)) for j in range(num_args)]
                for i in range(term_cnt)]
        Q = [[Bool('q_%d%d' % (i, j)) for j in range(num_args)]
                for i in range(term_cnt)]
        Z = [[Bool('z_%d%d' % (i, j)) for j in range(num_pos)]
                for i in range(term_cnt)]
        F = encode_logics(P, Q, Z, pos_inputs, neg_inputs)

        s = Solver()
        s.add(F)
        r = s.check()
        if r == sat:
            m = s.model()
            P_sols = [[m.evaluate(P[i][j]) for j in range(num_args)]
                    for i in range(term_cnt)]
            Q_sols = [[m.evaluate(Q[i][j]) for j in range(num_args)]
                    for i in range(term_cnt)]
            Z_sols = [[m.evaluate(Z[i][j]) for j in range(num_pos)]
                    for i in range(term_cnt)]
            answer = decode_logics(P_sols, Q_sols)
            print('Learned function with size = %d' % term_cnt)
            print('f(X) = %s' % answer)
            sys.exit(0)
        else:
            continue

    print('no solution exist')


if __name__ == '__main__':
    main()
