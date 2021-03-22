import sys

from z3 import * 


def encode_logics(A, B, l, th_A, th_B):
    '''TODO'''
    raise NotImplementedError


def decod_logics(A_sols, B_sols, l_sols):
    '''TODO'''
    raise NotImplementedError


def main():

    if len(sys.argv) < 2:
        print('Usage: %s <program spec>' % __file__)
        sys.exit(1)
    
    model_file = sys.argv[1]
    
    with open(model_file, 'r') as f:
        lines = [s.strip() for s in f.readlines()]
        max_step, num_states, num_shared = list(map(int, lines[:3]))
        thread_A = lines[4:4+num_states]
        thread_B = lines[-num_states:]

    # Find minimum steps to reach possible error state
    min_step = 0
    for i, (s_A, s_B) in enumerate(zip(thread_A, thread_B)):
        done_A = False
        done_B = False
        if ("critical" in s_A) and (not done_A):
            min_step += i
        if ("critical" in s_B) and (not done_B):
            min_step += i

    # Solve if mutual exclusion is guaranteed in r-th step
    s = Solver()
    for r in range(min_step, max_step + 1):
        A_states = dict()
        B_states = dict()
        l_shared = dict()

        for t in range(r):
            '''
            A_states: {
                0:      [A0_0, A1_0, ..., An_0],
                1:      [A0_1, A1_1, ..., An_1],
                ...
                r - 1 : [A0_`r-1`, A1_`r-1`, ..., An_`r-1`],
            }
            As_t: thread A is in the s-th state in the step `t`

            l_shared: {
                0:      [l0_0, l1_0, ..., li_0],
                1:      [l0_1, l1_1, ..., li_1],
                ...
                r - 1 : [l0_`r-1`, l1_`r-1`, ..., li_`r-1`],
            }
            li_t: the i-th shared variable is 1 in the step `t`
            '''
            A_states[t] = [Bool('A%d_%d' % (s, t))
                for s in range(num_states)]
            B_states[t] = [Bool('B%d_%d' % (s, t))
                for s in range(num_states)]
            l_shared[t] = [Bool('l%d_%d' % (i, t))
                    for i in range(num_shared)]

        F = encode_logics(A_states, B_states, l_shared,
                thread_A, thread_B)

        s.reset()
        s.add(F)
        res = s.check()
        if r == sat:
            m = s.model()
            A_sols = dict()
            B_sols = dict()
            l_sols = dict()
            answer = decode_logics(A_sols, B_sols, l_sols)
            print(answer)
            sys.exit(0)
        else:
            continue
    
    print('Mutual exclusion is proved')
            

if __name__ == '__main__':
    main()
