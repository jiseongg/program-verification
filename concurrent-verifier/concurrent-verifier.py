import sys

from z3 import * 

# global variables
max_step = 0
num_states = 0
num_shared = 0

def encode_logics(A, B, l, A_r, B_r, th_sel, th_A, th_B):
    
    ### target point of interest
    r = len(A)

    ### initial state
    # only A[0][0] is true among A[0]
    init_constraints = [
            A[0][s] if s == 0
            else Not(A[0][s])
            for s in range(len(A[0]))] 
    init_constraints += [
            B[0][s] if s == 0
            else Not(B[0][s])
            for s in range(len(B[0]))] 

    ### only one state is activated
    # e.g. A0_0 -> ~A3_0 (<=> ~A0_0 \/ ~A3_0) 
    unique_state_constraints = []
    for t in range(r):
        for s_A in range(num_states):
            for s_B in range(num_states):
                if s_A != s_B:
                    unique_state_constraints.append(
                            Or(Not(A[t][s_A]), Not(B[t][s_B])))

    



    raise NotImplementedError


def decod_logics(A_sols, B_sols, l_sols, A_r_sols, B_r_sols, th_sel_sols):
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

    # 1) Find all critical sections
    # 2) Find minimum steps to reach possible error state
    min_step = 0
    critical_list_A = []
    critical_list_B = []
    for i, (s_A, s_B) in enumerate(zip(thread_A, thread_B)):
        done_A = False
        done_B = False
        if "critical" in s_A:
            critical_list_A.append(i)
            if not (done_A):
                min_step += i
                done_A = True
        if "critical" in s_B:
            critical_list_B.append(i)
            if not (done_B):
                min_step += i
                done_B = True

    # Solve if mutual exclusion is guaranteed in r-th step
    s = Solver()
    for r in range(min_step, max_step + 1):
        A_states = dict()
        B_states = dict()
        l_shared = dict()
        A_r = []
        B_r = []
        th_sel = []

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

            A_r, B_r: list of boolean variables each mapped to
                the state of critical section 

            th_sel: list of boolean variables that notify next
                executing thread
            '''
            A_states[t] = [Bool('A%d_%d' % (s, t))
                for s in range(num_states)]
            B_states[t] = [Bool('B%d_%d' % (s, t))
                for s in range(num_states)]
            l_shared[t] = [Bool('l%d_%d' % (i, t))
                    for i in range(num_shared)]
            A_r = [Bool('A%d_%d' % (c, r))
                    for c in critical_list_A]
            B_r = [Bool('B%d_%d' % (c, r))
                    for c in critical_list_B]
            th_sel.append(Bool('sel_%d' % t))

        #print(A_states)
        #print(B_states)
        #print(l_shared)
        #print(A_r)
        #print(B_r)
        #print(th_sel)
        F = encode_logics(A_states, B_states, l_shared,
                A_r, B_r, th_sel, thread_A, thread_B)

        s.reset()
        s.add(F)
        res = s.check()
        if r == sat:
            m = s.model()
            A_sols = dict()
            B_sols = dict()
            l_sols = dict()
            A_r_sols = []
            B_r_sols = []
            th_sel_sols = []

            answer = decode_logics(A_sols, B_sols, l_sols,
                    A_r_sols, B_r_sols, th_sel_sols)
            #print(answer)
            sys.exit(0)
        else:
            continue
    
    print('Mutual exclusion is proved')
            

if __name__ == '__main__':
    main()
