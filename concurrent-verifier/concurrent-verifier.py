import sys
import pprint

from z3 import * 

# global variables
max_step = 0
num_states = 0
num_shared = 0

def encode_logics(A, B, l, th_sel_A, th_sel_B, th_A, th_B):
    
    global max_step
    global num_states
    global num_shared

    ### target point of interest
    r = len(A) - 1

    ### initial state
    # 1) only A[0][0] is true among A[0]
    # 2) all shared variables are zero.
    init_constraints = [
            A[0][s] if s == 0
            else Not(A[0][s])
            for s in range(len(A[0]))] 
    init_constraints += [
            B[0][s] if s == 0
            else Not(B[0][s])
            for s in range(len(B[0]))] 
    init_constraints += [
            Not(v) for v in l[0]]
    #print('========== init_constraints ==========')
    #pprint.pprint(init_constraints)
    #print()

    ### only one thread can be executed in one step
    unique_thread_constraints = [
            p == Not(q)
            for p, q in zip(th_sel_A, th_sel_B)]
    #print('========== unique_thread_constraints ==========')
    #pprint.pprint(unique_thread_constraints)
    #print()

    ### only one state is activated
    # e.g. A0_0 -> ~A3_0 (<=> ~A0_0 \/ ~A3_0) 
    unique_state_constraints = []
    for t in range(r + 1):
        for i in range(num_states):
            for j in range(num_states):
                if i != j:
                    unique_state_constraints.append(
                            Or(Not(A[t][i]), Not(A[t][j])))
                    unique_state_constraints.append(
                            Or(Not(B[t][i]), Not(B[t][j])))
    #print('========== unique_state_constraints ==========')
    #pprint.pprint(unique_state_constraints)
    #print()

    ### build constraints for each statement
    def encode_semantics(s_idx, stmt, th_sel, th):
        stmt_split = stmt.split(' ')
        cmd = stmt_split[0]
        constraints = []
        if cmd == 'maybe':
            s_next = int(stmt_split[1])
            constraints += [
                    Or(th_sel[t], Not(th[t][s_idx]), th[t+1][s_idx])
                    for t in range(r)]
            constraints += [
                    Or(Not(th_sel[t]), Not(th[t][s_idx]), th[t+1][s_idx], th[t+1][s_next])
                    for t in range(r)]

        elif cmd == 'if':
            cond, if_s, else_s = list(map(int, stmt_split[1:]))
            constraints += [
                    Or(th_sel[t], Not(th[t][s_idx]), th[t+1][s_idx])
                    for t in range(r)]
            constraints += [
                    Or(Not(th_sel[t]), Not(th[t][s_idx]), Not(l[t][cond]), th[t+1][if_s])
                    for t in range(r)]
            constraints += [
                    Or(Not(th_sel[t]), Not(th[t][s_idx]), l[t][cond], th[t+1][else_s])
                    for t in range(r)]

        elif cmd == "set":
            sh_var, val, s_next = list(map(int, stmt_split[1:]))

            constraints += [
                    Or(th_sel[t], Not(th[t][s_idx]), th[t+1][s_idx])
                    for t in range(r)]
            constraints += [
                    Or(Not(th_sel[t]), Not(th[t][s_idx]), th[t+1][s_next])
                    for t in range(r)]

            if val != 0:
                constraints += [
                        Or(Not(th_sel[t]), Not(th[t][s_idx]),
                            And(l[t+1][sh_var],
                                And([l[t][sh_other] == l[t+1][sh_other]
                                    for sh_other in range(num_shared)
                                    if sh_other != sh_var])))
                        for t in range(r)]
            else:
                constraints += [
                        Or(Not(th_sel[t]), Not(th[t][s_idx]),
                            And(Not(l[t+1][sh_var]),
                                And([l[t][sh_other] == l[t+1][sh_other]
                                    for sh_other in range(num_shared)
                                    if sh_other != sh_var])))
                        for t in range(r)]

        elif cmd == "critical":
            s_next = int(stmt_split[1])

            constraints += [
                    Or(th_sel[t], Not(th[t][s_idx]), th[t+1][s_idx])
                    for t in range(r)]
            constraints += [
                    Or(Not(th_sel[t]), Not(th[t][s_idx]), th[t+1][s_next])
                    for t in range(r)]

        return constraints

    transition_constraints = []
    for s_idx, (stmt_A, stmt_B) in enumerate(zip(th_A, th_B)):
        transition_constraints += encode_semantics(s_idx, stmt_A, th_sel_A, A)
        transition_constraints += encode_semantics(s_idx, stmt_B, th_sel_B, B)
    #print('========== transition_constraints ==========')
    #pprint.pprint(transition_constraints)
    #print()

    ### invariants for shared variables
    invariants_shared = []
    set_stmt_A = [s_idx
            for s_idx, stmt in enumerate(th_A)
            if "set" in stmt]
    set_stmt_B = [s_idx
            for s_idx, stmt in enumerate(th_B)
            if "set" in stmt]
    for t in range(r):
        in_set_stmt_A = Or([A[t][idx] for idx in set_stmt_A])
        in_set_stmt_B = Or([B[t][idx] for idx in set_stmt_B])
        for sh_idx in range(num_shared):
            invariants_shared += [
                    Or(Not(th_sel_A[t]), l[t][sh_idx],
                        in_set_stmt_A, Not(l[t+1][sh_idx]))]
            invariants_shared += [
                    Or(Not(th_sel_A[t]), Not(l[t][sh_idx]),
                        in_set_stmt_A, l[t+1][sh_idx])]
            invariants_shared += [
                    Or(Not(th_sel_B[t]), l[t][sh_idx],
                        in_set_stmt_B, Not(l[t+1][sh_idx]))]
            invariants_shared += [
                    Or(Not(th_sel_B[t]), Not(l[t][sh_idx]),
                        in_set_stmt_B, l[t+1][sh_idx])]

    for t in range(r):
        for sh_idx in range(num_shared):
            invariants_shared.append(
                    Implies(l[t][sh_idx] != l[t+1][sh_idx],
                    And([l[t][sh_other] == l[t+1][sh_other]
                        for sh_other in range(num_shared)
                        if sh_other != sh_idx])))

    #print('========== invariants_shared ==========')
    #pprint.pprint(invariants_shared)
    #print()

    return init_constraints + unique_thread_constraints + \
            unique_state_constraints + transition_constraints + \
            invariants_shared

def decod_logics(A_sols, B_sols, l_sols, A_r_sols, B_r_sols, th_sel_sols):
    '''TODO'''
    raise NotImplementedError


def main():

    global max_step
    global num_states
    global num_shared

    if len(sys.argv) < 2:
        print('Usage: %s <program spec>' % __file__)
        sys.exit(1)
    
    model_file = sys.argv[1]

    with open(model_file, 'r') as f:
        lines = [s.strip() for s in f.readlines()]
        max_step, num_states, num_shared = list(map(int, lines[:3]))
        thread_A = list(map(lambda x: x[2:], lines[4:4+num_states]))
        thread_B = list(map(lambda x: x[2:], lines[-num_states:]))

    # Find all critical sections
    critical_list_A = []
    critical_list_B = []
    for i, (s_A, s_B) in enumerate(zip(thread_A, thread_B)):
        if "critical" in s_A:
            critical_list_A.append(i)
        if "critical" in s_B:
            critical_list_B.append(i)

    # Solve if mutual exclusion is guaranteed in r-th step
    s = Solver()
    for r in range(1, max_step + 1):
        A_states = dict()
        B_states = dict()
        l_shared = dict()
        th_sel_A = []
        th_sel_B = []

        for t in range(r + 1):
            '''
            A_states: {
                0:      [A0_0, A1_0, ..., An_0],
                1:      [A0_1, A1_1, ..., An_1],
                ...
                r: [A0_r, A1_r, ..., An_r],
            }
            As_t: thread A is in the s-th state in the step `t`

            l_shared: {
                0:      [l0_0, l1_0, ..., li_0],
                1:      [l0_1, l1_1, ..., li_1],
                ...
                r: [l0_r, l1_r, ..., li_r],
            }
            li_t: the i-th shared variable is 1 in the step `t`

            th_sel_A, th_sel_B: which thread will be executed?
            '''
            A_states[t] = [Bool('A%d_%d' % (s, t))
                for s in range(num_states)]
            B_states[t] = [Bool('B%d_%d' % (s, t))
                for s in range(num_states)]
            l_shared[t] = [Bool('l%d_%d' % (i, t))
                    for i in range(num_shared)]
            th_sel_A.append(Bool('sel_A_%d' % t))
            th_sel_B.append(Bool('sel_B_%d' % t))

        F = encode_logics(A_states, B_states, l_shared,
                th_sel_A, th_sel_B, thread_A, thread_B)

        # error_condition
        error_condition = Or([
                And(A_states[r][a_idx], B_states[r][b_idx])
                for a_idx in critical_list_A
                for b_idx in critical_list_B])
        #print('========== error_condition ==========')
        #pprint.pprint(error_condition)
        #print()

        s.reset()
        s.add(F + [error_condition])
        res = s.check()
        if res == sat:
            m = s.model()
            A_sols = {t: list(map(lambda x: m.evaluate(x), var_list))
                    for t, var_list in A_states.items()}
            B_sols = {t: list(map(lambda x: m.evaluate(x), var_list))
                    for t, var_list in B_states.items()}
            l_sols = {t: list(map(lambda x: m.evaluate(x), var_list))
                    for t, var_list in l_shared.items()}
            th_sel_A_sols = list(map(lambda x: m.evaluate(x), th_sel_A))
            th_sel_B_sols = list(map(lambda x: m.evaluate(x), th_sel_B))

            #print('========== A_sols ==========')
            #pprint.pprint(A_sols)
            #print()

            #print('========== B_sols ==========')
            #pprint.pprint(B_sols)
            #print()

            #print('========== l_sols ==========')
            #pprint.pprint(l_sols)
            #print()

            #print('========== th_sel_A_sols ==========')
            #pprint.pprint(th_sel_A_sols)
            #print()

            #print('========== th_sel_B_sols ==========')
            #pprint.pprint(th_sel_B_sols)
            #print()

            print('Mutual exclusion could be violated in %d step: ' % r)

            #answer = decode_logics(A_sols, B_sols, l_sols,
            #        A_r_sols, B_r_sols, th_sel_A_sols)
            #print(answer)

            sys.exit(0)
        else:
            print('Safe when r is %d' % r)
            continue
    
    print('Mutual exclusion is proved within %d steps' % max_step)
            

if __name__ == '__main__':
    main()
