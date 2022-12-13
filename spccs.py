from z3 import And, Not, Or, Context
from typing import Any, List, Optional, Tuple
from config import ModelConfig
from model import make_solver
from plot import plot_model
from pyz3_utils import MySolver, run_query
from utils import make_periodic
from variables import VariableNames
import math
import matplotlib.pyplot as plt

#run using CLI python3 spccs.py --cmnd aimd_premature_loss --vars alpha

def aimd_premature_loss(variables, timeout=60):
    '''Finds a case where AIMD bursts 2 BDP packets where buffer size = 2 BDP and
    cwnd <= 2 BDP. Here 1BDP is due to an ack burst and another BDP is because
    AIMD just detected 1BDP of loss. This analysis created the example
    discussed in section 6 of the paper. As a result, cwnd can reduce to 1 BDP
    even when buffer size is 2BDP, whereas in a fluid model it never goes below
    1.5 BDP.

    '''
    c = ModelConfig.default()
    c.cca = "aimd"
    c.buf_min = 2
    c.buf_max = 2
    c.simplify = False
    c.T = 5

    s, v = make_solver(c)

    add_aimd_constraints(c, s, v)

    print(s.to_smt2(), file = open("/tmp/aimd_premature_loss.smt2", "w"))

    results = []
    end_runs = False # turns true when the solver is unsat

    # search exponentially lower and higher to find the range to binary search
    # store upper and lower bounds
    #binary search for actually lower and upper bound

    # should all variable be lower bounded at 0?
    lower_bounds = {}
    upper_bounds = {}

    qres = run_query(c, s, v, timeout)
    if qres.satisfiable == "sat":
        for var in variables:
            lower_bounds[var]  = (qres.v.__dict__[var] - qres.v.__dict__[var], qres.v.__dict__[var])
            upper_bounds[var] = (qres.v.__dict__[var], qres.v.__dict__[var] + qres.v.__dict__[var])
            finding_lower = True
            finding_upper = True

            #find lower bound
            s_lower, v_lower = make_solver(c)
            add_aimd_constraints(c, s_lower, v_lower)
            while finding_lower:
                lower, upper = lower_bounds[var]
                print(lower)
                s_lower.add(v_lower.__dict__[var] < lower)
                qres = run_query(c, s_lower, v_lower, timeout)
                print(qres.satisfiable)
                if qres.satisfiable != "sat":
                    finding_lower = False
                else:
                    if lower == 0:
                        lower_bounds[var] = (-last_lower, lower)
                    else:
                        lower_bounds[var] = ((lower-lower), lower)
                    if lower-lower == 0:
                        last_lower = lower

            # find upper bound
            s_upper, v_upper = make_solver(c)
            add_aimd_constraints(c, s_upper, v_upper)
            while finding_upper:
                lower, upper = upper_bounds[var]
                print(upper)
                s_upper.add(v_upper.__dict__[var] > upper)
                qres = run_query(c, s_upper, v_upper, timeout)
                print(qres.satisfiable)
                if qres.satisfiable != "sat":
                    finding_upper = False
                else:
                    upper_bounds[var] = (upper, (upper + upper))

            print((lower_bounds[var][0], upper_bounds[var][1]))
            # narrowing down on lower bound:
            lower_interval = binary_check_lower_bound(c, var, lower_bounds[var][0], lower_bounds[var][1], 5, timeout)
            # narrowing down on upper bound:
            upper_interval = binary_check_upper_bound(c, var, upper_bounds[var][0], upper_bounds[var][1], 5, timeout)
            print("Interval for lower bound:")
            print(lower_interval)
            print("Interval for upper bound:")
            print(upper_interval)
    else:
        print("unsatisfiable network conditions")

    # keeps finding discrete new solutions
    # while not end_runs:
    #     print("new round")
    #     qres = run_query(c, s, v, timeout)
    #     print(qres.satisfiable)
    #     if qres.satisfiable == "sat":
    #         temp = VariableNames(qres.v)
    #         res = {}
    #         for var in variables:
    #             if type(temp.__dict__[var]) == list:
    #                 conds_list = []
    #                 helper(conds_list, s, v.__dict__[var], qres.v.__dict__[var], temp.__dict__[var])
    #                 s.add(Or(*conds_list))
    #             else:
    #                 s.add(v.__dict__[var] != qres.v.__dict__[var])
    #             res[var] = qres.v.__dict__[var]
    #         results.append(res)
    #         print(results)
    #
    #     else:
    #         end_runs = True

    # for k in qres.model:
    #     print(k)
    # if str(qres.satisfiable) == "sat":
        #plot_model(qres.model, c, qres.v)


def binary_check_lower_bound(c, var, low, high, max_iter, timeout):
    print("starting binary check")
    count = 0
    res = [low, high]
    s, v = make_solver(c)
    add_aimd_constraints(c, s, v)
    s.add(v.__dict__[var] < high)
    while high >= low and count < max_iter:
        mid = (high + low) / 2
        s.add(v.__dict__[var] < mid)
        qres = run_query(c, s, v, timeout)
        print(qres.satisfiable)
        if qres.satisfiable == "sat":
            res[1] = mid
            high = mid
        else:
            res[0] = mid
            low = mid
            s, v = make_solver(c)
            add_aimd_constraints(c, s, v)
            s.add(v.__dict__[var] < high)

        count += 1
    return res

def binary_check_upper_bound(c, var, low, high, max_iter, timeout):
    print("starting upper binary check")
    count = 0
    res = [low, high]
    s, v = make_solver(c)
    add_aimd_constraints(c, s, v)
    s.add(v.__dict__[var] > low)
    while high >= low and count < max_iter:
        mid = (high + low) / 2
        s.add(v.__dict__[var] > mid)
        qres = run_query(c, s, v, timeout)
        print(qres.satisfiable)
        if qres.satisfiable == "sat":
            res[0] = mid
            low = mid
        else:
            res[1] = mid
            high = mid
            s, v = make_solver(c)
            add_aimd_constraints(c, s, v)
            s.add(v.__dict__[var] > low)

        count += 1
    return res

def add_aimd_constraints(c, s, v):
    # Start with zero loss and zero queue, so CCAC is forced to generate an
    # example trace *from scratch* showing how bad behavior can happen in a
    # network that was perfectly normal to begin with
    s.add(v.L[0] == 0)
    # Restrict alpha to small values, otherwise CCAC can output obvious and
    # uninteresting behavior
    s.add(v.alpha <= 0.1 * c.C * c.R)

    # Does there exist a time where loss happened while cwnd <= 1?
    conds = []
    for t in range(2, c.T - 1):
        conds.append(
            And(
                v.c_f[0][t] <= 2,
                v.Ld_f[0][t + 1] - v.Ld_f[0][t] >=
                1,  # Burst due to loss detection
                v.S[t + 1 - c.R] - v.S[t - c.R] >=
                c.C + 1,  # Burst of BDP acks
                v.A[t + 1] >=
                v.A[t] + 2,  # Sum of the two bursts
                v.L[t + 1] > v.L[t]
            ))

    # We don't want an example with timeouts
    for t in range(c.T):
        s.add(Not(v.timeout_f[0][t]))

    s.add(Or(*conds))
    s.add((v.aimd_factor == 2.0))

def helper(l, s, left, right, sol):
    if type(sol) != list:
        l.append((left != right))
    else:
        for i in range(len(sol)):
            helper(l, s, left[i], right[i], sol[i])

if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser()

    funcs = {
        "aimd_premature_loss": aimd_premature_loss,
    }
    usage = f"Usage: python3 example_queries.py <{'|'.join(funcs.keys())}>"

    CLI = argparse.ArgumentParser()
    CLI.add_argument(
        "--cmnd",  # name on the CLI - drop the `--` for positional/required parameters
        type=str,
        default="aimd_premature_loss",
    )
    CLI.add_argument(
        "--vars",
        nargs="*",
        type=str,  # any type/callable can be used here
        default=[],
    )

    # parse the command line
    args = CLI.parse_args()


    # if len(sys.argv) != 4:
    #     print("Expected exactly one command")
    #     print(usage)
    #     exit(1)
    cmd = args.cmnd
    if cmd in funcs:
        funcs[cmd](args.vars)
    else:
        print("Command not recognized")
        print(usage)
