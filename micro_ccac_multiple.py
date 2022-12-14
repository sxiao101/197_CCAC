from z3 import *

# assume z3 solver is installed and this is readable in z3

# part 1: micro CCAC finds variables in which these constraints are sat (identify a bad behavior)
cwnd0 = Int('cwnd0')
cwnd1 = Int('cwnd1')
cwnd2 = Int('cwnd2')
lost1 = Int('lost1')
lost2 = Int('lost2')

s = Solver()

s.add(cwnd0 == 32)
s.add(Implies(lost1 > 11, cwnd1 == cwnd0/4))
s.add(Implies(lost1 <= 11, cwnd1 == cwnd0+1))
s.add(Implies(lost2 > 11, cwnd2 == cwnd1/4))
s.add(Implies(lost2 <= 11, cwnd2 == cwnd1+1))
s.add(Or(cwnd0 < 2, cwnd1 < 2, cwnd2 < 2, cwnd1 == 9, cwnd2 == 9))

result = s.check()
print("s result :", result)

# if sat, store variable values that made it sat
if (result == sat):
    m = s.model()
    Lost1 = m[lost1]
    Lost2 = m[lost2]
    print ("Lost1 :", Lost1)
    print ("Lost2 :", Lost2)
    print("m :", m)

result_final = sat

# inside the while loop is similar to micro_ccac_single
# Basically, we want to repeat micro_ccac_single indefinitely until we've found PNew that works.
# we want the final result to be unsat
PNew = Int('PNew')

while (result_final == sat):
    # Part 2: find a new divide param that works in the prev 'bad' scenario

    s1 = Solver()
    s1.add(cwnd0 == 16)
    s1.add(Implies(Lost1 > 10, cwnd1 == cwnd0 / PNew))
    s1.add(Implies(Lost1 <= 10, cwnd1 == cwnd0 + 1))
    s1.add(Implies(Lost2 > 10, cwnd2 == cwnd1 / PNew))
    s1.add(Implies(Lost2 <= 10, cwnd2 == cwnd1 + 1))
    s1.add(PNew > 1)

    # add more cwnd constraints to trigger PNew that takes multiple rounds to be unsat?
    # ask Matthew how to set variable values such that PNew would have to go on for 2+ rounds
    s1.add(cwnd0 >= 2, cwnd1 >= 2, cwnd2 >= 2)
    result = s1.check()
    print(result)
    if (result == sat):
        m1 = s1.model()
        PNew = m1[PNew]
        Lost1_1 = m1[Lost1]
        Lost2_1 = m1[Lost2]
        print(m1)

    # Part 3: check if PNew1 works in all settings
    s2 = Solver()

    s2.add(cwnd0 == 16)
    s2.add(Implies(lost1 > 10, cwnd1 == cwnd0/PNew))
    s2.add(Implies(lost1 <= 10, cwnd1 == cwnd0+1))
    s2.add(Implies(lost2 > 10, cwnd2 == cwnd1/PNew))
    s2.add(Implies(lost2 <= 10, cwnd2 == cwnd1+1))
    s2.add(Or(cwnd0 < 2, cwnd1 < 2, cwnd2 < 2))
    
    result_final = s2.check()
    print(result_final)
    # end while if result_final is unsat.
    # we need to keep putting the variables generated in s2 into s1 and keep the while loop going but I can't figure out how to feed parameters generated here back into s1