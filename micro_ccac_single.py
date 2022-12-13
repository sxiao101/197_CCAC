from z3 import *

# this code is done and working
# assume z3 solver is installed and this is readable in z3

# micro CCAC finds variables in which these constraints are sat (part 1 of Matthew's email titled "writeup/example of my thought process")
cwnd0 = Int('cwnd0')
cwnd1 = Int('cwnd1')
cwnd2 = Int('cwnd2')
lost1 = Int('lost1')
lost2 = Int('lost2')

# create a solver
s = Solver()

# Implies: if first statement, then second statement
# Encoding a "bad outcome" in Z3
s.add(cwnd0 == 16)
s.add(Implies(lost1 > 10, cwnd1 == cwnd0/4))
s.add(Implies(lost1 <= 10, cwnd1 == cwnd0+1))
s.add(Implies(lost2 > 10, cwnd2 == cwnd1/4))
s.add(Implies(lost2 <= 10, cwnd2 == cwnd1+1))
s.add(Or(cwnd0 < 2, cwnd1 < 2, cwnd2 < 2))

# check() outputs sat/unsat
result = s.check()
print(result)

# if sat, store variable values that made it sat
# model() outputs values of all variables in s (solver) in mapping e.g. you can access cwnd0 value from s by m[cwnd0].
if (result == sat):
    m = s.model()
    Cwnd0 = m[cwnd0]
    Cwnd1 = m[cwnd1]
    Cwnd2 = m[cwnd2]
    Lost1 = m[lost1]
    Lost2 = m[lost2]
    print(m)

# find a new divide param that works in the prev 'bad' scenario (part 2 of email)
PNew = Int('PNew')

# declare a new solver everytime you are generating some new variable value
s1 = Solver()
s1.add(cwnd0 == 16)
s1.add(Implies(Lost1 > 10, cwnd1 == cwnd0 / PNew))
s1.add(Implies(Lost1 <= 10, cwnd1 == cwnd0 + 1))
s1.add(Implies(Lost2 > 10, cwnd2 == cwnd1 / PNew))
s1.add(Implies(Lost2 <= 10, cwnd2 == cwnd1 + 1))
s1.add(PNew > 1)
s1.add(cwnd0 >= 2, cwnd1 >= 2, cwnd2 >= 2)

result = s1.check()
print(result)

if (result == sat):
    m1 = s1.model()
    PNew1 = m1[PNew]
    Lost1_1 = m1[Lost1]
    Lost2_1 = m1[Lost2]
    print(m1)

# checking that PNew1 works in all settings (part 3 of email)
s2 = Solver()

s2.add(cwnd0 == 16)
s2.add(Implies(lost1 > 10, cwnd1 == cwnd0/PNew1))
s2.add(Implies(lost1 <= 10, cwnd1 == cwnd0+1))
s2.add(Implies(lost2 > 10, cwnd2 == cwnd1/PNew1))
s2.add(Implies(lost2 <= 10, cwnd2 == cwnd1+1))
s2.add(Or(cwnd0 < 2, cwnd1 < 2, cwnd2 < 2))
print(s2.check())
