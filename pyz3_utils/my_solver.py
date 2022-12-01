from typing import Any, List, Set
from z3 import ArithRef, Bool, BoolRef, Function, FuncDeclRef, Int, Real,\
    Solver


def extract_vars(e: BoolRef) -> List[str]:
    if e.children() == []:
        if str(e)[:4] == "Var(":
            return []
        elif type(e) == ArithRef or type(e) == BoolRef\
                or type(e) == FuncDeclRef:
            return [str(e)]
        else:
            return []
    else:
        res = []
        for x in e.children():
            res += extract_vars(x)
        return res


class MySolver:
    '''A thin wrapper over z3.Solver'''

    def __init__(self, ctx=None):
        self.s = Solver(ctx=ctx)
        # If ctx=None, we're using the global context. This means that in any
        # assertions testing equality of ctx, None will get compared to
        # None. If ctx!=None, we ensure the right context is being used
        self.ctx = ctx
        self.num_constraints = 0
        self.variables = {"False", "True"}
        self.track_unsat = False
        self.assertion_list = []
        self.warn_undeclared = True

    def check_expr(self, expr):
        if(type(expr) == bool):
            return True
        for var in extract_vars(expr):
            if not self.warn_undeclared:
                self.variables.add(var)
            if var not in self.variables:
                print(f"Warning: {var} in {str(expr)} not previously declared")
                return False
        return True

    def add(self, expr):
        assert type(expr) != bool
        assert self.check_expr(expr)
        self.assertion_list.append(expr)
        if self.track_unsat:
            self.s.assert_and_track(expr,
                                    str(expr) + f"  :{self.num_constraints}")
            self.num_constraints += 1
        else:
            self.s.add(expr)

    def set(self, **kwds):
        if "unsat_core" in kwds and kwds["unsat_core"]:
            self.track_unsat = True
        return self.s.set(**kwds)

    def check(self):
        return self.s.check()

    def model(self):
        return self.s.model()

    def push(self):
        self.s.push()

    def pop(self):
        self.s.pop()

    def unsat_core(self):
        # assert(self.track_unsat)
        return self.s.unsat_core()

    def to_smt2(self):
        return self.s.to_smt2()

    def statistics(self):
        return self.s.statistics()

    def assertions(self):
        return self.s.assertions()

    def translate(self, ctx):
        return self.s.translate(ctx)

    def Real(self, name: str, ctx=None):
        assert ctx == self.ctx
        if name in self.variables:
            print(f"Warning: {name} declared previously.")
        self.variables.add(name)
        return Real(name, ctx)

    def Function(self, name: str, t1, t2):
        if name in self.variables:
            print(f"Warning: {name} declared previously.")
        self.variables.add(name)
        # Takes ctx from t1, t2
        return Function(name, t1, t2)

    def Int(self, name: str, ctx=None):
        assert ctx == self.ctx
        if name in self.variables:
            print(f"Warning: {name} declared previously.")
        self.variables.add(name)
        return Int(name, ctx=ctx)

    def Bool(self, name: str, ctx=None):
        assert ctx == self.ctx
        if name in self.variables:
            print(f"Warning: {name} declared previously.")
        self.variables.add(name)
        return Bool(name, ctx=ctx)
