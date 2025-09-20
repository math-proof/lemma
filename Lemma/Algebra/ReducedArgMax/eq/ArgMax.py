from util import *


@apply
def apply(self, var=None):
    expr = self.of(ReducedArgMax)
    if expr.is_Stack:
        expr, limit = expr.args
        assert not expr.shape
        rhs = ArgMax(expr, limit)
    else:
        n, = expr.shape
        k = self.generate_var(integer=True, var=var)
        rhs = ArgMax[k:n](expr[k])

    return Equal(self, rhs)


@prove(provable=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    f = Function(real=True, shape=())
    i = Symbol(integer=True)
    Eq << apply(ReducedArgMax(Stack[i:n](f(i))))

    


if __name__ == '__main__':
    run()
# created on 2023-11-05
