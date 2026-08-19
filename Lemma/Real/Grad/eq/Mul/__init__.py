from util import *


@apply
def apply(self):
    expr, *limits_d = self.of(Derivative)
    vars = self.variables

    funcs, coeff = std.array_split(expr.of(Mul), lambda arg: arg.has(*vars))
    coeff = Mul(*coeff)
    funcs = Mul(*funcs)
    return Equal(self, coeff * Derivative(funcs, *limits_d))


@prove(proved=False)
def prove(Eq):
    x, h = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Derivative[x](f(x) * h))


if __name__ == '__main__':
    run()
# created on 2022-01-25
del Stack
from . import Grad
from . import Stack
