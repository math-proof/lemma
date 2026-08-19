from util import *


@apply
def apply(self):
    expr, *limits_d = self.of(Integral)
    vars = [var for var, *_ in limits_d]
    funcs, coeff = std.array_split(expr.of(Mul), lambda arg: arg.has(*vars))
    coeff = Mul(*coeff)
    funcs = Mul(*funcs)
    return Equal(self, coeff * Integral(funcs, *limits_d))


@prove
def prove(Eq):
    x, h = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Integral[x](f(x) * h))

    Eq << Eq[-1].this.lhs.simplify()


if __name__ == '__main__':
    run()
# created on 2023-03-27


del Bool
del Limit
from . import Bool
from . import Limit
