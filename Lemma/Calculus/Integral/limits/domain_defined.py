from util import *


@apply
def apply(self):
    expr, *limits = self.of(Integral)

    * limits, limit = limits
    x, = limit

    assert x.is_real

    return Equal(self, Integral(expr, *limits, (x, -oo, oo)))


@prove(provable=False)
def prove(Eq):
    x, y, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Integral[x:a:b, y](f(x, y)))


if __name__ == '__main__':
    run()
# created on 2020-06-08

