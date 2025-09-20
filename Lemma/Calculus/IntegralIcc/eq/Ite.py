from util import *


@apply
def apply(self):
    fx, (x, E) = self.of(Integral)
    a, b = E.of(Interval)
    return Equal(self, Piecewise((Integral[x:a:b](fx), a < b), (0, True)))


@prove(provable=False)
def prove(Eq):
    x, a, b = Symbol(real=True)
    f = Function(real=True, integrable=True)
    Eq << apply(Integral[x:Interval(a, b)](f(x)))


if __name__ == '__main__':
    run()
# created on 2020-05-23
