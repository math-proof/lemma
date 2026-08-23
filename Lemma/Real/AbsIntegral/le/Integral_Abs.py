from util import *


@apply
def apply(self):
    expr, *limits = self.of(Integral)
    return abs(self) <= Integral(abs(expr), *limits)


@prove
def prove(Eq):
    from Lemma import Real, Int

    f = Function(real=True, continuous=True)
    x, a, b = Symbol(real=True)
    Eq << apply(Integral[x:a:b](f(x)))

    Eq << Int.LeAbs.given.And.apply(Eq[0])

    Eq << Int.GeAbs.apply(f(x))

    Eq << Real.LeIntegral.of.Le.apply(Eq[-1], (x, a, b))

    Eq << Int.LeNegAbs.apply(f(x))

    Eq << Real.GeIntegral.of.Ge.apply(Eq[-1], (x, a, b))




if __name__ == '__main__':
    run()
# created on 2023-04-03
