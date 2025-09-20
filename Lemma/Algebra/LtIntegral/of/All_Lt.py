from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[Less])
    return Less(Integral(lhs, *limits).simplify(), Integral(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Lemma import Calculus
    x, a, b = Symbol(real=True)
    f, g = Function(shape=(), real=True)

    Eq << apply(All[x:a:b](f(x) < g(x)))

    Eq << Eq[0].reversed

    Eq << Calculus.GtIntegral.of.All_Gt.ioo.apply(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2019-01-29
