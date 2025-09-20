from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(Greater)

    return Greater(Integral(lhs, *limits).simplify(), Integral(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Lemma import Calculus, Logic
    x, a, b = Symbol(real=True)

    f, g = Function(shape=(), real=True)

    Eq << apply(Greater(f(x), g(x)), (x, a, b))

    Eq << Eq[0].apply(Logic.AllIn.of.All, (x, a, b))

    Eq << Calculus.GtIntegral.of.All_Gt.ioo.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-05-29

from . import ioo