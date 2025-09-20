from util import *


@apply
def apply(given):
    (expr, limit), x0 = given.of(Equal[ArgMax])
    return All(GreaterEqual(expr._subs(limit[0], x0), expr), limit)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, x0 = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    f = Function(real=True)
    Eq << apply(Equal(x0, ArgMax[x:S](f(x))))

    Eq << Algebra.EqArgMax.of.Eq.definition.apply(Eq[0])

    Eq << Algebra.All.Ge.of.Eq_Maxima.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2019-04-13
# updated on 2023-11-05
