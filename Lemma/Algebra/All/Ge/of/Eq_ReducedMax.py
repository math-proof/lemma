from util import *


@apply
def apply(given):
    arg, M = given.of(Equal[ReducedMax])
    fx, *limits = arg.of(Cup[FiniteSet])
    return All(M >= fx, *limits)


@prove
def prove(Eq):
    from Lemma import Algebra

    M, x = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    f = Function(real=True)
    Eq << apply(Equal(M, ReducedMax({f(x): Element(x, S)})))

    Eq << Eq[0].this.rhs.apply(Algebra.ReducedMax.eq.Maxima)

    Eq << Algebra.All.Ge.of.Eq_Maxima.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-01-14
