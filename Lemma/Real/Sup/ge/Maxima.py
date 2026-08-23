from util import *


@apply
def apply(sup):
    fx, *limits = sup.of(Sup)
    return sup >= Maxima(fx, *limits)


@prove
def prove(Eq):
    from Lemma import Bool, Real, Tensor

    x = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    f = Function(real=True)
    Eq << apply(Sup[x:S](f(x)))

    Eq << Eq[0].this.lhs.apply(Real.Sup.eq.ReducedMin)

    Eq << Eq[-1].this.lhs.apply(Tensor.ReducedMin.eq.Minima)

    Eq << Real.GeMinima.given.All.Ge.apply(Eq[-1])

    Eq << Bool.All.given.Imp.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Real.LeMaxima.of.All_Le)


if __name__ == '__main__':
    run()
# created on 2019-09-21
