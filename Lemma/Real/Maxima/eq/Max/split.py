from util import *


@apply
def apply(self, *, cond=None, wrt=None, simplify=True):
    from Lemma.Finset.Sum.eq.AddSumS import split
    return Equal(self, split(Maxima, self, cond, wrt=wrt, simplify=simplify), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Set, Nat, Real

    x = Symbol(integer=True)
    f = Function(real=True)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Maxima[x:A](f(x)), cond=B)

    Eq << Eq[-1].this.find(Maxima).apply(Real.Maxima.Ite)

    Eq << Eq[-1].this.rhs.find(Maxima).apply(Real.Maxima.Ite)

    Eq << Eq[-1].this.rhs.find(Maxima).apply(Real.Maxima.Ite)

    Eq << Eq[-1].this.rhs.apply(Real.Max.eq.Maxima)

    Eq << Eq[-1].this.find(Element).apply(Set.In.Is.In_Inter.ou.In_SDiff, B, simplify=None)

    Eq << Eq[-1].this.find(Piecewise).apply(Nat.Ite.eq.Max)


if __name__ == '__main__':
    run()
# created on 2023-04-23
