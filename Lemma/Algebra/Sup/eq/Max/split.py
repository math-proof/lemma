from util import *


@apply
def apply(self, *, cond=None, wrt=None, simplify=True):
    from Lemma.Algebra.Sum.eq.AddSumS import split
    return Equal(self, split(Sup, self, cond, wrt=wrt, simplify=simplify), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    x = Symbol(integer=True)
    f = Function(real=True)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Sup[x:A](f(x)), cond=B)

    Eq << Eq[-1].this.find(Sup).apply(Algebra.Sup.Ite)

    Eq << Eq[-1].this.rhs.find(Sup).apply(Algebra.Sup.Ite)

    Eq << Eq[-1].this.rhs.find(Sup).apply(Algebra.Sup.Ite)

    Eq << Eq[-1].this.rhs.apply(Algebra.Max.eq.Sup)

    Eq << Eq[-1].this.find(Element).apply(Set.In.Is.In_Inter.ou.In_SDiff, B, simplify=None)

    Eq << Eq[-1].this.find(Piecewise).apply(Algebra.Ite.eq.Max)


if __name__ == '__main__':
    run()
# created on 2023-04-23
