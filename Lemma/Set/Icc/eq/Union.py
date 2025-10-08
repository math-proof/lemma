from util import *


@apply
def apply(self, pivot=None):
    a, b = self.of(Interval)
    assert self.conditionally_contains(pivot)
    A = self.copy(stop=pivot, right_open=True)
    B = self.copy(start=pivot, left_open=False)
    return Equal(self, Union(A, B, evaluate=False))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    a, b = Symbol(integer=True)
    c = Symbol(domain=Interval(a, b, left_open=True, right_open=True))
    Eq << apply(Interval(a, b), c)

    Eq << Set.Eq.given.All_Imp.All_Imp.apply(Eq[0])

    Eq <<= Eq[-2].this.find(Element[Interval]).apply(Set.In_Icc.Is.And), Eq[-1].this.find(Element[Interval]).apply(Set.In_Icc.Is.And)

    Eq <<= Eq[-2].this.find(Element[Union]).apply(Set.In_Union.Is.OrInS), Eq[-1].this.find(Element[Union]).apply(Set.In_Union.Is.OrInS)

    Eq <<= Eq[-2].this.find(Element).apply(Set.In_Icc.Is.And), Eq[-1].this.find(Element).apply(Set.In_Icc.Is.And)

    Eq <<= Eq[-2].this.find(Element).apply(Set.In_Icc.Is.And), Eq[-1].this.find(Element).apply(Set.In_Icc.Is.And)

    Eq << Bool.ImpOr.given.Imp.Imp.apply(Eq[-1])

    Eq <<= Bool.Imp_And.given.Imp.delete.apply(Eq[-2]), Bool.Imp_And.given.Imp.delete.apply(Eq[-1], 0)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ge.of.Ge.relax, a)

    Eq << Eq[-2].this.lhs.apply(Algebra.Lt.of.Lt.relax, b)

    Eq << Bool.Imp.given.Or_Not.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-04-18
