from util import *


@apply
def apply(self, index=-1):
    a, b = self.of(Interval)
    kwargs = self.kwargs
    args = a.of(Max)
    former = Max(*args[:index])
    latter = Max(*args[index:])
    return Equal(self, Intersection(Interval(former, b, **kwargs), Interval(latter, b, **kwargs), evaluate=False))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    a, b, c = Symbol(integer=True)
    Eq << apply(Interval(Max(b, c), a))

    Eq << Set.Eq.given.All_Imp.All_Imp.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Set.Ge.Le.of.In_Icc), Eq[-1].this.rhs.apply(Set.In_Ico.given.Ge.Lt)

    Eq <<= Eq[-2].this.find(GreaterEqual).apply(Algebra.And.Ge.of.Ge_Max), Eq[-1].this.find(GreaterEqual).apply(Algebra.Ge_Max.given.And.Ge)

    Eq <<= Eq[-2].this.find(Element).apply(Set.In_Inter.given.And, simplify=None), Eq[-1].this.find(Element).apply(Set.And.of.In_Inter, simplify=None)

    Eq <<= Eq[-2].this.find(Element).apply(Set.In_Ico.given.Ge.Lt), Eq[-1].this.find(Element).apply(Set.Ge.Le.of.In_Icc)

    Eq <<= Eq[-2].this.find(Element).apply(Set.In_Ico.given.Ge.Lt), Eq[-1].this.find(Element).apply(Set.Ge.Le.of.In_Icc)




if __name__ == '__main__':
    run()
# created on 2022-01-08
