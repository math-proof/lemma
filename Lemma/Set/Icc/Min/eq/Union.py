from util import *


@apply
def apply(self, index=-1):
    a, b = self.of(Interval)
    kwargs = self.kwargs
    args = a.of(Min)
    former = Min(*args[:index])
    latter = Min(*args[index:])
    return Equal(self, Union(Interval(former, b, **kwargs), Interval(latter, b, **kwargs), evaluate=False))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    a, b, c = Symbol(integer=True)
    Eq << apply(Interval(Min(b, c), a, right_open=True))

    Eq << Set.Eq.given.All_Imp.All_Imp.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Set.Le.Le.of.In_Icc), Eq[-1].this.rhs.apply(Set.In_Ico.given.Le.Lt)

    Eq <<= Eq[-2].this.find(GreaterEqual).apply(Algebra.Or.Ge.of.Ge_Min), Eq[-1].this.find(GreaterEqual).apply(Algebra.Ge_Min.given.Or.Ge)

    Eq <<= Eq[-2].this.find(Element).apply(Set.In_Union.given.OrInS, simplify=None), Eq[-1].this.find(Element).apply(Set.OrInS.of.In_Union, simplify=None)

    Eq <<= Eq[-2].this.find(Element).apply(Set.In_Ico.given.Le.Lt), Eq[-1].this.find(Element).apply(Set.Le.Le.of.In_Icc)

    Eq <<= Eq[-2].this.find(Element).apply(Set.In_Ico.given.Le.Lt), Eq[-1].this.find(Element).apply(Set.Le.Le.of.In_Icc)




if __name__ == '__main__':
    run()
# created on 2022-01-08
