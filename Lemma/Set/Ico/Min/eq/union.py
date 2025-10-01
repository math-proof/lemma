from util import *


@apply
def apply(self, index=-1):
    a, b = self.of(Range)
    args = a.of(Min)
    former = Min(*args[:index])
    latter = Min(*args[index:])
    return Equal(self, Union(Range(former, b), Range(latter, b), evaluate=False))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    a, b, c = Symbol(integer=True)
    Eq << apply(Range(Min(b, c), a))

    Eq << Set.Eq.given.All_Imp.All_Imp.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Set.Ge.Le_Sub_1.of.In_Ico), Eq[-1].this.rhs.apply(Set.In_Ico.given.And)

    Eq <<= Eq[-2].this.find(GreaterEqual).apply(Algebra.Or.Ge.of.Ge_Min), Eq[-1].this.find(GreaterEqual).apply(Algebra.Ge_Min.given.Or.Ge)

    Eq <<= Eq[-2].this.find(Element).apply(Set.In_Union.given.OrInS, simplify=None), Eq[-1].this.find(Element).apply(Set.OrInS.of.In_Union, simplify=None)

    Eq <<= Eq[-2].this.find(Element).apply(Set.In_Ico.given.And), Eq[-1].this.find(Element).apply(Set.Ge.Le_Sub_1.of.In_Ico)

    Eq <<= Eq[-2].this.find(Element).apply(Set.In_Ico.given.And), Eq[-1].this.find(Element).apply(Set.Ge.Le_Sub_1.of.In_Ico)




if __name__ == '__main__':
    run()
# created on 2022-01-08
