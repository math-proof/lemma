from util import *


@apply
def apply(self, index=-1):
    a, b = self.of(Range)
    args = a.of(Max)
    former = Max(*args[:index])
    latter = Max(*args[index:])
    return Equal(self, Intersection(Range(former, b), Range(latter, b), evaluate=False))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    a, b, c = Symbol(integer=True)
    Eq << apply(Range(Max(b, c), a))

    Eq << Set.Eq.given.All_Imp.All_Imp.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Set.And.of.In_Range), Eq[-1].this.rhs.apply(Set.In_Range.given.And)

    Eq <<= Eq[-2].this.find(GreaterEqual).apply(Algebra.And.Ge.of.Ge_Max), Eq[-1].this.find(GreaterEqual).apply(Algebra.Ge_Max.given.And.Ge)

    Eq <<= Eq[-2].this.find(Element).apply(Set.In_Inter.given.And, simplify=None), Eq[-1].this.find(Element).apply(Set.And.of.In_Inter, simplify=None)

    Eq <<= Eq[-2].this.find(Element).apply(Set.In_Range.given.And), Eq[-1].this.find(Element).apply(Set.And.of.In_Range)

    Eq <<= Eq[-2].this.find(Element).apply(Set.In_Range.given.And), Eq[-1].this.find(Element).apply(Set.And.of.In_Range)




if __name__ == '__main__':
    run()
# created on 2022-01-08
