from util import *


@apply
def apply(self, simplify=True):
    from Lemma.Set.OrInS.of.In_Union import split
    return split(self, simplify=simplify)


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    e = Symbol(integer=True, given=True)
    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Element(e, A | B))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Set.OrInS.of.In_Union)
    Eq << Eq[-1].this.rhs.apply(Set.In_Union.given.OrInS)




if __name__ == '__main__':
    run()
# created on 2023-04-18
