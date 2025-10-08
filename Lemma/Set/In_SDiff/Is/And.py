from util import *


@apply
def apply(given):
    e, domain = given.of(Element)
    A, B = domain.of(Complement)

    return And(Element(e, A), NotElement(e, B))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool

    e = Symbol(integer=True, given=True)
    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Element(e, A - B))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Set.In.NotIn.of.In_SDiff)

    Eq << Eq[-1].this.rhs.apply(Set.In_SDiff.given.And, simplify=None)




if __name__ == '__main__':
    run()
# created on 2023-04-24
