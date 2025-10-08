from util import *


@apply
def apply(contains1, contains2):
    e, A = contains1.of(Element)
    S[e], B = contains2.of(Element)

    return Element(e, A & B)


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool

    e = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Element(e, A), Element(e, B))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Set.In_Inter.of.In.In)
    Eq << Eq[-1].this.rhs.apply(Set.In.In.given.In.Inter)


if __name__ == '__main__':
    run()
# created on 2023-08-26
