from util import *


@apply
def apply(given):
    x, complement = given.of(Element)

    B, A = complement.of(Complement)
    return And(Element(x, B), NotElement(x, A))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    x = Symbol(real=True)
    A, B = Symbol(etype=dtype.real)
    Eq << apply(Element(x, B - A))

    Eq.suffice, Eq.necessary = Logic.Iff.given.Imp.Imp.apply(Eq[-1])

    Eq << Logic.Imp_And.given.Imp.Imp.apply(Eq.suffice)

    Eq << Eq[-2].this.lhs.apply(Set.In.of.In_SDiff)

    Eq << Eq[-1].this.lhs.apply(Set.NotIn.of.In_SDiff)

    Eq << Eq.necessary.this.lhs.simplify()


if __name__ == '__main__':
    run()

# created on 2021-01-25
