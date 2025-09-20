from util import *


@apply
def apply(given, wrt=None):
    A, B = given.of(Equal[Intersection, EmptySet])

    if wrt is None:
        wrt = given.generate_var(**given.lhs.etype.dict)

    return Equal(Bool(Element(wrt, A | B)), Bool(Element(wrt, A)) + Bool(Element(wrt, B)))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic
    A, B = Symbol(etype=dtype.integer)

    Eq << apply(Equal(A & B, A.etype.emptySet))

    Eq <<= Eq[-1].rhs.args[0].this.apply(Logic.Bool.eq.Ite), Eq[-1].rhs.args[1].this.apply(Logic.Bool.eq.Ite)

    Eq << Eq[-1] + Eq[-2]

    Eq << Set.Eq_Ite.of.Eq_Empty.apply(Eq[0], *Eq[-1].rhs.args)

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq[-1], Eq[-2])

    Eq << Eq[1].this.lhs.apply(Logic.Bool.eq.Ite)


if __name__ == '__main__':
    run()

# created on 2020-07-04
