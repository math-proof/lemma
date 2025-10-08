from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    lhs = lhs.of(Bool)
    rhs = rhs.of(Bool)
    return Iff(lhs, rhs)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    a, b = Symbol(integer=True)
    f = Function(shape=())

    Eq << apply(Equal(functions.Bool(a > b), functions.Bool(f(a) > f(b))))

    Eq << Eq[0] * Eq[0].lhs

    Eq << Algebra.SquareBool.eq.Bool.apply(Eq[-1].lhs)

    Eq << Eq[-2] - Eq[-1]

    Eq << Algebra.Eq.of.Sub.eq.Zero.apply(Eq[-1])

    Eq.suffice = Bool.Imp.of.Bool.eq.MulBoolS.apply(Eq[-1])

    Eq << Eq[0] * Eq[0].rhs

    Eq << Algebra.SquareBool.eq.Bool.apply(Eq[0].rhs ** 2)

    Eq << Eq[-2] + Eq[-1]

    Eq << Eq[-1].this.apply(Algebra.EqAddS.Is.Eq)

    Eq << Bool.Imp.of.Bool.eq.MulBoolS.apply(Eq[-1])

    Eq <<= Eq.suffice & Eq[-1]


if __name__ == '__main__':
    run()

# created on 2018-03-22
