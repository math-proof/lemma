from util import *


@apply
def apply(given):
    x = given.of(NotElement[Integers])

    return Equal(floor(-frac(x)), -1)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x = Symbol(real=True)
    Eq << apply(NotElement(x, Integers))

    Eq << Set.Frac.In.Ioo.of.NotIn_Range.apply(Eq[0])

    Eq << Set.Neg.In.Icc.of.In_Icc.apply(Eq[-1])

    Eq << Set.Ge.Le.of.In_Icc.apply(Eq[-1])

    Eq <<= Algebra.LtFloor.of.Lt.apply(Eq[-1]), Algebra.GeFloor.of.Gt.apply(Eq[-2])

    Eq << Algebra.Le.of.Lt.strengthen.apply(Eq[-2])

    Eq <<= Eq[-2] & Eq[-1]


if __name__ == '__main__':
    run()
# created on 2018-05-20
