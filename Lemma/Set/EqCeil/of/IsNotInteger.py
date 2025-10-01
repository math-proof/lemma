from util import *


@apply
def apply(given):
    x = given.of(NotElement[Integers])
    return Equal(ceil(x), floor(x) + 1)


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    x = Symbol(real=True)
    Eq << apply(NotElement(x, Integers))

    Eq << Algebra.GeCeil.apply(x)

    Eq << Set.GtFrac_0.of.NotIn_Range.apply(Eq[0])

    Eq << Eq[-1].this.lhs.apply(Algebra.Frac.eq.Sub_Floor)

    Eq << Algebra.Gt.of.Sub.gt.Zero.apply(Eq[-1])

    Eq.lt_floor = Eq[-1].reversed

    Eq << Algebra.Gt.of.Ge.Gt.apply(Eq[2], Eq[-1])

    Eq << Algebra.Ge.of.Gt.strengthen.apply(Eq[-1])

    Eq.gt_floor = Algebra.Floor.gt.Sub_1.apply(x)

    Eq << Eq.gt_floor + 1

    Eq << Algebra.Gt.of.Ge.Gt.apply(Eq[-2], Eq[-1])

    Eq << Algebra.Ceil.lt.Add_1.apply(x)

    Eq << Set.In.Icc.of.Gt.Lt.apply(Eq[-1], Eq[-2])

    Eq << Set.In.Icc.of.Gt.Lt.apply(Eq.gt_floor, Eq.lt_floor)

    Eq << Set.Sub.In.Ioc.of.In.In.apply(Eq[-2], Eq[-1])

    Eq << Set.Ge.Le.of.In_Icc.apply(Eq[-1])

    Eq <<= Algebra.Ge.of.Gt.strengthen.apply(Eq[-2]), Algebra.Le.of.Lt.strengthen.apply(Eq[-1])

    Eq << Algebra.Eq.of.Ge.Le.apply(Eq[-1], Eq[-2])
    Eq << Eq[-1].this.apply(Algebra.Eq.transport)


if __name__ == '__main__':
    run()
# created on 2018-05-17
