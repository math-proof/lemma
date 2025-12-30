from util import *


@apply
def apply(n, d):
    assert d > 0
    return Element(n - d * Floor(n / d), Interval(0, d, right_open=True))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Rat

    n = Symbol(real=True)
    d = Symbol(real=True, positive=True)
    Eq << apply(n, d)

    Eq << Set.In_Ico.given.Le.Lt.apply(Eq[0])

    Eq << Rat.LeFloor.apply(Eq[0].find(Floor).arg)

    Eq << Algebra.LeMul.of.Le.apply(Eq[-1], d)

    Eq << -Eq[-1] + n

    Eq << Algebra.Lt_Add_.Floor.One.apply(Eq[0].find(Floor).arg) - 1

    Eq << Eq[-1] * d

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << -Eq[-1] + n

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2018-06-18
