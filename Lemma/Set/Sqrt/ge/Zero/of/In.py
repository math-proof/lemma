from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    assert R in Interval(-1, 1)
    return sqrt(1 - x ** 2) >= 0


@prove
def prove(Eq):
    from Lemma import Set, Nat, Int, Real

    x = Symbol(real=True, given=True)
    Eq << apply(Element(x, Interval(-1, 1)))

    Eq << Set.Le.Le.of.In_Icc.apply(Eq[0])

    Eq <<= Eq[-2] + 1, Eq[-1] - 1

    Eq << -Eq[-2]

    Eq << Int.Ge_0.of.Le_0.Le_0.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.apply(Nat.Mul_Add.eq.AddMulS, deep=True)

    Eq << Real.GeSqrt_0.of.Ge_0.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-03-14
