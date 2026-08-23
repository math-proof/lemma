from util import *


@apply
def apply(le, le_neg):
    x, y = le.of(LessEqual)
    S[-x], S[y] = le_neg.of(LessEqual)
    return abs(x) <= y


@prove
def prove(Eq):
    from Lemma import Nat, Int, Real

    x, y = Symbol(real=True)
    Eq << apply(x <= y, -x <= y)

    Eq << Eq[0] - y

    Eq << Eq[1] - y

    Eq << Int.Ge_0.of.Le_0.Le_0.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.expand() + x * x

    Eq << Eq[-1].reversed

    Eq.lt = Real.LeSqrt.of.Le.apply(Eq[-1])

    Eq << Nat.Ge.of.Le.Ge.apply(Eq[0], -Eq[1])

    Eq << (Eq[-1] + y) / 2

    Eq << Int.EqAbs.of.Ge_0.apply(Eq[-1])

    Eq << Eq.lt.subs(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2022-01-07
