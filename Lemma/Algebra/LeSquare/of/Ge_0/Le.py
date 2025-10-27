from util import *


@apply
def apply(is_nonnegative, le):
    x = is_nonnegative.of(Expr >= 0)
    S[x], M = le.of(LessEqual)

    return LessEqual(x * x, M * M)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    x, M = Symbol(real=True)
    Eq << apply(x >= 0, x <= M)

    Eq << Nat.Ge.of.Ge.Ge.apply(Eq[0], Eq[1])

    Eq << -Eq[-1]

    Eq << Nat.Ge.of.Ge.Ge.apply(Eq[0], Eq[-1])

    Eq << Algebra.Le_0.of.Ge.Le.apply(Eq[-1], Eq[1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1] - Eq[-1].lhs.args[1]





if __name__ == '__main__':
    run()
# created on 2019-06-17
# updated on 2025-04-10
