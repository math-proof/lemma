from util import *


@apply
def apply(is_nonnegative, le):
    x = is_nonnegative.of(Expr >= 0)
    S[x], y = le.of(LessEqual)

    return Equal(Min(y ** 2, x ** 2), x ** 2)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    x, y = Symbol(real=True)
    Eq << apply(x >= 0, x <= y)

    Eq << Eq[-1] - x ** 2

    Eq << Eq[-1].this.lhs.apply(Algebra.Add.eq.Min)

    Eq << Algebra.LeSquare.of.Ge_0.Le.apply(Eq[0], Eq[1])

    Eq << Algebra.Ge_0.of.Le.apply(Eq[-1])

    Eq << Nat.EqMin.of.Ge.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-06-20
