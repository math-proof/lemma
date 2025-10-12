from util import *


@apply
def apply(is_nonnegative, lt):
    x = is_nonnegative.of(Expr >= 0)
    S[x], y = lt.of(Less)

    return Equal(Min(y ** 2, x ** 2), x ** 2)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    x, y = Symbol(real=True)
    Eq << apply(x >= 0, x < y)

    Eq << Nat.Le.of.Lt.apply(Eq[1])

    Eq << Algebra.EqMin.of.Ge_0.Le.apply(Eq[0], Eq[-1])












if __name__ == '__main__':
    run()
# created on 2019-07-02
