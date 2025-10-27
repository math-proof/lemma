from util import *


@apply
def apply(is_nonnegative, lt):
    x = is_nonnegative.of(Expr >= 0)
    S[x], M = lt.of(Less)

    return Equal(x, frac(x))


@prove
def prove(Eq):
    from Lemma import Algebra, Rat

    x = Symbol(real=True)
    Eq << apply(x >= 0, x < 1)

    Eq << Eq[-1].this.rhs.apply(Rat.Frac.eq.Sub_Floor).reversed

    Eq << Algebra.Floor.eq.Zero.of.Ge_0.Lt.apply(Eq[0], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-03-07
