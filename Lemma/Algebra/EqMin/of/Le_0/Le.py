from util import *


@apply
def apply(is_nonpositive, le):
    x = is_nonpositive.of(Expr <= 0)
    y, S[x] = le.of(LessEqual)

    return Equal(Min(y ** 2, x ** 2), x ** 2)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True)
    Eq << apply(x <= 0, y <= x)

    Eq << Eq[-1] - x ** 2

    Eq << Eq[-1].this.lhs.apply(Algebra.Add.eq.Min)

    Eq << Algebra.LeSquare.of.Le_0.Le.apply(Eq[0], Eq[1])

    Eq << Algebra.Ge_0.of.Le.apply(Eq[-1])

    Eq << Algebra.EqMin.of.Ge.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-12-07
