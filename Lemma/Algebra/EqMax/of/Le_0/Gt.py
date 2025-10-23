from util import *


@apply
def apply(is_nonpositive, lt):
    x = is_nonpositive.of(Expr <= 0)
    S[x], y = lt.of(Greater)

    return Equal(Max(y ** 2, x ** 2), y ** 2)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    x, y = Symbol(real=True)
    Eq << apply(x <= 0, x > y)

    Eq << Eq[-1] - y ** 2

    Eq << Eq[-1].this.lhs.apply(Algebra.Add.eq.Max)

    Eq << Algebra.LtSquare.of.Le_0.Gt.apply(Eq[0], Eq[1])

    Eq << Algebra.Lt_0.of.Lt.apply(Eq[-1])

    Eq << Nat.EqMax.of.Lt.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-09-05
