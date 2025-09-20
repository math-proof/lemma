from util import *


@apply
def apply(is_nonpositive, greater_than):
    x = is_nonpositive.of(Expr <= 0)
    S[x], m = greater_than.of(GreaterEqual)

    return LessEqual(x * x, m * m)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, m = Symbol(real=True)
    Eq << apply(x <= 0, x >= m)

    Eq << Algebra.Le.of.Le.Ge.apply(Eq[0], Eq[1])

    Eq << -Eq[-1]

    Eq << Algebra.Le.of.Le.Ge.apply(Eq[0], Eq[-1])

    Eq << Algebra.Le_0.of.Ge.Le.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1] - Eq[-1].lhs.args[1]




if __name__ == '__main__':
    run()
# created on 2019-10-25
# updated on 2023-05-20
