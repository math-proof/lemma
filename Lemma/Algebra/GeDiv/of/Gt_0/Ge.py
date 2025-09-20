from util import *


@apply
def apply(is_positive_x, ge):
    x = is_positive_x.of(Expr > 0)
    lhs, rhs = ge.of(GreaterEqual)
    return GreaterEqual(lhs / x, rhs / x)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, a, b = Symbol(real=True)
    Eq << apply(x > 0, a >= b)

    Eq << Algebra.Div.gt.Zero.of.Gt_0.apply(Eq[0])

    Eq << Algebra.GeMul.of.Gt_0.Ge.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2018-07-20
