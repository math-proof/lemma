from util import *


@apply
def apply(le_zero):
    x = le_zero.of(Expr <= 0)
    return sin(x) >= x * (1 - x / S.Pi)

@prove
def prove(Eq):
    from Lemma import Trigonometry, Algebra, Logic

    x = Symbol(real=True)
    Eq << apply(x <= 0)

    Eq << (x >= 0).this.apply(Trigonometry.LeSin.of.Ge_0.quadratic)

    Eq << Eq[-1].subs(x, -x)

    Eq << -Eq[-1].this.lhs

    Eq << -Eq[-1].this.rhs

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-10-03
