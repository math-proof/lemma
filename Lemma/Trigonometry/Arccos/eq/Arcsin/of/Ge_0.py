from util import *


@apply
def apply(is_nonnegative):
    x = is_nonnegative.of(Expr >= 0)
    return Equal(acos(x), asin(sqrt(1 - x ** 2)))


@prove
def prove(Eq):
    from Lemma import Trigonometry, Algebra

    x = Symbol(real=True)
    Eq << apply(x >= 0)

    Eq << Eq[-1].this.lhs.apply(Trigonometry.Arccos.eq.Ite.Arcsin)

    Eq << Algebra.Cond.given.Cond.subst.Bool.apply(Eq[-1], cond=Eq[0])

    # https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()
# created on 2020-12-01
