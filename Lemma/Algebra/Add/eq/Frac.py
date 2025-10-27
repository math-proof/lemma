from util import *


@apply
def apply(sub):
    y, x = sub.of(Expr - Expr)

    if y == ceil(x):
        return Equal(sub, frac(-x))
    if x == floor(y):
        return Equal(sub, frac(y))


@prove
def prove(Eq):
    from Lemma import Algebra, Rat
    x = Symbol(real=True)
    Eq << apply(ceil(x) - x)

    Eq << Eq[-1].this.rhs.apply(Rat.Frac.eq.Sub_Floor)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ceil.eq.Neg.Floor)


if __name__ == '__main__':
    run()
# created on 2018-05-21
