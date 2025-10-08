from util import *


@apply
def apply(given):
    factor, cond = given.of(GreaterEqual[Mul[Bool], 1])
    return factor >= 1, cond


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, y = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(GreaterEqual((f(x) >= 0).toNat * y, 1))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.And.of.GeMul)

    Eq << Eq[-1].this.rhs.apply(Algebra.GeMul.given.And)


if __name__ == '__main__':
    run()
# created on 2023-11-05
