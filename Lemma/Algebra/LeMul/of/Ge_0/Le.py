from util import *


@apply
def apply(is_nonnegative, ge):
    if 0 not in is_nonnegative.args:
        ge, is_nonnegative = given

    x = is_nonnegative.of(Expr >= 0)
    a, b = ge.of(LessEqual)

    return LessEqual(a * x, b * x)


@prove
def prove(Eq):
    from Lemma import Algebra, Int

    x, a, b = Symbol(real=True)
    Eq << apply(x >= 0, a <= b)

    Eq << Eq[1] - b

    Eq << Int.Le_0.of.Ge_0.Le_0.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Algebra.Le.of.Le_0.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-06-21
