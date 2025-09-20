from util import *


@apply
def apply(is_nonpositive, lt):
    x = is_nonpositive.of(Expr <= 0)
    y, S[x] = lt.of(Less)

    return Equal(Min(y ** 2, x ** 2), x ** 2)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True)
    Eq << apply(x <= 0, y < x)

    Eq << Algebra.Le.of.Lt.apply(Eq[1])

    Eq << Algebra.EqMin.of.Le_0.Le.apply(Eq[0], Eq[-1])








if __name__ == '__main__':
    run()
# created on 2019-12-09
