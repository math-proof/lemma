from util import *


@apply
def apply(is_nonpositive, lt):
    x = is_nonpositive.of(Expr <= 0)
    y, S[x] = lt.of(Less)
    return Greater(y ** 2, x ** 2)


@prove
def prove(Eq):
    from Lemma import Algebra, Int

    x, a, y = Symbol(real=True)
    Eq << apply(x <= 0, y < x)

    Eq << Eq[1] + x

    Eq << Eq[0] * 2

    Eq << Algebra.Lt.of.Lt.Le.apply(Eq[-2], Eq[-1])

    Eq << Algebra.Lt_0.of.Lt.apply(Eq[1])

    Eq << Int.Gt_0.of.Lt_0.Lt_0.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul_Add.eq.AddMulS, deep=True)

    Eq << Eq[-1].this.apply(Algebra.Gt.transport, lhs=1)




if __name__ == '__main__':
    run()
# created on 2019-12-09
# updated on 2023-05-20
