from util import *


@apply
def apply(is_nonnegative, strict_greater_than):
    x = is_nonnegative.of(Expr >= 0)
    y, S[x] = strict_greater_than.of(Greater)
    return Greater(y ** 2, x ** 2)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    x, a, y = Symbol(real=True)
    Eq << apply(x >= 0, y > x)

    Eq << Eq[1] + x

    Eq << Eq[0] * 2

    Eq << Nat.Gt.of.Gt.Ge.apply(Eq[-1], Eq[-2])

    Eq << Algebra.Gt_0.of.Gt.apply(Eq[1])

    Eq << Nat.Gt_0.of.Gt_0.Gt_0.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul_Add.eq.AddMulS, deep=True)

    Eq << Eq[-1].this.apply(Algebra.Gt.transport, lhs=1)




if __name__ == '__main__':
    run()
# created on 2019-06-14
# updated on 2023-05-20
