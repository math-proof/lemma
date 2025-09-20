from util import *


@apply
def apply(is_nonpositive, le):
    x = is_nonpositive.of(Expr <= 0)
    y, S[x] = le.of(LessEqual)
    return GreaterEqual(y ** 2, x ** 2)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True)
    Eq << apply(x <= 0, y <= x)

    Eq << Eq[1] + x

    Eq << Eq[0] * 2

    Eq << Algebra.Le.of.Le.Le.apply(Eq[-2], Eq[-1])

    Eq << Algebra.Le_0.of.Le.apply(Eq[1])

    Eq << Algebra.Ge_0.of.Le_0.Le_0.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul_Add.eq.AddMulS, deep=True)

    Eq << Eq[-1].this.apply(Algebra.Ge.transport, lhs=1)




if __name__ == '__main__':
    run()
# created on 2019-09-03
# updated on 2023-05-20
