from util import *


@apply
def apply(self):
    x, S[x] = self.of(Expr * Conjugate[Expr])
    assert x.is_super_complex
    return Equal(self, Abs(x) ** 2)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x = Symbol(complex=True)
    Eq << apply(x * ~x)

    Eq << Algebra.Expr.eq.AddRe_MulIIm.apply(x)

    Eq << Algebra.Expr.eq.AddRe_MulIIm.apply(~x)

    Eq << Eq[-1] * Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Add.eq.AddMulS, deep=True)

    Eq << Algebra.EqAbs.of.Eq.apply(Eq[1])

    Eq << Eq[-1] * Eq[-1]

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq[-3], Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-05-25
# updated on 2023-06-28
