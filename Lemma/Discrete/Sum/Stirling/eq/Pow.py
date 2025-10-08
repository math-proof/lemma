from util import *


@apply
def apply(self):
    ((x, k), (n, S[k])), (k, S[0], S[n + 1]) = self.of(Sum[FallingFactorial * Stirling])
    return Equal(self, x ** n)


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Bool

    k = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True, given=False)
    x = Symbol(real=True)
    Eq << apply(Sum[k:n + 1](FallingFactorial(x, k) * Stirling(n, k)))

    # try to prove it by inspecting the recurrence relations of the coefficients! We can induct on n:

    Eq << Eq[0].subs(n, n + 1)

    Eq << Eq[1].this.find(Stirling).apply(Discrete.Stirling.eq.Add.recurrence)

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.limits.subst.offset, 1)

    Eq << Eq[0] * x

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.eq.Pow.Add.exponent)

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul_Sum.eq.Sum_Mul)

    Eq << Eq[-1].this.lhs().expr.args[:2].apply(Discrete.Mul.FallingFactorial.eq.Add)

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum_Add.eq.AddSumS)

    Eq << Imply(Eq[0], Eq[1], plausible=True)

    Eq << Bool.Eq_Ite.of.All_Imp.apply(Eq[-1], n, 0)




if __name__ == '__main__':
    run()
# created on 2023-08-26
