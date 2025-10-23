from util import *


@apply
def apply(self):
    (xi, xj), (j, S[0], i), (S[i], S[0], n) = self.of(Sum[Pow[Expr - Expr, 2]])
    if not xi._has(i):
        xi, xj = xj, xi
    assert xj._subs(j, i) == xi
    return Equal(self, n * Sum[i:n](xi ** 2) - Sum[i:n](xi) ** 2)


@prove
def prove(Eq):
    from Lemma import Algebra, Finset, Finset, Finset

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(oo,))
    Eq << apply(Sum[j:i, i:n]((x[i] - x[j]) ** 2))

    Eq << Eq[0].this.lhs.expr.apply(Algebra.SquareAdd.eq.AddAddSquareS_MulMul2)

    Eq << Eq[-1].this.lhs.apply(Finset.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].this.lhs.args[1].apply(Algebra.Sum.limits.swap.intlimit)

    Eq << Eq[-1].this.lhs.args[1].apply(Algebra.Sum.limits.separate)

    Eq << Eq[-1].this.lhs.args[1].limits_subs(j, i)

    Eq << Eq[-1].this.lhs.args[1].expr.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << -Eq[-1].this.lhs.args[1].apply(Finset.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].this.find(2 * ~Sum).apply(Algebra.Sum_Mul.eq.Sub_DivSumSquare)





if __name__ == '__main__':
    run()
# created on 2019-11-12
# updated on 2023-06-24
