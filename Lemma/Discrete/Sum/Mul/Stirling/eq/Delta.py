from util import *


@apply
def apply(self):
    (a, exp), (k, start, n) = self.of(Sum[Expr * (-1) ** Expr])
    n -= 1
    ik, kn = a.of(Stirling * Stirling1)
    i, = {*ik} - {k}
    n_, = {*kn} - {k}
    i, = {i, n_} - {n}
    assert start in (0, i)
    assert exp in (k - i, k + i, n - k, n + k)
    return Equal(self, KroneckerDelta(n, i))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor

    k = Symbol(integer=True)
    i = Symbol(integer=True, nonnegative=True)
    n = Symbol(domain=Range(i, oo))
    Eq << apply(Sum[k:i:n + 1]((-1) ** (k - i) * Stirling1(n, k) * Stirling(k, i)))

    x = Symbol(complex=True)
    Eq << Discrete.FallingFactorial.eq.Sum.Stirling.apply(FallingFactorial(x, n), k)

    Eq << Eq[-1].this.rhs().find(Symbol ** Symbol).apply(Discrete.Pow.eq.Sum.Stirling.FallingFactorial)

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.Mul_Sum.eq.Sum_Mul)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.swap.intlimit)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.separate)

    Eq << Eq[-1].this.rhs.apply(Tensor.Sum.eq.Dot)

    Eq << Eq[-1].this.lhs.apply(Tensor.FallingFactorial.eq.Dot.Delta)

    Eq << Tensor.Eq.of.EqDotSStackFallingFactorial.vector_independence.apply(Eq[-1])

    Eq << Algebra.Cond.of.All.subst.apply(Eq[-1], Eq[-1].variable, i)

    Eq << Eq[-1] * (-1) ** (n - i)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Sum.eq.Sum_Mul)

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul.Delta.subst)

    Eq << Eq[-1].reversed





if __name__ == '__main__':
    run()
# created on 2023-08-20
# updated on 2023-08-27
