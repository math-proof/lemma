from util import *


@apply
def apply(self):
    k, (S[k], S[0], n) = self.of(Sum[Expr ** 2])
    return Equal(self, n * (2 * n - 1) * (n - 1) / 6)


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra

    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    n = Symbol(domain=Range(2, oo))
    Eq << apply(Sum[k:n](k ** 2))

    Eq << Binomial(k, 2).this.apply(Discrete.Binom.eq.Mul.FallingFactorial.doit)

    Eq << Eq[-1] * 2

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].reversed + k

    Eq << Algebra.EqSumS.of.Eq.apply(Eq[-1], (k, 0, n), simplify=None)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.eq.Mul.series.arithmetic)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.eq.Add.shift)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.eq.Add.shift)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.limits.subst.offset, 2)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Discrete.Sum.Binom.eq.Binom)

    Eq << Eq[-1].this.find(Binomial).apply(Discrete.Binom.eq.Mul.FallingFactorial.doit)

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Mul)

    Eq << Eq[0].this.rhs.args[::3].simplify()




if __name__ == '__main__':
    run()
# created on 2023-12-13
