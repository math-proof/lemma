from util import *


@apply
def apply(self):
    k, (S[k], S[0], n) = self.of(Sum[Expr ** 3])
    return Equal(self, Sum[k:n](k) ** 2)


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra

    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    n = Symbol(domain=Range(3, oo))
    Eq << apply(Sum[k:n](k ** 3))

    Eq << Discrete.Pow.eq.Sum.Stirling.FallingFactorial.apply(k ** 3)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Add.doit)

    Eq << Binomial(k, 3).this.apply(Discrete.Binom.eq.Mul.FallingFactorial.doit).reversed * 6

    Eq << Binomial(k, 2).this.apply(Discrete.Binom.eq.Mul.FallingFactorial.doit).reversed * 2

    Eq << Eq[-3].subs(*Eq[-2:])

    Eq << Algebra.EqSumS.of.Eq.apply(Eq[-1], (k, 0, n), simplify=None)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.eq.Mul.series.arithmetic)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.eq.Add.shift)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.eq.Add.shift)

    Eq << Eq[-1].this.rhs.find(Mul[~Sum][2]).apply(Algebra.Sum.eq.Add.shift)

    Eq << Eq[-1].this.rhs.find(Mul[~Sum][2]).apply(Algebra.Sum.eq.Add.shift)

    Eq << Eq[-1].this.rhs.find(Mul[~Sum][2]).apply(Algebra.Sum.eq.Add.shift)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.limits.subst.offset, 2)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.limits.subst.offset, 3)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Discrete.Sum.Binom.eq.Binom)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Discrete.Sum.Binom.eq.Binom)

    Eq << Eq[-1].this.find(Binomial).apply(Discrete.Binom.eq.Mul.FallingFactorial.doit)

    Eq << Eq[-1].this.find(Binomial).apply(Discrete.Binom.eq.Mul.FallingFactorial.doit)

    Eq << Eq[-1].this.rhs.apply(Algebra.AddMulS.eq.Mul_Add)

    Eq << Eq[-1].this.find(Add[Mul]).expand()

    Eq << Eq[-1].this.find(Add[Mul]).apply(Algebra.AddMulS.eq.Mul_Add)

    Eq << Eq[0].this.rhs.find(Sum).apply(Algebra.Sum.eq.Mul.series.arithmetic)


if __name__ == '__main__':
    run()
# created on 2023-12-13
