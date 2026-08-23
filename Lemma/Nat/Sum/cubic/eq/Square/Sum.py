from util import *


@apply
def apply(self):
    k, (S[k], S[0], n) = self.of(Sum[Expr ** 3])
    return Equal(self, Sum[k:n](k) ** 2)


@prove
def prove(Eq):
    from Lemma import Finset, Nat, Fin, Rat

    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    n = Symbol(domain=Range(3, oo))
    Eq << apply(Sum[k:n](k ** 3))

    Eq << Finset.Pow.eq.Sum.Stirling.FallingFactorial.apply(k ** 3)

    Eq << Eq[-1].this.rhs.apply(Finset.Sum.eq.Add.doit)

    Eq << Binomial(k, 3).this.apply(Finset.Binom.eq.Mul.FallingFactorial.doit).reversed * 6

    Eq << Binomial(k, 2).this.apply(Finset.Binom.eq.Mul.FallingFactorial.doit).reversed * 2

    Eq << Eq[-3].subs(*Eq[-2:])

    Eq << Fin.Sum.of.All_Eq.apply(Eq[-1], (k, 0, n), simplify=None)

    Eq << Eq[-1].this.rhs.apply(Finset.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Rat.Sum.eq.Mul.series.arithmetic)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Finset.Sum.eq.Add.shift)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Finset.Sum.eq.Add.shift)

    Eq << Eq[-1].this.rhs.find(Mul[~Sum][2]).apply(Finset.Sum.eq.Add.shift)

    Eq << Eq[-1].this.rhs.find(Mul[~Sum][2]).apply(Finset.Sum.eq.Add.shift)

    Eq << Eq[-1].this.rhs.find(Mul[~Sum][2]).apply(Finset.Sum.eq.Add.shift)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Finset.SumIco.eq.Sum_UFnAdd, 2)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Finset.SumIco.eq.Sum_UFnAdd, 3)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Finset.Sum.Binom.eq.Binom)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Finset.Sum.Binom.eq.Binom)

    Eq << Eq[-1].this.find(Binomial).apply(Finset.Binom.eq.Mul.FallingFactorial.doit)

    Eq << Eq[-1].this.find(Binomial).apply(Finset.Binom.eq.Mul.FallingFactorial.doit)

    Eq << Eq[-1].this.rhs.apply(Nat.AddMulS.eq.Mul_Add)

    Eq << Eq[-1].this.find(Add[Mul]).expand()

    Eq << Eq[-1].this.find(Add[Mul]).apply(Nat.AddMulS.eq.Mul_Add)

    Eq << Eq[0].this.rhs.find(Sum).apply(Rat.Sum.eq.Mul.series.arithmetic)


if __name__ == '__main__':
    run()
# created on 2023-12-13
