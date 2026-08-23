from util import *


@apply
def apply(self):
    ((n, k), (S[k], S[4]), (x, S[k])), (S[k], a, S[n + 1]) = self.of(Sum[Binomial * Pow * Pow])
    assert a in (0, 1)
    return Equal(self, RisingFactorial(n * x, 4) * (x + 1) ** (n - 4) - n * x * ((4 * n - 1) * x + 5) * (x + 1) ** (n - 3))


@prove
def prove(Eq):
    from Lemma import Algebra, Finset, Int, Nat, Real

    x, k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(Sum[k:n + 1](Binomial(n, k) * x ** k * k ** 4))

    Eq << Eq[0].this.lhs.apply(Algebra.Sum.eq.Add.shift)

    Eq << Eq[-1].this.lhs().find(Binomial).apply(Finset.Binom.eq.Div.Binom)

    Eq << Eq[-1].this.find(Sum).apply(Finset.SumIco.eq.Sum_UFnAdd, 1)

    Eq << Eq[-1].this.lhs.find(Pow).apply(Real.Pow_Add.eq.MulPowS.of.Gt_0)

    Eq << Eq[-1].this.find(Add ** 3).apply(Finset.PowAdd.eq.Sum_MulMulPowS)

    Eq << Eq[-1].this.find(Sum).expr.apply(Nat.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Sum).apply(Finset.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].this.lhs.apply(Nat.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Sum[Mul[Symbol]]).apply(Algebra.Sum.eq.Sub.unshift)

    Eq << Eq[-1].this.find(Sum[Mul[Symbol]]).apply(Finset.Sum.Binom.eq.Mul.Newton)

    Eq << Eq[-1].this.find(Sum).apply(Finset.Sum.Binom.eq.Pow.Newton)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.eq.Sub.unshift)

    Eq << Eq[-1].this.lhs.apply(Int.AddAddS.eq.MulAddS, factor=x)

    Eq << Eq[-1].this.find(Add).apply(Int.AddAddS.eq.MulAddS, factor=n)

    Eq << Eq[-1].this.lhs.find(Add).apply(Int.AddAddS.eq.MulAddS, factor=n)

    Eq << Eq[-1].this.find(Add[Pow]).apply(Int.AddAddS.eq.MulAddS, factor=(x + 1) ** (n - 2))

    Eq << Eq[-1].this.find(Sum).apply(Finset.Sum.Binom.eq.Mul.Newton.trois)

    Eq << Eq[-1].this.find(Sum).apply(Finset.Sum.Binom.eq.Mul.Newton.deux)

    Eq << Eq[-1].this.find(Mul + Mul).apply(Int.AddAddS.eq.MulAddS, factor=(x + 1) ** (n - 4))

    Eq << Eq[-1].this.find(1 + ~Mul).expand()

    Eq << Eq[-1].this.find(1 + ~Mul[Add]).expand()

    Eq << Eq[-1].this.lhs.find(Add).apply(Int.AddAddS.eq.MulAddS, factor=x * (x + 1) ** (n - 4))

    Eq << Eq[-1].this.rhs.find(Add[Mul]).expand()

    Eq << Int.Eq.given.Sub.eq.Zero.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Int.AddAddS.eq.MulAddS, factor=(x + 1) ** (n - 4))

    Eq << Eq[-1].this.lhs.args[1].expand()





if __name__ == '__main__':
    run()
# created on 2021-11-26
# updated on 2023-04-12
