from util import *


@apply
def apply(self):
    hi, (i, a, b) = self.of(Sum)
    first = hi._subs(i, a)
    last = hi._subs(i, b - 1)

    return Equal(self, (first + last) * (b - a) / 2)


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Finset, Int

    k, h = Symbol(complex=True)
    a, b, i = Symbol(integer=True)
    Eq << apply(Sum[i:a:b](k * i + h))

    Eq << Eq[-1].this.lhs.apply(Finset.Sum_Add.eq.AddSumS)

    Eq.eq = Eq[-1].this.rhs.apply(Algebra.Mul_Add.eq.AddMulS, 2)

    Eq << Discrete.Binom.eq.Add.Pascal.apply(Binomial(i + 1, 2))

    Eq << Eq[-1].this.apply(Int.EqAdd.Is.Eq_Sub, rhs=1)

    Eq << Algebra.EqSumS.of.Eq.apply(Eq[-1], (i, a, b)).reversed

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Sub.telescope)

    Eq << Eq[-1].this.find(Binomial).apply(Discrete.Binom.eq.Mul.FallingFactorial.doit)

    Eq << Eq[-1].this.find(Binomial).apply(Discrete.Binom.eq.Mul.FallingFactorial.doit)

    Eq << Eq.eq.subs(Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1].this.rhs.expand()


if __name__ == '__main__':
    run()
# created on 2022-01-15
