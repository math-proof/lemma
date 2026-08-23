from util import *


@apply
def apply(self):
    S[S.Half], n = self.of(Binomial)
    assert n.is_integer
    assert n >= 0
    return Equal(self, -(-S.One / 4) ** n * Binomial(2 * n, n) / (2 * n - 1))


@prove
def prove(Eq):
    from Lemma import Finset, Real

    n = Symbol(integer=True, nonnegative=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(Binomial(S.One / 2, n))

    Eq << Eq[0].lhs.this.apply(Finset.Binom.eq.Mul.FallingFactorial)

    Eq << Eq[-1].this.find(FallingFactorial).apply(Finset.FallingFactorial.eq.Prod)

    Eq << Eq[-1].this.find(Product).apply(Finset.Prod.eq.Mul.Neg)

    Eq << Eq[-1].this.find(Product).apply(Finset.Prod.eq.Mul.scale, 2)

    Eq << Eq[-1].this.find(Mul).args[:2].apply(Real.MulPowS.eq.PowMul)

    Eq << Eq[-1].this.find(Product).apply(Finset.Prod.eq.Mul.push)

    Eq << Eq[-1].this.find(Product).apply(Finset.Prod.eq.Mul.shift)

    Eq << Eq[0].this.rhs.find(Binomial).apply(Finset.Binom.eq.Div.Factorial2)

    Eq << Eq[-1].this.find(Factorial2).apply(Finset.Factorial2.eq.Prod.odd)





if __name__ == '__main__':
    run()

# created on 2020-10-21
# updated on 2023-06-03
