from util import *


@apply
def apply(self):
    x, y, z = self.of(Binomial[Add, 3])
    assert x >= 0 and y >= 0 and z >= 0
    return Equal(self, binomial(x, 3) + binomial(y, 3) + binomial(z, 3) + binomial(x + y, 2) * z + binomial(y + z, 2) * x + binomial(x + z, 2) * y - 2 * x * y * z)


@prove
def prove(Eq):
    from Lemma import Discrete

    x, y, z = Symbol(integer=True, nonnegative=True)
    Eq << apply(Binomial(x + y + z, 3))

    Eq << Eq[-1].this.lhs.apply(Discrete.Binom.eq.Mul.FallingFactorial)

    Eq << Eq[-1].this.find(Binomial).apply(Discrete.Binom.eq.Mul.FallingFactorial)

    Eq << Eq[-1].this.find(Binomial).apply(Discrete.Binom.eq.Mul.FallingFactorial)

    Eq << Eq[-1].this.find(Binomial).apply(Discrete.Binom.eq.Mul.FallingFactorial)

    Eq << Eq[-1].this.find(Binomial).apply(Discrete.Binom.eq.Mul.FallingFactorial)

    Eq << Eq[-1].this.find(Binomial).apply(Discrete.Binom.eq.Mul.FallingFactorial)

    Eq << Eq[-1].this.find(Binomial).apply(Discrete.Binom.eq.Mul.FallingFactorial)

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1].this.rhs.expand()




if __name__ == '__main__':
    run()
# created on 2022-07-11
