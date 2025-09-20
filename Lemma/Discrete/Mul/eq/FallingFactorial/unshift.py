from util import *


@apply
def apply(self):
    x, (S[x - 1], k) = self.of(Expr * FallingFactorial)
    k += 1
    assert k > 0
    return Equal(self, FallingFactorial(x, k))


@prove
def prove(Eq):
    from Lemma import Discrete

    x = Symbol(complex=True)
    k = Symbol(integer=True, positive=True)
    Eq << apply(x * FallingFactorial(x - 1, k - 1))

    Eq << Eq[0].this.rhs.apply(Discrete.FallingFactorial.eq.Mul.shift)


if __name__ == '__main__':
    run()
# created on 2023-08-17
