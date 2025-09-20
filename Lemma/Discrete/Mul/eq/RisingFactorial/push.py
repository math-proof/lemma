from util import *


@apply
def apply(self):
    (x, k), S[x + k] = self.of(RisingFactorial * Expr)
    k += 1
    assert k > 0
    return Equal(self, RisingFactorial(x, k))


@prove
def prove(Eq):
    from Lemma import Discrete

    x = Symbol(complex=True)
    k = Symbol(integer=True, positive=True)
    Eq << apply((x + k - 1) * RisingFactorial(x, k - 1))

    Eq << Eq[0].this.rhs.apply(Discrete.RisingFactorial.eq.Mul.pop)


if __name__ == '__main__':
    run()
# created on 2023-08-17
