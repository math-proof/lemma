from util import *


@apply
def apply(self):
    x, i = self.of(RisingFactorial)
    return Equal(self, (-1) ** i * FallingFactorial(-x, i))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra

    x = Symbol(real=True)
    n = Symbol(integer=True, nonnegative=True)
    Eq << apply(RisingFactorial(x, n))

    Eq << Eq[0].this.lhs.apply(Discrete.RisingFactorial.eq.Prod)

    Eq << Eq[-1].this.find(FallingFactorial).apply(Discrete.FallingFactorial.eq.Prod)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.eq.Prod.distribute)




if __name__ == '__main__':
    run()
# created on 2023-08-20
