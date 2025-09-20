from util import *


@apply
def apply(self):
    x, i = self.of(FallingFactorial)
    return Equal(self, (-1) ** i * RisingFactorial(-x, i))


@prove
def prove(Eq):
    from Lemma import Discrete

    x = Symbol(real=True)
    n = Symbol(integer=True, nonnegative=True)
    Eq << apply(FallingFactorial(x, n))

    Eq << Eq[0].this.find(RisingFactorial).apply(Discrete.RisingFactorial.eq.Mul.FallingFactorial)








if __name__ == '__main__':
    run()
# created on 2023-08-20
