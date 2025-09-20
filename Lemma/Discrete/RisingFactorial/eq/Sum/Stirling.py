from util import *


@apply
def apply(self, var=None):
    x, n = self.of(RisingFactorial)
    if var is None:
        k = self.generate_var(integer=True)
    else:
        k = var
    return Equal(self, Sum[k:n + 1](x ** k * Stirling1(n, k)))


@prove
def prove(Eq):
    from Lemma import Discrete

    n = Symbol(integer=True, nonnegative=True)
    x = Symbol(real=True)
    Eq << apply(RisingFactorial(x, n))

    Eq << Eq[0].this.rhs.apply(Discrete.Sum.Stirling.eq.RisingFactorial)




if __name__ == '__main__':
    run()
# created on 2023-08-26
