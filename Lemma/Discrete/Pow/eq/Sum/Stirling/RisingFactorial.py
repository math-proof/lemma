from util import *


@apply
def apply(self, var=None):
    x, n = self.of(Pow)
    if var is None:
        k = self.generate_var(integer=True)
    else:
        k = var
    assert n >= 0 and n.is_integer
    return Equal(self, Sum[k:n + 1](RisingFactorial(x, k) * Stirling(n, k) * (-1) ** (n - k)))


@prove
def prove(Eq):
    from Lemma import Discrete

    x = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    Eq << apply(x ** n)

    Eq << Eq[-1].this.rhs.apply(Discrete.Sum_MulMul_RisingFactorial_Stirling.eq.Pow)


if __name__ == '__main__':
    run()
# created on 2023-08-26
