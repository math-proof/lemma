from util import *


@apply
def apply(self, upper=1):
    z, n = self.of(FallingFactorial)
    assert n.is_integer
    assert upper >= 0
    assert n >= 0
    i = self.generate_var(integer=True)
    return Equal(self, Stack[i:n + upper](FallingFactorial(z, i)) @ Stack[i:n + upper](KroneckerDelta(i, n)))


@prove
def prove(Eq):
    from Lemma import Discrete, Tensor

    h = Symbol(real=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)
    z = Symbol(real=True)
    Eq << apply(FallingFactorial(z, n))

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Sum)


if __name__ == '__main__':
    run()
# created on 2023-08-26
