from util import *


@apply
def apply(self, swap=None):
    (λ, h), (γ, S[h]) = self.of(Pow * Identity @ Pow)
    n, = h.shape
    if swap:
        λ, γ = γ, λ
    return Equal(self, (λ * γ) ** h)


@prove
def prove(Eq):
    from Lemma import Discrete, Tensor

    h = Symbol(real=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)
    λ, γ = Symbol(real=True)
    Eq << apply((λ ** h[:n]) * Identity(n) @ γ ** h[:n])

    Eq << Eq[-1].this.rhs.apply(Tensor.Pow.eq.Dot, swap=True)




if __name__ == '__main__':
    run()
# created on 2023-04-16
