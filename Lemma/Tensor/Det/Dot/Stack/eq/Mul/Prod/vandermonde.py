from util import *


@apply
def apply(self):
    (((j, i), (x, S[j])), (S[j], S[0], m), (S[i], S[0], d)), (((S[-x], S[j - i]), (S[j], S[i])), (S[j], S[0], S[d]), (S[i], S[0], S[m])) = self.of(Det[Stack[Pow * Pow] @ Stack[Pow * Binomial]])
    assert d <= m
    return Equal(self, x ** Binomial(d, 2) * Product[i:d](factorial(i)))


@prove
def prove(Eq):
    from Lemma import Discrete, Tensor

    m = Symbol(integer=True, positive=True)
    d = Symbol(domain=Range(m))
    i, j = Symbol(integer=True)
    x = Symbol(real=True)
    Eq << apply(Det(Stack[j:m, i:d](j ** i * x ** j) @ Stack[j:d, i:m](Binomial(j, i) * (-x) ** (j - i))))

    Eq << Eq[-1].this.find(MatMul).apply(Tensor.Dot.Stack.eq.Stack.Stirling.vandermonde)

    Eq << Eq[-1].this.lhs.doit(deep=True)

    Eq << Eq[-1].this.find(Binomial).apply(Discrete.Binom.eq.Mul.FallingFactorial.doit)

    Eq << Eq[-1].this.rhs.find(Mul).expand()





if __name__ == '__main__':
    run()
# created on 2022-01-15
# updated on 2023-03-21
