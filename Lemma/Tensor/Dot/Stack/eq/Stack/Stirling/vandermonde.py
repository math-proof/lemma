from util import *


@apply
def apply(self):
    (((j, i), (x, S[j])), (S[j], S[0], m), (S[i], S[0], d)), (((S[-x], S[j - i]), (S[j], S[i])), (S[j], S[0], S[d]), (S[i], S[0], S[m])) = self.of(Stack[Pow * Pow] @ Stack[Pow * Binomial])
    assert d <= m
    return Equal(self, Stack[j:d, i:d](x ** j * factorial(j) * Stirling(i, j)))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor

    m, d = Symbol(integer=True, positive=True)
    d = Symbol(domain=Range(m))
    i, j = Symbol(integer=True)
    x = Symbol(real=True)
    Eq << apply(Stack[j:m, i:d](j ** i * x ** j) @ Stack[j:d, i:m](Binomial(j, i) * (-x) ** (j - i)))

    Eq << Eq[-1].this.lhs.apply(Tensor.Dot.eq.Stack_Sum_MulGetS, simplify=None)

    Eq << Eq[-1].this.find((-Symbol) ** Add).apply(Algebra.Pow.eq.Mul.Neg, simplify=None)

    Eq << Eq[-1].this.lhs().find(Sum).simplify()

    Eq << Eq[-1].this.find(Sum).apply(Discrete.Sum.Binom.eq.Mul.Stirling)





if __name__ == '__main__':
    run()
# created on 2022-01-18
# updated on 2023-08-27
