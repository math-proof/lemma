from util import *


@apply
def apply(self):
    ((delta, i), (j, S[0], m), (S[i], S[0], (S[m], d))), (((λ, (S[d], S[j], S[-i])), (S[d], S[i - j])), (S[j], S[0], S[m - d]), (S[i], S[0], S[m])) = \
    self.of(Det[Stack[Pow, Tuple[Expr - Expr]] @ Stack[(-Expr) ** Add * Binomial]])
    delta -= j
    assert not delta._has(j)
    return Equal(self, (1 - λ) ** (d * (m - d)) * Product[i:m - d](factorial(i)))


@prove
def prove(Eq):
    from Lemma import Discrete, Tensor

    m = Symbol(integer=True, positive=True)
    d = Symbol(integer=True, nonnegative=True)
    i, j = Symbol(integer=True)
    λ, delta = Symbol(real=True)
    Eq << apply(Det(Stack[j:m, i:m - d]((j + delta) ** i) @ Stack[j:m - d, i:m](binomial(d, i - j) * (-λ) ** (d + j - i))))

    Eq << Eq[-1].this.find(MatMul).apply(Tensor.DotStackS.eq.DotStackS.vandermonde.col_transform)

    Eq << Eq[-1].this.lhs.apply(Discrete.Det.eq.Mul, doit=True, deep=False)

    Eq << Eq[-1].this.find(Sum).apply(Discrete.Sum.Binom.eq.Pow.Newton)

    Eq << Eq[-1].this.find(Det).apply(Discrete.DetStackPowAdd.eq.Prod_Factorial.vandermonde)




if __name__ == '__main__':
    run()
# created on 2022-01-15
# updated on 2023-03-21
