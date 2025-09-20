from util import *


@apply
def apply(self):
    ((delta, i), (j, S[0], m), (S[i], S[0], n)), (((λ, (d, S[j], S[-i])), (S[d], S[i - j])), (S[j], S[0], S[m - d]), (S[i], S[0], S[m])) = self.of(Stack[Pow] @ Stack[(-Expr) ** Add * Binomial])
    delta -= j
    assert not delta._has(j)
    h = self.generate_var(integer=True, var='h')
    return Equal(self, Stack[j:n, i:n](binomial(i, j) * Sum[h:d + 1](binomial(d, h) * (-λ) ** (d - h) * h ** (i - j))) @ Stack[j:m - d, i:n]((j + delta) ** i))


@prove
def prove(Eq):
    from Lemma import Discrete, Tensor

    n, m = Symbol(integer=True, positive=True)
    d = Symbol(integer=True, nonnegative=True)
    i, j = Symbol(integer=True)
    λ, delta = Symbol(real=True)
    Eq << apply(Stack[j:m, i:n]((j + delta) ** i) @ Stack[j:m - d, i:m](binomial(d, i - j) * (-λ) ** (d + j - i)))

    x = Symbol(real=True)
    Eq << Tensor.Dot.vandermonde.col_transform.apply(Stack[j:m, i:n]((j + delta) ** i * x ** j) @ Stack[j:m - d, i:m](binomial(d, i - j) * (-λ) ** (d + j - i)))

    Eq << Eq[-1].subs(x, 1)


if __name__ == '__main__':
    run()
# created on 2022-01-15
