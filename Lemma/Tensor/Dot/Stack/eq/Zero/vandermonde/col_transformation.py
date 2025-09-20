from util import *


@apply
def apply(self):
    (((_x, _j), (delta, _i)), (j, S[0], m), (i, S[0], d)), (((x, (S[d], S[j], S[-i])), (S[d], S[i - j])), (S[j], S[0], S[m - d]), (S[i], S[0], S[m])) = \
    self.of(Stack[Pow * Pow] @ Stack[(-Symbol) ** Add * Binomial])
    if _x != x:
        _x, _j, delta, _i = delta, _i, _x, _j

    assert _x == x
    assert _j == j
    assert _i == i

    delta -= j
    assert not delta._has(j)
    return Equal(self, Zeros(d, m - d))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor

    m = Symbol(integer=True, positive=True)
    d = Symbol(integer=True, nonnegative=True)
    i, j = Symbol(integer=True)
    delta, x = Symbol(real=True)
    Eq << apply(Stack[j:m, i:d]((j + delta) ** i * x ** j) @ Stack[j:m - d, i:m](binomial(d, i - j) * (-x) ** (d + j - i)))

    Eq << Eq[-1].this.lhs.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.find(Pow[-Symbol]).apply(Algebra.Pow.eq.Mul.Neg)

    # j < m - d
    # k <= d + j < d + (m - d) = m
    # k < m
    Eq << Eq[-1].this.lhs().expr.simplify()

    Eq << Eq[-1].this.find(Sum).apply(Discrete.Sum.Binom.eq.Mul.Diff)

    Eq << Eq[-1].this.find(Stack[Mul])().find(Difference).apply(Discrete.Diff.eq.Zero)





if __name__ == '__main__':
    run()
# created on 2021-11-30
# updated on 2021-12-01
