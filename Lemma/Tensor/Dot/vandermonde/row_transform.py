from util import *


@apply
def apply(self):
    (expr, (j, S[0], m), (i, S[0], m_d)), (((x, S[i]), (delta, S[j])), (S[j], S[0], n), (S[i], S[0], S[m])) = self.of(Stack[(-Expr) ** Add * Binomial] @ Stack[Pow * Pow])
    (λ, (d, _i, _j)), (S[d], S[j - i]) = expr
    if _i != i:
        _i, _j = _j, _i
    assert _i == i and _j == -j
    assert m_d == m - d

    delta -= i
    assert not delta._has(i)
    h = self.generate_var(integer=True, var='h')
    return Equal(self, Stack[j:n, i:m - d]((i + delta) ** j * x ** i) @ Stack[j:n, i:n](binomial(j, i) * Sum[h:d + 1](binomial(d, h) * (-λ) ** (d - h) * x ** h * h ** (j - i))))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor, Finset

    n, m = Symbol(integer=True, positive=True)
    d = Symbol(integer=True, nonnegative=True)
    i, j = Symbol(integer=True)
    λ, delta, x = Symbol(real=True)
    Eq << apply(Stack[j:m, i:m - d](binomial(d, j - i) * (-λ) ** (d + i - j)) @ Stack[j:n, i:m]((i + delta) ** j * x ** i))

    Eq << Eq[-1].this.lhs.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    i = Symbol(domain=Range(m - d))
    j = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], [i, j])

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Sum.Sum.limits.swap)

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Sum.limits.subst.offset, -i)

    Eq << Eq[-1].this.rhs.apply(Finset.Mul_Sum.eq.Sum_Mul)

    Eq << Eq[-1].this.find(Mul[~Sum]).apply(Discrete.Sum.Binom.eq.Pow.Newton)




if __name__ == '__main__':
    run()
# created on 2022-01-15
