from util import *


@apply
def apply(given):
    (p_polynomial, *x), (S[p_polynomial], *y) = given.of(Equal[MatMul[2]])
    x = MatMul(*x)
    y = MatMul(*y)
    from Lemma.Tensor.Eq.of.EqDotSStack_Pow.independence.vector import extract
    return Equal(*extract(p_polynomial, x, y))

@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Tensor

    p = Symbol(complex=True, zero=False)
    m, n, k = Symbol(positive=True, integer=True)
    x, y = Symbol(shape=(n, m), given=True, complex=True)
    Eq << apply(Equal(p ** Stack[k:n](k) @ x, p ** Stack[k:n](k) @ y))

    Eq << Eq[0].this.find(Pow[Stack]).apply(Tensor.Expr.eq.Stack, k)

    Eq << Eq[-1].this.find(Pow[Stack]).apply(Tensor.Expr.eq.Stack, k)

    Eq << Tensor.Eq.of.EqDotSStack_Pow.independence.matrix.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-04-08
# updated on 2023-04-09
