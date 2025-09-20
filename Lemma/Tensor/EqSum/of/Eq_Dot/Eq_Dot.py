from util import *


@apply
def apply(eq_xy, eq_ab, i=None):
    (x, w), y = eq_xy.of(Equal[MatMul])
    (a, S[w]), b = eq_ab.of(Equal[MatMul])

    n, = x.shape
    [S[n]] = a.shape
    _i, _j = w.of(SwapMatrix)
    assert 0 <= _i < n
    assert 0 <= _j < n
    if i is None:
        i = eq_xy.generate_var(eq_ab.free_symbols, integer=True, var='i')

    return Equal(Sum[i:n](x[i] * a[i]), Sum[i:n](y[i] * b[i]))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor

    n = Symbol(integer=True, positive=True)
    x, y, a, b = Symbol(shape=(n,), real=True)
    i, j = Symbol(domain=Range(n))
    Eq << apply(Equal(x @ SwapMatrix(n, i, j), y), Equal(a @ SwapMatrix(n, i, j), b))

    _i = Eq[-1].lhs.variable
    Eq << Eq[0][_i].reversed

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Sum)

    Eq << Eq[1][_i].reversed

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Sum)

    Eq << Eq[-1] * Eq[-3]

    Eq << Eq[2].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.domain_defined)





if __name__ == '__main__':
    run()
# created on 2019-11-13
# updated on 2023-09-16
