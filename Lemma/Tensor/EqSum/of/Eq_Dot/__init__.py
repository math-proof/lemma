from util import *


@apply
def apply(given, t=None):
    (x, w), y = given.of(Equal[MatMul])
    n, = x.shape
    i, j = w.of(SwapMatrix)
    assert 0 <= i < n
    assert 0 <= j < n
    if t is None:
        t = given.generate_var(integer=True, var='t')

    return Equal(Sum[t:n](x[t]), Sum[t:n](y[t]))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor, Vector

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), real=True, given=True)
    i, j = Symbol(domain=Range(n))
    t = Symbol(integer=True)
    Eq << apply(Equal(x @ SwapMatrix(n, i, j), y), t)

    Eq << Tensor.EqReducedSum.of.Eq_Dot.apply(Eq[0])

    Eq << Eq[-1].this.rhs.apply(Vector.Sum.eq.Sum_Get, t)

    Eq << Eq[-1].this.lhs.apply(Vector.Sum.eq.Sum_Get, t)


if __name__ == '__main__':
    run()
# created on 2019-11-11
from . import Eq_Dot
