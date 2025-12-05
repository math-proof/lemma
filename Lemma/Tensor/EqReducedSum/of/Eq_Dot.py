from util import *


@apply
def apply(given):
    (x, w), y = given.of(Equal[MatMul])
    n, = x.shape
    i, j = w.of(SwapMatrix)
    assert 0 <= i < n
    assert 0 <= j < n
    return Equal(ReducedSum(x), ReducedSum(y))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor, Int, Vector

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), real=True)
    i, j = Symbol(domain=Range(n))
    Eq << apply(Equal(x @ SwapMatrix(n, i, j), y))

    t = Symbol(integer=True)
    Eq << Eq[0][t].reversed

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Sum)

    Eq << Eq[1].this.rhs.apply(Vector.Sum.eq.Sum_Get, t)

    Eq << Eq[-1].this.lhs.apply(Vector.Sum.eq.Sum_Get, t)

    Eq << Eq[-1].subs(Eq[-3])

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.find(Piecewise).apply(Int.Ite.eq.AddMulS)


if __name__ == '__main__':
    run()
# created on 2019-11-10
# updated on 2023-05-23
