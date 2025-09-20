from util import *


@apply
def apply(self, swap=False):
    args = self.of(MatMul)
    size = len(args)
    assert not size & 1
    size //= 2
    x, y = args[:size], args[size:]
    if swap:
        x, y = y, x
    x = MatMul(*x)
    y = MatMul(*y)
    if y == ~x:
        ...
    elif len(x.shape) == 1:
        assert y.T == ~x

    return Equal(self, Norm(x) ** 2)


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor

    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    Eq << apply(x @ ~x)

    Eq << Eq[-1].this.lhs.apply(Tensor.Dot.eq.ReducedSum.Square.Abs)

    Eq << Eq[-1].this.find(Norm).apply(Algebra.Norm.eq.Sqrt)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.ReducedSum)




if __name__ == '__main__':
    run()
# created on 2023-06-24
