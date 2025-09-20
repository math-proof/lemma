from util import *


@apply
def apply(self, *, simplify=True):
    A, B = self.of(MatMul)
    n, = A.shape
    S[n], = B.shape
    res = ReducedSum(A * B)
    if simplify:
        res = res.simplify()
    return Equal(self, res, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Discrete, Tensor

    n = Symbol(integer=True, positive=True)
    A, B = Symbol(shape=(n,), complex=True)
    Eq << apply(A @ B)

    Eq << Eq[0].this.rhs.apply(Tensor.ReducedSum.eq.Dot)


if __name__ == '__main__':
    run()
# created on 2022-03-16
# updated on 2022-04-02

from . import Square
