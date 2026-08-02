from util import *


@apply
def apply(self):
    (A, B), (C, D) = self.of(Det[BlockMatrix[BlockMatrix[1], BlockMatrix[1]]])
    assert not A or not D
    factor = (-1) ** (B.shape[0] * C.shape[0])

    assert B.is_Identity
    assert C.is_Identity
    return Equal(self, factor)


@prove(proved=False)
def prove(Eq):
    n, m = Symbol(integer=True, positive=True)
    Eq << apply(Det(BlockMatrix([[Zeros(n, m), Identity(n)], [Identity(m), Zeros(m, n)]])))


if __name__ == '__main__':
    run()
# created on 2021-08-23
# updated on 2021-12-16
