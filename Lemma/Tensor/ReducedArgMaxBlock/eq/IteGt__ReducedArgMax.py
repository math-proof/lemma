from util import *


@apply
def apply(self):
    x, y = self.of(ReducedArgMax[BlockMatrix])
    m, = x.shape
    n, = y.shape
    assert x.is_nonnegative
    assert y.is_nonnegative
    
    return Equal(self, Piecewise(
        (ReducedArgMax(BlockMatrix(Zeros(m), y)), ReducedMax(y) > ReducedMax(x)), 
        (ReducedArgMax(BlockMatrix(x, BlockMatrix(Zeros(n)))), True)))


@prove(proved=False)
def prove(Eq):
    n, m = Symbol(integer=True, positive=True)
    y = Symbol(shape=(n,), real=True, nonnegative=True)
    x = Symbol(shape=(m,), real=True, nonnegative=True)
    Eq << apply(ReducedArgMax(BlockMatrix(x, y)))


if __name__ == '__main__':
    run()
# created on 2022-01-03
