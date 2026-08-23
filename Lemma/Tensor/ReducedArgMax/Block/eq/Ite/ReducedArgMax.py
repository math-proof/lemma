from util import *


@apply
def apply(self):
    x, y = self.of(ReducedArgMax[BlockMatrix])
    m, = x.shape
    n, = y.shape

    return Equal(self, Piecewise((m + ReducedArgMax(y), ReducedMax(y) > ReducedMax(x)), (ReducedArgMax(x), True)))


@prove(proved=False)
def prove(Eq):
    n, m = Symbol(integer=True, positive=True)
    y = Symbol(shape=(n,), real=True)
    x = Symbol(shape=(m,), real=True)
    Eq << apply(ReducedArgMax(BlockMatrix(x, y)))




if __name__ == '__main__':
    run()
# created on 2022-01-03

