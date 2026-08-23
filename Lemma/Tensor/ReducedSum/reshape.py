from util import *


@apply
def apply(self, *shape):
    expr = self.of(ReducedSum)
    from functools import reduce
    S[reduce(lambda x, y: x * y, shape)], = expr.shape
    return Equal(self, ReducedSum[tuple(range(len(shape)))](expr.reshape(*shape)))

@prove(provable=False)
def prove(Eq):
    m, n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(m * n,))
    Eq << apply(ReducedSum(x), m, n)

    


if __name__ == '__main__':
    run()
# created on 2023-12-17
