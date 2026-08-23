from util import *


@apply
def apply(self):
    function, *limits, limit = self.of(Maxima)

    if limits:
        rhs = ReducedMax(Stack(Maxima(function, *limits), limit).simplify())
    else:
        rhs = ReducedMax(Stack(function, limit).simplify())

    return Equal(self, rhs, evaluate=False)


@prove(proved=False)
def prove(Eq):
    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    a = Symbol(shape=(oo, n), real=True)
    Eq << apply(Maxima[i, j](a[i, j]))


if __name__ == '__main__':
    run()
# created on 2021-08-12
