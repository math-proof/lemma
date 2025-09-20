from util import *


@apply
def apply(self):
    function, *limits = self.of(Maxima[Exp])
    rhs = exp(Maxima(function, *limits).simplify()).simplify()

    return Equal(self, rhs, evaluate=False)


@prove(proved=False)
def prove(Eq):
    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    a = Symbol(shape=(oo, n), real=True)
    Eq << apply(Maxima[i, j](exp(a[i, j])))


if __name__ == '__main__':
    run()
# created on 2020-12-19
