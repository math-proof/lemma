from util import *


@apply
def apply(self):
    x = self.of(ReducedArgMax[Exp])
    return Equal(self, ReducedArgMax(x))


@prove(proved=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    Eq << apply(ReducedArgMax(Exp(x)))


if __name__ == '__main__':
    run()
# created on 2021-12-20
