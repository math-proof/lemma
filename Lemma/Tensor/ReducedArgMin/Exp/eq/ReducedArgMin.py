from util import *


@apply
def apply(self):
    x = self.of(ReducedArgMin[Exp])
    return Equal(self, ReducedArgMin(x))


@prove(proved=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    Eq << apply(ReducedArgMin(Exp(x)))


if __name__ == '__main__':
    run()
# created on 2021-12-20
