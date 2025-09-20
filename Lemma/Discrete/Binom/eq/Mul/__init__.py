from util import *


@apply
def apply(self):
    n, k = self.of(Binomial)
    return Equal(self, factorial(n) / (factorial(k) * factorial(n - k)))


@prove(proved=False)
def prove(Eq):
    n, k = Symbol(integer=True, positive=True)
    Eq << apply(binomial(n, k))


if __name__ == '__main__':
    run()


# created on 2020-02-23
del FallingFactorial
from . import FallingFactorial
from . import half
