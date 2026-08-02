from util import *


@apply
def apply(self, i=None):
    n = self.of(Factorial2)
    assert n.is_integer
    assert n >= 0
    if i is None:
        i = self.generate_var(integer=True)
    return Equal(self, Product[i: Ceil(n / 2)](n - 2 * i))


@prove(provable=False)
def prove(Eq):
    n = Symbol(integer=True, nonnegative=True)
    Eq << apply(Factorial2(n))

    # https://en.wikipedia.org/wiki/Double_factorial



if __name__ == '__main__':
    run()
# created on 2023-06-03
from . import odd
