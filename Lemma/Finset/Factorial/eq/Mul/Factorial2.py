from util import *


@apply
def apply(self, i=None):
    n = self.of(Factorial)
    assert n.is_integer
    assert n >= 0
    return Equal(self, Factorial2(n) * Factorial2(n - 1))


@prove(proved=False)
def prove(Eq):
    n = Symbol(integer=True, nonnegative=True)
    Eq << apply(Factorial(n))

    # https://en.wikipedia.org/wiki/Double_factorial
    


if __name__ == '__main__':
    run()
# created on 2023-06-03
