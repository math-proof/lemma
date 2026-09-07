from util import *


@apply
def apply(self):
    x, i = self.of(FallingFactorial)
    return Equal(self, 1 / FallingFactorial(x - i, -i))


@prove(provable=False)
def prove(Eq):
    x = Symbol(real=True)
    n = Symbol(integer=True, nonnegative=True)
    i = Symbol(integer=True)
    Eq << apply(FallingFactorial(x, -i))


if __name__ == '__main__':
    run()
# created on 2023-08-20
