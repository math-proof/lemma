from util import *


@apply
def apply(self):
    n, *args = self.of(Multinomial)
    from functools import reduce
    return Equal(self, Factorial(n) / reduce(lambda x, y: x * y, (Factorial(arg) for arg in args)))


@prove(provable=False)
def prove(Eq):
    n, i, j, k = Symbol(integer=True, nonnegative=True)
    Eq << apply(Multinomial(n, i, j, k))

    


if __name__ == '__main__':
    run()
# created on 2023-08-20
