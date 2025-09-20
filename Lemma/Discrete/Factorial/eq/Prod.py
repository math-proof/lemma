from util import *


@apply
def apply(self):
    n = self.of(Factorial)

    assert n.is_nonnegative and n.is_integer
    i = self.generate_var(var='i', integer=True)

    return Equal(self, Product[i:1:n + 1](i))


@prove(provable=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    Eq << apply(factorial(n))


if __name__ == '__main__':
    run()
# created on 2020-02-23
