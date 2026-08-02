from util import *


@apply
def apply(self, wrt=None):
    n, k = self.of(FallingFactorial)
    if wrt is None:
        wrt = self.generate_var(var='i', integer=True)
    return Equal(self, Product[wrt:k](n - wrt))


@prove(provable=False)
def prove(Eq):
    x = Symbol(complex=True)
    k = Symbol(integer=True, negative=False)
    Eq << apply(FallingFactorial(x, k))


if __name__ == '__main__':
    run()
# created on 2020-02-22
